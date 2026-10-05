import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSpineSeeds

/-! A constructor terminal observes its captures as literal source variables.
Their finite wrapper grammar can be substituted with typed projection queries
without erasing the projection node or inventing a source domain typing. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor
open private raiseView from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
set_option backward.isDefEq.respectTransparency false

structure ProjectionGradedResult
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  footprint : Footprint
  query : ProjectionObs env registry target node locals σ raw footprint
  adapter : NormalProfileAdapter env U registry target raw (raiseProfile rank bound requested)
  resources : footprint.Available available

namespace ProjectionGradedResult
variable {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} {available : Valuation}

noncomputable def raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : ProjectionGradedResult env registry target node locals σ available requested)
    (N : Nat) (bound : result.rank ≤ N) :
    ProjectionGradedResult env registry target node locals σ available requested := {
  rank := N, bound := Nat.le_trans result.bound bound
  raw := raiseProfile N bound result.raw, footprint := result.footprint
  query := .raise result.query bound
  adapter := by simpa only [raiseProfile_trans] using result.adapter.raise henv hscoped formed bound
  resources := result.resources }

def unpad
    (result : ProjectionGradedResult env registry target node locals σ available requested.pad) :
    ProjectionGradedResult env registry target node locals σ available requested := {
  rank := result.rank, bound := Nat.le_trans (Nat.le_succ _) result.bound
  raw := result.raw, footprint := result.footprint, query := result.query
  adapter := by simpa only [raiseProfile_pad] using result.adapter
  resources := result.resources }

noncomputable def pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Profile n}
    (result : ProjectionGradedResult env registry target node locals σ available requested) :
    ProjectionGradedResult env registry target node locals σ available requested.pad := by
  let N := max result.rank (n + 1)
  let lifted := result.raiseTo henv hscoped formed N (Nat.le_max_left ..)
  refine ⟨N, Nat.le_max_right .., lifted.raw, lifted.footprint, lifted.query,
    ?_, lifted.resources⟩
  rw [raiseProfile_pad]
  exact lifted.adapter

noncomputable def view
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : ProjectionGradedResult env registry target node locals σ available (.singleton first))
    (change : AtomView env U registry target first second) :
    ProjectionGradedResult env registry target node locals σ available (.singleton second) := by
  refine ⟨result.rank, result.bound, result.raw, result.footprint, result.query, ?_, result.resources⟩
  have previous := result.adapter
  rw [raiseProfile_singleton] at previous ⊢
  exact previous.comp (.cons (List.mem_singleton_self _)
    ((raiseView result.bound change).toAdapter henv hscoped formed) (.nil _))

noncomputable def union
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (first : ProjectionGradedResult env registry target node locals σ available p)
    (second : ProjectionGradedResult env registry target node locals σ available q) :
    ProjectionGradedResult env registry target node locals σ available (p.union q) := by
  let N := max first.rank second.rank
  let left := first.raiseTo henv hscoped formed N (Nat.le_max_left ..)
  let right := second.raiseTo henv hscoped formed N (Nat.le_max_right ..)
  refine ⟨N, left.bound, left.raw.union right.raw, left.footprint ++ right.footprint,
    .union left.query right.query,
    ?_,
    fun i need member => (List.mem_append.mp member).elim (left.resources i need) (right.resources i need)⟩
  rw [raiseProfile_union]
  have leftAdapter : NormalProfileAdapter env U registry target (left.raw : Profile N)
      (raiseProfile N left.bound p) := left.adapter
  have rightAdapter : NormalProfileAdapter env U registry target (right.raw : Profile N)
      (raiseProfile N right.bound q) := right.adapter
  exact leftAdapter.union rightAdapter

noncomputable def exact
    {footprint : Footprint}
    (query : ProjectionObs env registry target node locals σ demand footprint)
    (resources : footprint.Available available) :
    ProjectionGradedResult env registry target node locals σ available demand := {
  rank := _, bound := Nat.le_refl _, raw := demand, footprint := footprint, query := query
  adapter := by rw [raiseProfile_self]; exact .refl _
  resources := resources }

/-- Restrict the already observed input by actual binder coverage. -/
noncomputable def localDemand
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {input : Profile n}
    (result : ProjectionGradedResult env registry target node locals σ available input)
    (need : Need) (bound : need.rank ≤ n)
    (covered : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ProjectionGradedResult env registry target node locals σ available need.profile := by
  have select : NormalProfileAdapter env U registry target input (raiseProfile n bound need.profile) := by
    apply ProfileAdapter.select
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨old, covered old (by simpa only [Need.atGrade, dif_pos bound, Profile.atoms] using present), rfl⟩
  exact ⟨result.rank, Nat.le_trans bound result.bound, result.raw, result.footprint, result.query,
    by simpa only [raiseProfile_trans] using
      result.adapter.comp (select.raise henv hscoped formed result.bound), result.resources⟩

end ProjectionGradedResult

/-- Every occurrence is an explicit finite query at the same original
projected argument node. The constructor terminal's variable index is fixed. -/
inductive ProjectionVariableSupply (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr) (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) (slot : Nat) : Footprint → Type where
  | nil : ProjectionVariableSupply env registry target node locals σ available slot []
  | cons (value : ProjectionGradedResult env registry target node locals σ available need.profile)
      (tail : ProjectionVariableSupply env registry target node locals σ available slot rest) :
      ProjectionVariableSupply env registry target node locals σ available slot ((slot, need) :: rest)

theorem ProjectionVariableSupply.split
    (supply : ProjectionVariableSupply env registry target node locals σ available slot (left ++ right)) :
    Nonempty (ProjectionVariableSupply env registry target node locals σ available slot left) ∧
    Nonempty (ProjectionVariableSupply env registry target node locals σ available slot right) := by
  induction left with
  | nil => exact ⟨⟨.nil⟩, ⟨supply⟩⟩
  | cons entry rest ih =>
    cases supply with
    | cons value tail =>
      obtain ⟨⟨left⟩, ⟨right⟩⟩ := ih tail
      exact ⟨⟨.cons value left⟩, ⟨right⟩⟩

theorem ProjectionVariableSupply.member
    (supply : ProjectionVariableSupply env registry target node locals σ available slot footprint)
    (present : (slot, need) ∈ footprint) :
    Nonempty (ProjectionGradedResult env registry target node locals σ available need.profile) := by
  induction supply with
  | nil => cases present
  | cons value tail ih =>
    rcases List.mem_cons.mp present with equal | present
    · cases Prod.mk.inj equal |>.2
      exact ⟨value⟩
    · exact ih present

theorem ProjectionVariableSupply.restrict
    (supply : ProjectionVariableSupply env registry target node locals σ available slot before)
    (included : ∀ entry ∈ after, entry ∈ before)
    (same : ∀ entry ∈ after, entry.1 = slot) :
    Nonempty (ProjectionVariableSupply env registry target node locals σ available slot after) := by
  induction after with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    have equal := same (index, need) List.mem_cons_self
    change index = slot at equal
    subst index
    obtain ⟨value⟩ := supply.member (included _ List.mem_cons_self)
    obtain ⟨tail⟩ := ih
      (fun entry member => included entry (List.mem_cons_of_mem _ member))
      (fun entry member => same entry (List.mem_cons_of_mem _ member))
    exact ⟨.cons value tail⟩

/-- Actual prefix-row needs and coverage produce the complete finite supply. -/
theorem ProjectionGradedResult.supply
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {input : Profile n}
    (result : ProjectionGradedResult env registry target node locals σ available input)
    (needs : List Need) (slot : Nat)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    Nonempty (ProjectionVariableSupply env registry target node locals σ available slot
      (needs.map (slot, ·))) := by
  induction needs with
  | nil => exact ⟨.nil⟩
  | cons need tail ih =>
    obtain ⟨rest⟩ := ih (fun need member => bounded need (List.mem_cons_of_mem _ member))
      (fun need member => covered need (List.mem_cons_of_mem _ member))
    exact ⟨.cons (result.localDemand henv hscoped formed need (bounded _ List.mem_cons_self)
      (covered _ List.mem_cons_self)) rest⟩

/-- Literal terminal variable observers preserve their complete query and
adapter through substitution by an original projected argument. -/
theorem reifyProjectedVariable
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (observation : Obs env U registry target captureLocals captures (.bvar slot) demand footprint)
    (supply : ProjectionVariableSupply env registry target node locals σ available slot footprint) :
    Nonempty (ProjectionGradedResult env registry target node locals σ available demand) := by
  match observation with
  | .var .. =>
    cases supply with
    | cons value tail => exact ⟨value⟩
  | .empty =>
    exact ⟨ProjectionGradedResult.exact .empty (fun _ _ member => nomatch member)⟩
  | .union first second =>
    obtain ⟨⟨left⟩, ⟨right⟩⟩ := supply.split
    obtain ⟨firstResult⟩ := reifyProjectedVariable henv hscoped formed first left
    obtain ⟨secondResult⟩ := reifyProjectedVariable henv hscoped formed second right
    exact ⟨firstResult.union henv hscoped formed secondResult⟩
  | .view child change =>
    obtain ⟨result⟩ := reifyProjectedVariable henv hscoped formed child supply
    exact ⟨result.view henv hscoped formed change⟩
  | .pad child =>
    obtain ⟨result⟩ := reifyProjectedVariable henv hscoped formed child supply
    exact ⟨result.pad henv hscoped formed⟩
  | .unpad child =>
    obtain ⟨result⟩ := reifyProjectedVariable henv hscoped formed child supply
    exact ⟨result.unpad⟩
  | .rowShift child =>
    obtain ⟨result⟩ := reifyProjectedVariable henv hscoped formed child supply
    exact ⟨(result.pad henv hscoped formed).view henv hscoped formed (.commutePadFn _ _)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
