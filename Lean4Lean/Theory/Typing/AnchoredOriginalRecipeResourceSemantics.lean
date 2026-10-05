import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaTrace
import Lean4Lean.Theory.Typing.AnchoredAtomActionInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! Variable resource transfer is evaluated on the current paired frame. Its
plain variable observations contain no canonical openings. Empty demands use
empty support; a nonempty actual relation supplies its own type capability. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure RecipeResourceValue (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (left right assigned : VExpr) (input : Profile n) where
  support : Profile n
  typed : input.HasType support
  related : Related env U registry target left right assigned input support
  code : TypeRelated env U registry target assigned assigned support

namespace RecipeResourceValue

def empty : RecipeResourceValue env U registry target left right assigned (.empty : Profile n) where
  support := .empty
  typed := Profile.HasType.empty Profile.WF.empty
  related := Related.of_singletons (fun _ h => nomatch h)
  code := TypeRelated.of_singletons (fun _ h => nomatch h)

theorem ofRelated
    {input support : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (typed : input.HasType support)
    (related : Related env U registry target left right assigned input support) :
    Nonempty (RecipeResourceValue env U registry target left right assigned input) := by
  by_cases nonempty : input.Nonempty
  · exact ⟨⟨support, typed, related, related.typeCode henv hscoped formed nonempty⟩⟩
  · have equal : input = .empty := by
      exact Classical.not_not.mp nonempty
    cases equal
    exact ⟨empty⟩

noncomputable def union (henv : env.Ordered)
    (first : RecipeResourceValue env U registry target left right assigned p)
    (second : RecipeResourceValue env U registry target left right assigned q) :
    RecipeResourceValue env U registry target left right assigned (p.union q) := by
  have wf := first.typed.wf_type.union second.typed.wf_type
  have ft := first.typed.enlarge (Profile.le_union_left _ _) wf
  have st := second.typed.enlarge (Profile.le_union_right _ _) wf
  have code : TypeRelated env U registry target assigned assigned (first.support.union second.support) :=
    TypeRelated.of_singletons (fun _ member => (List.mem_append.mp member).elim
      (fun h => first.code.singleton h) (fun h => second.code.singleton h))
  exact ⟨_, ft.union st,
    (Related.retag henv ft code first.related).union (Related.retag henv st code second.related), code⟩

noncomputable def action
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (value : RecipeResourceValue env U registry target left right assigned (.singleton a))
    (action : AtomAction env U registry target a b) :
    RecipeResourceValue env U registry target left right assigned (.singleton b) :=
  ⟨action.support.apply value.support, action.typed value.typed,
    action.termMap henv hscoped formed value.typed value.related,
    action.support.codeMap henv hscoped value.code⟩

def pad (henv : env.Ordered)
    (value : RecipeResourceValue env U registry target left right assigned profile) :
    RecipeResourceValue env U registry target left right assigned profile.pad :=
  ⟨value.support.pad, value.typed.pad, value.related.pad henv, value.code.pad henv⟩

def unpad (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (value : RecipeResourceValue env U registry target left right assigned profile.pad) :
    RecipeResourceValue env U registry target left right assigned profile :=
  ⟨value.support.down, value.typed.pad_inv, value.related.unpad henv formed, value.code.down henv⟩

end RecipeResourceValue

/-- These values are obtained from actual lookup relations, not from a
supplied fundamental answer at synthetic variable originals. -/
def RecipeResourceRealization (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target source : List VExpr) (σ τ : Subst) (footprint : Footprint) : Prop :=
  ∀ index need, (index, need) ∈ footprint → ∀ assigned,
    Lookup source index assigned →
      Nonempty (RecipeResourceValue env U registry target (σ index) (τ index)
        (assigned.subst σ) need.profile)

theorem OriginalRichFrame.recipeResources
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (resources : footprint.Available available) :
    RecipeResourceRealization env U registry target source σ τ footprint := by
  intro index need member assigned lookup
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed (resources index need member) lookup
  exact RecipeResourceValue.ofRelated henv hscoped formed entry.typed entry.related

private theorem variableTraceValue
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (trace : VariableTrace env U registry target index profile footprint)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint)
    (lookup : Lookup source index assigned) :
    ∃ query : Obs env U registry target locals τ (.bvar index) profile footprint,
      Nonempty (RecipeResourceValue env U registry target (σ index) (τ index)
        (assigned.subst σ) profile) := by
  induction trace with
  | leaf demand => exact ⟨.var locals τ index demand, resources _ _ List.mem_cons_self _ lookup⟩
  | empty => exact ⟨.empty, ⟨.empty⟩⟩
  | union first second ihl ihr =>
    obtain ⟨left, ⟨lv⟩⟩ := ihl (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨right, ⟨rv⟩⟩ := ihr (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨.union left right, ⟨lv.union henv rv⟩⟩
  | view source change ih =>
    obtain ⟨query, ⟨value⟩⟩ := ih resources
    exact ⟨.view query change, ⟨value.action henv hscoped formed (.view change)⟩⟩
  | pad source ih =>
    obtain ⟨query, ⟨value⟩⟩ := ih resources
    exact ⟨.pad query, ⟨value.pad henv⟩⟩
  | unpad source ih =>
    obtain ⟨query, ⟨value⟩⟩ := ih resources
    exact ⟨.unpad query, ⟨value.unpad henv formed⟩⟩
  | rowShift source ih =>
    obtain ⟨query, ⟨value⟩⟩ := ih resources
    exact ⟨.rowShift query, ⟨(value.pad henv).action henv hscoped formed
      (.view (.commutePadFn _ _))⟩⟩

theorem recipeVariableValue
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : Obs env U registry target locals σ (.bvar index) profile footprint)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint)
    (lookup : Lookup source index assigned) :
    ∃ right : Obs env U registry target locals τ (.bvar index) profile footprint,
      Nonempty (RecipeResourceValue env U registry target (σ index) (τ index)
        (assigned.subst σ) profile) :=
  variableTraceValue henv hscoped formed query.variableTrace resources lookup

/-- Evaluate every transferred resource with the current paired realization.
No new original proof or fundamental/reindex call is introduced here. -/
theorem RecipeResourceTransfer.realize
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint) :
    RecipeResourceRealization env U registry target source σ τ required := by
  induction transfer with
  | nil => intro _ _ member; cases member
  | cons query tail ih =>
    intro index need member assigned lookup
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      obtain ⟨_, value⟩ := recipeVariableValue henv hscoped formed query
        (fun i need member => resources i need (List.mem_append_left _ member)) lookup
      exact value
    · exact ih (fun i need member => resources i need (List.mem_append_right _ member))
        index need member assigned lookup

/-- A literal variable query changes its realization structurally. All its
finite actions and exact source footprint are kept. -/
noncomputable def variableRequery
    (query : Obs env U registry target locals σ (.bvar index) profile footprint)
    (τ : Subst) : Obs env U registry target locals τ (.bvar index) profile footprint :=
  match query with
  | .var _ _ _ demand => .var locals τ index demand
  | .empty => .empty
  | .union left right => .union (variableRequery left τ) (variableRequery right τ)
  | .view source change => .view (variableRequery source τ) change
  | .pad source => .pad (variableRequery source τ)
  | .unpad source => .unpad (variableRequery source τ)
  | .rowShift source => .rowShift (variableRequery source τ)
termination_by sizeOf query

theorem variableRequery_headDepth
    (query : Obs env U registry target locals σ (.bvar index) profile footprint)
    (τ : Subst) (policy : Name → Nat → Nat) :
    (variableRequery query τ).headDepth policy = query.headDepth policy := by
  match query with
  | .var .. | .empty => simp only [variableRequery, Obs.headDepth]
  | .union left right =>
    simp only [variableRequery, Obs.headDepth,
      variableRequery_headDepth left, variableRequery_headDepth right]
  | .view source change | .pad source | .unpad source | .rowShift source =>
    simpa only [variableRequery, Obs.headDepth] using variableRequery_headDepth source τ policy
termination_by sizeOf query

noncomputable def RecipeResourceTransfer.requery
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (τ : Subst) : RecipeResourceTransfer env U registry target locals τ required footprint :=
  match transfer with
  | .nil => .nil
  | .cons query tail => .cons (variableRequery query τ) (tail.requery τ)

theorem RecipeResourceTransfer.requery_headDepth
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (τ : Subst) (policy : Name → Nat → Nat) :
    (transfer.requery τ).headDepth policy = transfer.headDepth policy := by
  induction transfer with
  | nil => rfl
  | cons query tail ih =>
    simp only [RecipeResourceTransfer.requery, RecipeResourceTransfer.headDepth,
      variableRequery_headDepth, ih]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
