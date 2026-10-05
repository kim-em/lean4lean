import Lean4Lean.Theory.Typing.AnchoredSortableDepthGraded
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthRenaming
import Lean4Lean.Theory.Typing.AnchoredSortableGradedAction

/-! Finite replacement supplies whose actual payloads satisfy every caller
control simultaneously. The bound is an arbitrary vector, not one selected
current declaration block. -/
namespace Lean4Lean.AnchoredSource.Adapted.AllDepth
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

abbrev Budget := (Name → Bool) → Nat

structure GradedResult (budget : Budget) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (expression : VExpr) (requested : Profile n)
    extends SortableGradedResult env U registry Γ locals σ available expression requested where
  bounded : ∀ current, observation.nativeDepth current ≤ budget current

noncomputable def GradedResult.exact
    (observation : SortableObs env U registry Γ locals σ expression demand footprint)
    (resources : footprint.Available available) (live : Profile.Live env U registry Γ demand)
    (bounded : ∀ current, observation.nativeDepth current ≤ budget current) :
    GradedResult budget env U registry Γ locals σ available expression demand :=
  { SortableGradedResult.exact observation resources live with bounded := bounded }

noncomputable def GradedResult.unpad
    (result : GradedResult budget env U registry Γ locals σ available expression requested.pad) :
    GradedResult budget env U registry Γ locals σ available expression requested :=
  { result.toSortableGradedResult.unpad with bounded := result.bounded }

noncomputable def GradedResult.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : GradedResult budget env U registry Γ locals σ available expression requested) :
    GradedResult budget env U registry Γ locals σ available expression requested.pad :=
  { result.toSortableGradedResult.pad henv hscoped hΓ with
    bounded := by
      intro current
      simpa only [SortableGradedResult.pad, SortableGradedResult.raiseTo,
        SortableObs.nativeDepth_raise] using result.bounded current }

noncomputable def GradedResult.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : GradedResult budget env U registry Γ locals σ available expression (.singleton a))
    (view : AtomView env U registry Γ a b) :
    GradedResult budget env U registry Γ locals σ available expression (.singleton b) :=
  { result.toSortableGradedResult.view henv hscoped hΓ view with bounded := result.bounded }

noncomputable def GradedResult.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (left : GradedResult budget env U registry Γ locals σ available expression p)
    (right : GradedResult budget env U registry Γ locals σ available expression q) :
    GradedResult budget env U registry Γ locals σ available expression (p.union q) :=
  { left.toSortableGradedResult.union henv hscoped hΓ right.toSortableGradedResult with
    bounded := by
      intro current
      simpa only [SortableGradedResult.union, SortableGradedResult.raiseTo,
        SortableObs.nativeDepth, SortableObs.nativeDepth_raise] using
        Nat.max_le.mpr ⟨left.bounded current, right.bounded current⟩ }

noncomputable def GradedResult.sourceLift
    (result : GradedResult budget env U registry Γ locals σ available expression requested)
    (anchor : VExpr) (head : List Need) :
    GradedResult budget env U registry Γ (Locals.push locals) (σ.cons anchor)
      (Valuation.push head available) expression.lift requested :=
  { result.toSortableGradedResult.sourceLift anchor head with
    bounded := by
      intro current
      simpa only [SortableGradedResult.sourceLift, SortableObs.nativeDepth_rec, SortableObs.nativeDepth_expr_mp,
        lift_eq_lift', SortableObs.nativeDepth_renameSource] using result.bounded current }

theorem GradedResult.app
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed) {key : Key n} {output : Atom n}
    (function : GradedResult budget env U registry Γ locals σ available f (Profile.fn key output))
    (argument : GradedResult budget env U registry Γ locals σ available a rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)) :
    Nonempty (GradedResult budget env U registry Γ locals σ available (.app f a) (.singleton output)) := by
  obtain ⟨result, bound⟩ := function.toSortableGradedResult.app_allDepth henv hscoped hΓ closed
    argument.toSortableGradedResult arguments admitted
  exact ⟨{ result with
    bounded := fun current => Nat.le_trans (bound current)
      (Nat.max_le.mpr ⟨function.bounded current, argument.bounded current⟩) }⟩

theorem GradedResult.lam
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed) {key : Key n} {output : Atom n} {support : Profile n}
    (domain : SortableCert env U registry Γ locals σ annotation true support domainFootprint)
    (domainBound : ∀ current, domain.nativeDepth current ≤ budget current)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, List.Subset (need.atGrade n) key.input)
    (body : GradedResult budget env U registry Γ (Locals.push locals) (σ.cons key.anchor)
      (Valuation.push localNeeds available) expression (.singleton output))
    (bodyClosed : (Valuation.push localNeeds available).AtomClosed) :
    Nonempty (GradedResult budget env U registry Γ locals σ available
      (.lam annotation expression) (Profile.fn key output)) := by
  obtain ⟨result, bound⟩ := SortableGradedResult.lam_allDepth henv hscoped hΓ closed domain
    domainAvailable guard localNeeds bounded covered body.toSortableGradedResult bodyClosed
  exact ⟨{ result with
    bounded := fun current => Nat.le_trans (bound current)
      (Nat.max_le.mpr ⟨domainBound current, body.bounded current⟩) }⟩

theorem GradedResult.code
    (henv : env.Ordered) (closed : available.AtomClosed)
    (result : GradedResult budget env U registry Γ locals σ available expression requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : SortableCert env U registry Γ locals σ expression relevant requested footprint,
      footprint.Available available ∧ ∀ current, certificate.nativeDepth current ≤ budget current := by
  obtain ⟨footprint, certificate, resources, bound⟩ :=
    result.toSortableGradedResult.code_allDepth henv closed formed
  exact ⟨footprint, certificate, resources,
    fun current => Nat.le_trans (bound current) (result.bounded current)⟩

noncomputable def GradedResult.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (result : GradedResult budget env U registry Γ locals σ available expression (.singleton a)) :
    GradedResult budget env U registry Γ locals σ available expression (.singleton b) where
  rank := result.rank
  bound := result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := by
    have step := (action.raise result.bound).toGeneralAdapter henv hscoped hΓ
    have first := result.adapter
    rw [raiseProfile_singleton] at first ⊢
    exact GeneralProfileAdapter.comp first (.cons (List.mem_singleton_self _) step (.nil _))
  resources := result.resources
  live := result.live
  bounded := result.bounded

inductive GradedSupply (budget : Budget) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ replacement : Subst) (available : Valuation) : Footprint → Type where
  | nil : GradedSupply budget env U registry Γ locals σ replacement available []
  | cons {index : Nat} {need : Need}
      (value : GradedResult budget env U registry Γ locals σ available (replacement index) need.profile)
      (tail : GradedSupply budget env U registry Γ locals σ replacement available rest) :
      GradedSupply budget env U registry Γ locals σ replacement available ((index, need) :: rest)

theorem GradedSupply.split
    (supply : GradedSupply budget env U registry Γ locals σ replacement available (left ++ right)) :
    Nonempty (GradedSupply budget env U registry Γ locals σ replacement available left) ∧
    Nonempty (GradedSupply budget env U registry Γ locals σ replacement available right) := by
  induction left with
  | nil => exact ⟨⟨.nil⟩, ⟨supply⟩⟩
  | cons entry rest ih =>
    cases supply with
    | cons value tail =>
      obtain ⟨⟨left⟩, ⟨right⟩⟩ := ih tail
      exact ⟨⟨.cons value left⟩, ⟨right⟩⟩

theorem GradedSupply.underBinder
    {input : Profile n} {head : List Need}
    (normal : BinderPack n input required outside)
    (inside : Profile.Live env U registry Γ input)
    (headContains : ∀ need ∈ required.localNeeds, need ∈ head)
    (supply : GradedSupply budget env U registry Γ locals σ replacement available outside)
    (anchor : VExpr) :
    Nonempty (GradedSupply budget env U registry Γ (Locals.push locals) (σ.cons anchor)
      replacement.lift (Valuation.push head available) required) := by
  induction normal with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    obtain ⟨first, restLive⟩ := Profile.Live.union_iff.mp inside
    have lower : Profile.Live env U registry Γ need.profile := by
      simp only [Need.atGrade, dif_pos bound] at first
      exact (raiseProfile_live_iff bound need.profile).mp first
    obtain ⟨tail⟩ := ih restLive (fun original hm => headContains original (List.mem_cons_of_mem _ hm)) supply
    have resources : Footprint.Available [(0, need)] (Valuation.push head available) := by
      intro index original hm
      cases List.mem_singleton.mp hm
      exact headContains need List.mem_cons_self
    exact ⟨.cons (GradedResult.exact (.legacy (.var _ _ 0 need.profile)) resources lower
      (by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _)) tail⟩
  | external index need rest ih =>
    cases supply with
    | cons value tail =>
      obtain ⟨result⟩ := ih inside headContains tail
      exact ⟨.cons (value.sourceLift anchor head) result⟩

end Lean4Lean.AnchoredSource.Adapted.AllDepth
