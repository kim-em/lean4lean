import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental

/-! A precise coverage obstruction for the current type-unindexed source
grammar. Even after target constructor eta is repaired, a resource-free
nonempty observer cannot be returned at a source variable. This rules out
claiming unrestricted unit-like transfer from the target eta theorem alone.
It is not an impossibility result for a corrected observation grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Obs.variable_noResources
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {index : Nat}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available (fun _ => [])) : demand = .empty := by
  match n, demand, footprint, observation with
  | _, _, _, .var .. => exact False.elim (List.not_mem_nil (resources _ _ List.mem_cons_self))
  | _, _, _, .empty => rfl
  | _, _, _, .union left right =>
    have hl := left.variable_noResources (fun i need member => resources i need (List.mem_append_left _ member))
    have hr := right.variable_noResources (fun i need member => resources i need (List.mem_append_right _ member))
    rw [hl, hr]; rfl
  | _, _, _, .view source _ =>
    have empty := source.variable_noResources resources
    cases empty
  | _, _, _, .pad source =>
    rw [source.variable_noResources resources]; rfl
  | _, _, _, .unpad source =>
    have empty := source.variable_noResources resources
    exact List.map_eq_nil_iff.mp empty
  | _, _, _, .rowShift source =>
    have empty := source.variable_noResources resources
    cases empty
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransferResult.noResourceVariable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {expression assigned : VExpr} {index : Nat} {atom : Atom n}
    (result : GradedTransferResult env U registry target locals σ τ (fun _ => [])
      expression (.bvar index) assigned (.singleton atom)) : False := by
  have empty := result.observation.variable_noResources result.resultAvailable
  have adapter := result.adapter
  change ProfileAdapter env U registry target (AdapterNormal.profile result.rawDemand)
    (AdapterNormal.profile (raiseProfile result.rank result.bound (.singleton atom))) at adapter
  rw [empty, raiseProfile_singleton] at adapter
  have member : AdapterNormal.atom (raiseAtom result.rank result.bound atom) ∈
      (AdapterNormal.profile (Profile.singleton (raiseAtom result.rank result.bound atom))).atoms :=
    List.mem_singleton_self _
  obtain ⟨_, impossible, _⟩ := adapter.origin member
  exact List.not_mem_nil impossible

/-- Any proposed unit-like source case must repair this exact return
obligation when its constructor-side observation uses no variable resource. -/
theorem GradedTransfer.resourceFreeToVariable_impossible
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {expression assigned : VExpr} {index : Nat} {atom : Atom n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression (.singleton atom) footprint)
    (resources : footprint.Available (fun _ => []))
    (transfer : GradedTransfer env U registry target locals σ τ (fun _ => [])
      expression (.bvar index) assigned) : False := by
  obtain ⟨result⟩ := transfer observation resources
  exact result.noResourceVariable

end Lean4Lean.AnchoredSource.Adapted
