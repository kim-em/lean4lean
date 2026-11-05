import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedRigidValueInjectivity
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalEquality
import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Computational injectivity for normalized family heads

A sort-headed family supplies the telescope and saturation evidence needed by
the value observer. No argument-history premise is required from callers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- Computational equality of saturated sort-headed rigid families gives
computational equality of every parameter and index, at its actual assignment. -/
theorem TypedComputationEqU.rigid_spine_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hS : SortHeaded c ls) (hS' : SortHeaded c ls')
    (ht : env.HasType univs Γ (VExpr.mkApps (.const c ls) args) (.sort u))
    (H : TypedComputationEqU D Γ (VExpr.mkApps (.const c ls) args)
      (VExpr.mkApps (.const c ls') args')) :
    List.Forall₂ (TypedComputationEqU D Γ) args args' := by
  have ht' := ht.defeqU_l henv hΓ H.defeq
  obtain ⟨doms, w, hf⟩ := hS hΓ
  obtain ⟨doms', w', hf'⟩ := hS' hΓ
  have EL := HasType.mkApps_sort_arity henv hΓ hf ht
  have EL' := HasType.mkApps_sort_arity henv hΓ hf' ht'
  obtain ⟨result, HW, _⟩ := HasType.mkApps_telescope henv hΓ hf ⟨_, ht⟩
    (EL ▸ VExpr.takeForalls_wrapForalls doms (.sort w))
  obtain ⟨result', HW', _⟩ := HasType.mkApps_telescope henv hΓ hf' ⟨_, ht'⟩
    (EL' ▸ VExpr.takeForalls_wrapForalls doms' (.sort w'))
  exact (TypedComputationEq.rigid_spine_inv heq hs HF hΓ hc hD hf
    (EL.symm ▸ RigidDemandProfile.sortTelescope_wrapForalls doms w) HW hf'
    (EL'.symm ▸ RigidDemandProfile.sortTelescope_wrapForalls doms' w') HW' ht H.choose_spec).2

end Lean4Lean.VEnv.Strengthening
