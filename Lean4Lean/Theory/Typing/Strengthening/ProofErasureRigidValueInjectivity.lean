import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedValueChain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout

/-! # The precise value-history input to computational rigid injectivity

Existing head readout gives a literal rigid spine after beta cleanup. Only its
argument histories remain missing. This module states that input at literal
endpoints and derives typed argument chains from it and type-fork joining.
Forward argument origins are deliberately not required: caller eta refutes them.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Missing rigid argument-history theorem. A full-union path between a typed
rigid type spine and a literal spine of the same head must retain pointwise
scoped value chains. The endpoints need not have the same universe instances.
This is unproved; head/arity readout alone supplies no such argument histories. -/
def RigidSpineValueHistory (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ c ls args u ls' args'}, OnCtx Γ (env.IsType univs) → env.Rigid c →
    (∀ levels rhs, ¬ D.unfolds c levels rhs) →
    env.HasType univs Γ (VExpr.mkApps (.const c ls) args) (.sort u) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) (ProofShape.mkApps (.const c ls') args') →
    List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ)) (args.map (proofErase Γ)) args'

/-- Two argument lists with histories to the same raw vector give exact typed
chains whenever ordinary rigid injectivity supplies their common assignments.
Ordinary equalities here are used only for endpoint typing. -/
theorem scoped_value_histories_reify
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : List.Forall₂ (env.IsDefEqU univs Γ) args args')
    (HL : List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ)) (args.map (proofErase Γ)) out)
    (HR : List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ)) (args'.map (proofErase Γ)) out) :
    List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args' := by
  induction HE generalizing out with
  | nil => exact .nil
  | cons H _ ih =>
    cases HL with
    | cons CL HL =>
      cases HR with
      | cons CR HR =>
        obtain ⟨A, H⟩ := H
        exact .cons ⟨A, (CL.trans heq hs CR.symm).at_endpoints heq hs hΓ H.hasType.1 H.hasType.2⟩
          (ih HL HR)

/-- Computational rigid-spine injectivity follows from the explicit missing
literal-endpoint history theorem and TypeForkJoin. The existing head observer
provides beta cleanup; no additional head-exposure premise is introduced. -/
theorem TypedComputationEq.rigid_spine_inv_of_value_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : TypeForkJoin D) (HV : RigidSpineValueHistory D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : env.HasType univs Γ (.const c ls) T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const c ls) args) (.sort u))
    (H : TypedComputationEq D Γ (VExpr.mkApps (.const c ls) args)
      (VExpr.mkApps (.const c ls') args') A) :
    List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args' := by
  obtain ⟨hls, HA⟩ := H.defeq.toU.rigidApp_inv henv hΓ hc ht
  have H := H.at_source_type hΓ ht
  obtain ⟨shared, RL, RR⟩ := H.type_join heq hs HF hΓ
  obtain ⟨levels, outputs, _, RB⟩ :=
    RigidDemandProfile.static_structure_rigid_telescope_head_readout heq hs hc hD hΓ hf HT HW RL
  have HL := HV hΓ hc hD ht (RL.trans (.beta RB))
  have HR := HV hΓ hc hD H.defeq.hasType.2 (RR.trans (.beta RB))
  exact ⟨hls, scoped_value_histories_reify heq hs hΓ HA HL HR⟩

end Lean4Lean.VEnv.Strengthening
