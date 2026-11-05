import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeApplicationTailJoin

/-! # Complete native control-application outputs in actual environments

Actual environment definitions discharge core confluence, universe compatibility
and rigid-head preservation. Fixed-sort argument checks give the shared argument
computation. Native outputs include all selected Pis and final conversion tails.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]
namespace EnvironmentCore

/-- Arbitrary complete stage-zero recoveries of applications of one actual
function join when both arguments check against the same fixed sort. No selected
Pi comparison, result-type comparison, native image condition or type-fork axiom
is assumed. This covers a fixed function, not two arbitrarily compared functions. -/
theorem stage_zero_control_application_outputs_join
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) xMode (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) yMode (.sort u) (proofErase Γ y))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.app f y)) outR) :
    ComputeJoin (ErasedLevelCore definitions) outL outR := by
  have hp : env.HasType univs Γ (.sort u) C := HC.defeq (.sort hu)
  have EP : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ (HasType.sort hu))
  have RX := stage_zero_compared_sort_returns heq sound hΓ hu (HC.symm.defeq hx) HX
  have RY := stage_zero_compared_sort_returns heq sound hΓ hu (HC.symm.defeq hy) HY
  rw [← EP] at RX RY
  exact stage_zero_same_function_native_application_outputs_join heq sound (levelCompatible hcon) hcon
    no_rigid (typed_core_confluence hcon) hΓ hf hx hy hp RX RY RL RR

/-- The common core reduct supplies an actual stage-zero checking certificate
for the complete native outputs, in either mode. No normalization of the function
or its dependent result types is required. -/
theorem stage_zero_control_application_outputs_compare
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) xMode (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) yMode (.sort u) (proofErase Γ y))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.app f y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) mode outL outR := by
  obtain ⟨shared, L, R⟩ := stage_zero_control_application_outputs_join heq hcon hΓ hu HC hf hx hy HX HY RL RR
  exact .compute (L.scoped (fun H => .base (.inl H))) (R.scoped (fun H => .base (.inl H))) (.leaf .refl)

end EnvironmentCore
end Lean4Lean.VEnv.Strengthening
