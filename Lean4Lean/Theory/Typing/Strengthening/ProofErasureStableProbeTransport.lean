import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedFamilyPrefixes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangePaths

/-! # Checking transport through Eq probes with future comparison certificates

Only a future comparison of the indices is required. Their computations may
end at distinct eta-related shapes rather than a common output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- All certified carrier guards at the minor also check at the Eq probe,
provided its proposition indices have a future comparison certificate. -/
theorem eqTypeProbe_certified_carrier_of_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ S) a b) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) a b :=
  .carrierCompute (eqTypeProbe_compute_certified_of_family heq hs hregistry hΓ hS hP hQ hq HF) H

/-- Every certified body comparison under the minor survives replacement of
that binder by the Eq probe, including non-joining indices. Its endpoints stay fixed, and the result retains
certificates for subsequent transport. This is the reverse-computation direction. -/
theorem eqTypeProbe_certified_context_of_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (ha : env.HasType univs (S :: Γ) a T) (hb : env.HasType univs (S :: Γ) b T)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (S :: Γ)) mode
      (proofErase (S :: Γ) a) (proofErase (S :: Γ) b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (eqTypeProbe u S P Q q :: Γ)) mode
      (proofErase (eqTypeProbe u S P Q q :: Γ) a)
      (proofErase (eqTypeProbe u S P Q q :: Γ) b) := by
  have HPQ := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs)
    hΓ hP hQ (.carrierChecked HF.base)
  exact proofErase_joint_context_compute_back (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) hΓ
    (eqTypeProbe_defeq heq hΓ hS hP hQ hq HPQ.toU)
    (eqTypeProbe_compute_certified_of_family heq hs hregistry hΓ hS hP hQ hq HF) ha hb H

end Lean4Lean.VEnv.Strengthening
