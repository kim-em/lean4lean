import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrierPrefixes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation

/-! # Future checking through certified Eq type conversions

An explicit future comparison of the proposition indices licenses the type
computation. It transports the entire future carrier certificate at the minor,
so later substitutions and beta paths can reuse the result without an arbitrary
typed-composition or type-conversion law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A future index certificate supplies the explicit carrier computation
needed to pull back every future certificate from the minor to the probe.
The conclusion retains future paths of the probe itself and both endpoints. -/
theorem eqTypeProbe_future_carrier_of_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ S) a b) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) a b :=
  H.certified_carrier_prefix heq hs hΓ (eqTypeProbe_typed heq hΓ hS hP hQ hq)
    (eqTypeProbe_compute_certified_of_family heq hs hregistry hΓ hS hP hQ hq HF)

/-- A structurally subsingleton minor makes all endpoints future-related at
the probe, provided the proposition conversion has its own future certificate.
This discharges the unit composition example without using either input link
or assuming unrestricted typed composition. -/
theorem eqTypeProbe_future_subsingleton_of_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (Hsub : SubsingletonCarrier (proofErase Γ S)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) a b :=
  eqTypeProbe_future_carrier_of_family heq hs hregistry hΓ hS hP hQ hq HF
    (BetaStableCarrier.subsingleton Hsub)

end Lean4Lean.VEnv.Strengthening
