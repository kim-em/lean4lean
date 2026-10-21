import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta

/-! # Expressing joint carrier certificates as proposition comparisons

Canonical Eq has native recovery of its argument domain, independently of
recovery for the supplied endpoints. Its final application therefore turns any
joint carrier certificate into a comparison of two typed propositions. This
is a forward encoding, not a decoder for substituted carrier certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_app native_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction
variable [Params]

/-- Every typed joint carrier guard gives a comparison of Eq propositions at
the same stage and in either mode. The selected Eq argument domain is recovered
from its declaration; the carrier and endpoints need no recovery premise. -/
theorem proofErase_joint_carrier_propositions
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hz : env.HasType univs Γ z A) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u A z a)) (proofErase Γ (eqApp u A z b)) := by
  have h0 : env.HasType univs Γ (.const ``Eq [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    simpa [canonicalEqType, VExpr.instL, VLevel.inst] using
      (HasType.const (Γ := Γ) heq.1 (ls := [u]) (by simpa using hu) rfl)
  have h1 : env.HasType univs Γ (.app (.const ``Eq [u]) A)
      (.forallE A (.forallE A.lift (.sort .zero))) := by
    simpa [VExpr.inst, instVar, VExpr.liftN] using h0.app hA
  have h2 : env.HasType univs Γ (.app (.app (.const ``Eq [u]) A) z)
      (.forallE A (.sort .zero)) := by
    simpa only [VExpr.inst, VExpr.inst_lift] using h1.app hz
  have h3 : env.HasType univs Γ (eqApp u A z a) (.sort .zero) := h2.app ha
  have h4 : env.HasType univs Γ (eqApp u A z b) (.sort .zero) := h2.app hb
  have hn3 := not_isProof_of_sort hΓ h3
  have hn2 := not_isProof_fn hΓ h2 ha hn3
  have hn1 := not_isProof_fn hΓ h1 hz hn2
  have hn0 := not_isProof_fn hΓ h0 hA hn1
  have R0 := native_const (Step := Step) hΓ heq.1 (ls := [u]) (by simpa using hu) rfl hn0
  have R1 := native_app hΓ h0 hA hn1
    (by simpa [canonicalEqType, VExpr.instL, VLevel.inst] using R0)
  have R2 := native_app hΓ h1 hz hn2
    (by simpa [VExpr.inst, instVar, VExpr.liftN] using R1)
  have R2 : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.app (.app (.const ``Eq [u]) A) z))
      (proofErase Γ (.forallE A (.sort .zero))) := by
    simpa only [VExpr.inst, VExpr.inst_lift] using R2
  have hPi := HasType.forallE hA (HasType.sort (l := .zero) (by trivial))
  rw [show proofErase Γ (.forallE A (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at R2
  rw [show proofErase Γ (eqApp u A z a) =
    .app (proofErase Γ (.app (.app (.const ``Eq [u]) A) z)) (proofErase Γ a) from if_neg hn3,
    show proofErase Γ (eqApp u A z b) =
    .app (proofErase Γ (.app (.app (.const ``Eq [u]) A) z)) (proofErase Γ b) from
      if_neg (not_isProof_of_sort hΓ h4)]
  exact .appCarrier R2 (.leaf .refl) H

/-- Assuming only proposition beta stability of the joint union, an arbitrary
typed substitution preserves the proposition encoding of every carrier guard.
This does not claim a carrier guard at the substituted carrier: decoding the
proposition certificate, or using it in a general singleton guard, is separate. -/
theorem proofErase_joint_carrier_propositions_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D)) (hu : u.WF univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hC : env.HasType univs (A :: Γ) C (.sort u))
    (hz : env.HasType univs (A :: Γ) z C)
    (ha : env.HasType univs (A :: Γ) a C) (hb : env.HasType univs (A :: Γ) b C)
    (hx : env.HasType univs Γ x A)
    (H : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ∃ later, stage ≤ later ∧ JointCompare (ErasedJointStage D later) (proofEraseCtx Γ) true
      (proofErase Γ ((eqApp u C z a).inst x)) (proofErase Γ ((eqApp u C z b).inst x)) :=
  Hbeta.inst heq hs hΓA (HasType.eqApp heq hu hC hz ha) (HasType.eqApp heq hu hC hz hb) hx
    (proofErase_joint_carrier_propositions heq hu hΓA hC hz ha hb H)

end Lean4Lean.VEnv.Strengthening
