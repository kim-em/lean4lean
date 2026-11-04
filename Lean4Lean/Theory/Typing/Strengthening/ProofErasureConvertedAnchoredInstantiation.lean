import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedNeutralStageContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointFirstStageSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointAnchoredSubstitution

/-! # Instantiate through a convertible anchored selected type

A selected type may first change recursively at neutral leaves. The complete
body comparison is transported to that binder context, then the existing
anchored-image substitution theorem consumes the image at its selected type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every common-typed stage-zero body comparison instantiates by an image
with an anchored path at a recursively neutral-convertible selected type.
The path need not exist at the original assigned type. The binder conversion
and complete recursive body transport are proved, not extra hypotheses. -/
theorem proofErase_computed_joint_zero_compare_inst_converted_anchored
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : AnchoredFamilyRecovery D cut Γ p (proofErase Γ U) n)
    (ha : env.HasType univs (T :: Γ) a A)
    (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  have HC := proofErase_computed_joint_recursive_neutral_context hstep
    (erased_joint_stage_head 0) (fun H _ => erased_iota_primitive_subst H)
    hΓ HTU HT ha hb H
  have W : IsDefEqCtx env univs [] (T :: Γ) (U :: Γ) := .succ (.refl hΓ) HTU
  exact proofErase_computed_joint_zero_compare_inst_anchored hs hΓ hp HR
    (ha.defeqDFC henv W) (hb.defeqDFC henv W) HC

/-- The converted anchored-image criterion also transports complete first-layer
computations. Recursive neutral context conversion retains the exact output;
the existing anchored substitution then instantiates that output literally. -/
theorem proofErase_computed_joint_one_compute_inst_converted_anchored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : AnchoredFamilyRecovery D cut Γ p (proofErase Γ U) n)
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (T :: Γ))
      (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  have RC := proofErase_computed_joint_stage_compute_neutral_context heq hs hΓ HTU HT he R
  have W : IsDefEqCtx env univs [] (T :: Γ) (U :: Γ) := .succ (.refl hΓ) HTU
  exact proofErase_computed_joint_one_compute_inst_anchored heq hs hΓ hp HR (he.defeqDFC henv W) RC

end Lean4Lean.VEnv.Strengthening
