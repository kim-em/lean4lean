import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroLambdaReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBackwardContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaSubstitution

/-! # Pull computed lambda body comparisons back to their original binder

Stage-zero component histories preserve exact native images for the original
binder. Typed replay realizes computed bodies at their original common dependent
type, so a comparison under a computed binder pulls back at its existing stage.
The literal computed lambda endpoints may have different domains and bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Stage-zero computation of a binder and both typed bodies can precede a
body comparison at any finite stage without increasing that stage. Actual
replay retains the common dependent body type; backward native images move the
comparison from the computed binder to the original one. -/
theorem stage_zero_computed_body_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ C) X)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) a) x)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) b) y)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (X :: proofEraseCtx Γ) mode x y) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  obtain ⟨C', HC, EC⟩ := proofErase_scoped_compute_realize hstep hΓ hC rfl rfl RC
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓC ha rfl rfl RA
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓC hb rfl rfl RB
  have hctx : IsDefEqCtx env univs Γ (C :: Γ) (C' :: Γ) := .succ .zero HC
  have ha' := HA.hasType.2.defeqDFC henv hctx
  have hb' := HB.hasType.2.defeqDFC henv hctx
  have EA' : proofErase (C' :: Γ) a' = x :=
    (proofErase_defeqCtx hΓC hctx HA.hasType.2).symm.trans EA
  have EB' : proofErase (C' :: Γ) b' = y :=
    (proofErase_defeqCtx hΓC hctx HB.hasType.2).symm.trans EB
  have hΓC' : OnCtx (C' :: Γ) (env.IsType univs) := ⟨hΓ, u, HC.hasType.2⟩
  have H' : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx (C' :: Γ)) mode (proofErase (C' :: Γ) a') (proofErase (C' :: Γ) b') := by
    simpa only [proofEraseCtx, EC, EA', EB'] using H
  have R := StaticStructureEtaNativeSubstitution.check heq hs H' hΓC' ha' hb' rfl rfl rfl
    (static_structure_native_backward_context heq hs hΓ HC (by simpa only [EC] using RC))
  have R' : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx (C :: Γ)) mode x y := by
    simpa only [Nat.add_zero, ProofShape.subst_id, EA', EB'] using R
  exact .compute (RA.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n) H))
    (RB.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n) H)) R'

/-- If two functions compute to literal lambdas whose bodies compare under
the left computed domain, their original bodies compare under the original
common binder. All computations may use control wrappers and beta interleavings.
The final body check is arbitrary and keeps its stage and mode. This covers
structural lambda comparison after computation; general computed function
comparisons may instead end in applications or recursive eta and remain unresolved. -/
theorem stage_zero_computed_lambda_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) (.lam X x))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) (.lam Y y))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (X :: proofEraseCtx Γ) mode x y) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨_, _, _, _, _, _, _, RC, Ra⟩ :=
    proofErase_stage_zero_lambda_components heq hs hΓ hC ha hna RA
  obtain ⟨_, _, _, _, _, _, _, _, Rb⟩ :=
    proofErase_stage_zero_lambda_components heq hs hΓ hC hb hnb RB
  exact stage_zero_computed_body_pullback heq hs hΓ hC ha hb RC Ra Rb H

/-- Displayed eta between computed literal lambda endpoints also supplies an
original-body comparison. Typed replay at the original common Pi validates the
proof-marker eta case; the exposed bodies have a beta path in one direction.
This covers eta leaves and etaLams at the computed boundary, in either mode. -/
theorem stage_zero_computed_lambda_eta_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) (.lam X x))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) (.lam Y y))
    (H : EtaHead (.lam X x) (.lam Y y) ∨ EtaHead (.lam Y y) (.lam X x)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  obtain ⟨f, HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hC ha) rfl
    (show proofErase Γ (.lam C a) = .lam _ _ from if_neg hna) RA
  obtain ⟨g, HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hC hb) rfl
    (show proofErase Γ (.lam C b) = .lam _ _ from if_neg hnb) RB
  obtain ⟨A, a', rfl, _, _, Ea⟩ := erase_lam_inv Ef
  obtain ⟨B, b', rfl, _, _, Eb⟩ := erase_lam_inv Eg
  apply stage_zero_computed_lambda_body_compare heq hs hΓ hC ha hb hna hnb RA RB
  rcases H with H | H
  · have Rβ := proofErase_eta_lambda_bodies_beta hΓ HF.hasType.2 HG.hasType.2
      (by simpa only [Ef, Eg] using H)
    rw [Ea, Eb] at Rβ
    exact .compute (.beta Rβ) .refl (.leaf .refl)
  · have Rβ := proofErase_eta_lambda_bodies_beta hΓ HG.hasType.2 HF.hasType.2
      (by simpa only [Ef, Eg] using H)
    rw [Ea, Eb] at Rβ
    exact .compute .refl (.beta Rβ) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
