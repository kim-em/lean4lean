import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredLambdaTrace
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedLambdaBody

/-! # Comparing marked lambda payloads below temporary control binders

Exact lower component histories and certificate descent remove temporary
control prefixes. Native backward context transport then returns the comparison
to the original binder. No strengthening hypothesis is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Comparing two lifted marked payload bodies under the left payload domain
suffices to compare the original bodies below all temporary controls. -/
theorem stage_zero_lambda_payload_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (PA : StageZeroLambdaOrigin D Γ C a u X x)
    (PB : StageZeroLambdaOrigin D Γ C b u Y y)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (X.liftN n :: proofEraseCtx Γ') mode (x.liftN n 1) (y.liftN n 1)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨C', _, _, HC, _, EC, _, RC, Ra⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, _, Rb⟩ := PB
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓC ha rfl rfl Ra
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓC hb rfl rfl Rb
  have hctx : IsDefEqCtx env univs Γ (C :: Γ) (C' :: Γ) := .succ .zero HC
  have ha' := HA.hasType.2.defeqDFC henv hctx
  have hb' := HB.hasType.2.defeqDFC henv hctx
  have EA' : proofErase (C' :: Γ) a' = x := (proofErase_defeqCtx hΓC hctx HA.hasType.2).symm.trans EA
  have EB' : proofErase (C' :: Γ) b' = y := (proofErase_defeqCtx hΓC hctx HB.hasType.2).symm.trans EB
  have hΓC' : OnCtx (C' :: Γ) (env.IsType univs) := ⟨hΓ, u, HC.hasType.2⟩
  have hΓC'' : OnCtx (C'.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, HC.hasType.2.weakN henv W⟩
  have EΓ : proofEraseCtx (C'.liftN n :: Γ') = X.liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W HC.hasType.2, EC]
  have H' := (proofErase_computed_joint_compare_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0)
    hΓC' hΓC'' W.succ EΓ ha' hb' (by simpa only [EA', EB'] using H)).1
    ⟨_, (ha'.isType henv hΓC').choose_spec⟩
  apply stage_zero_computed_body_pullback heq hs hΓ hC ha hb RC Ra Rb
  simpa only [proofEraseCtx, EC, EA', EB'] using H'

/-- Identical marked payloads give common exact body computations in the
original context, without needing a type comparison at the control boundary. -/
theorem stage_zero_lambda_common_payload_compare
    (PA : StageZeroLambdaOrigin D Γ C a u X x)
    (PB : StageZeroLambdaOrigin D Γ C b u X x) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨_, _, _, _, _, _, _, _, RA⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, _, RB⟩ := PB
  exact .compute RA RB (.leaf .refl)

/-- Displayed eta between lifted payload lambdas descends syntactically and
then compares the original bodies using typed eta/body beta. -/
theorem stage_zero_lambda_payload_eta_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (PA : StageZeroLambdaOrigin D Γ C a u X x)
    (PB : StageZeroLambdaOrigin D Γ C b u Y y)
    (H : EtaHead ((ProofShape.lam X x).liftN n) ((ProofShape.lam Y y).liftN n) ∨
      EtaHead ((ProofShape.lam Y y).liftN n) ((ProofShape.lam X x).liftN n)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨_, _, _, _, _, _, _, RA, Ra⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, RB, Rb⟩ := PB
  exact stage_zero_computed_lambda_eta_body_compare heq hs hΓ hC ha hb hna hnb
    (.lam RA (by simpa only [proofEraseCtx] using Ra))
    (.lam RB (by simpa only [proofEraseCtx] using Rb))
    (H.imp EtaHead.of_liftN EtaHead.of_liftN)

end Lean4Lean.VEnv.Strengthening
