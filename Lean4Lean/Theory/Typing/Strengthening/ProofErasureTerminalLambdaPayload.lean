import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalTransport

/-! # Marked lambda payloads with independently converted terminal binders

Each original function retains its written domain. Both body histories are read
in a fixed, ordinarily equal terminal context. This supports comparison through
symmetry without requiring computation between the written annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- A body history at an ordinarily converted binder has the exact same raw
source when read at the reference binder. Stage-zero context independence
moves the computation, while actual conversion justifies erasure agreement. -/
theorem stage_zero_body_history_at_reference
    (hΓ : OnCtx Γ (env.IsType univs)) (HCA : env.IsDefEq univs Γ C A (.sort u))
    (ha : env.HasType univs (C :: Γ) a T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) a) x) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) a) x := by
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, HCA.hasType.1⟩
  have E := proofErase_defeqCtx hΓC (IsDefEqCtx.succ .zero HCA) ha
  rw [E]
  exact R.recontext_independent (fun H => H)

/-- A comparison of lifted payload bodies descends to a fixed terminal binder,
even when neither original annotation computes from that reference binder. -/
theorem stage_zero_terminal_lambda_payload_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (PA : StageZeroLambdaOrigin D Γ A a u X x) (PB : StageZeroLambdaOrigin D Γ B b u Y y)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (X.liftN n :: proofEraseCtx Γ') mode (x.liftN n 1) (y.liftN n 1)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨A', _, _, HAA', _, EX, _, _, Ra⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, _, Rb⟩ := PB
  have Ra := stage_zero_body_history_at_reference hΓ HCA ha Ra
  have Rb := stage_zero_body_history_at_reference hΓ HCB hb Rb
  have HCX := HCA.trans HAA'
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, HCA.hasType.1⟩
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓC ha rfl rfl Ra
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓC hb rfl rfl Rb
  have hctx : IsDefEqCtx env univs Γ (C :: Γ) (A' :: Γ) := .succ .zero HCX
  have ha' := HA.hasType.2.defeqDFC henv hctx
  have hb' := HB.hasType.2.defeqDFC henv hctx
  have EA' : proofErase (A' :: Γ) a' = x := (proofErase_defeqCtx hΓC hctx HA.hasType.2).symm.trans EA
  have EB' : proofErase (A' :: Γ) b' = y := (proofErase_defeqCtx hΓC hctx HB.hasType.2).symm.trans EB
  have hΓX : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, HCX.hasType.2⟩
  have hΓX' : OnCtx (A'.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, HCX.hasType.2.weakN henv W⟩
  have EΓ : proofEraseCtx (A'.liftN n :: Γ') = X.liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W HCX.hasType.2, EX]
  have H' := (proofErase_computed_joint_compare_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0)
    hΓX hΓX' W.succ EΓ ha' hb' (by simpa only [EA', EB'] using H)).1
    ⟨_, (ha'.isType henv hΓX).choose_spec⟩
  have H'' := stage_zero_compare_terminal_context heq hs hΓ HCX.symm (HT.convert hΓ HCX) ha' hb' H'
  exact .compute Ra Rb (by simpa only [EA', EB'] using H'')

/-- Identical payload bodies compare at the reference binder, even with
independent original annotations and no computation between those annotations. -/
theorem stage_zero_terminal_lambda_common_payload_compare
    (hΓ : OnCtx Γ (env.IsType univs))
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (PA : StageZeroLambdaOrigin D Γ A a u X x) (PB : StageZeroLambdaOrigin D Γ B b u X x) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨_, _, _, _, _, _, _, _, RA⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, _, RB⟩ := PB
  exact .compute (stage_zero_body_history_at_reference hΓ HCA ha RA)
    (stage_zero_body_history_at_reference hΓ HCB hb RB) (.leaf .refl)

/-- Displayed eta between two differently annotated payloads has a typed beta
path between their bodies. Common actual function typing comes from ordinary
lambda domain conversion at the fixed reference binder. -/
theorem stage_zero_terminal_lambda_payload_eta_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (PA : StageZeroLambdaOrigin D Γ A a u X x) (PB : StageZeroLambdaOrigin D Γ B b u Y y)
    (H : EtaHead ((ProofShape.lam X x).liftN n) ((ProofShape.lam Y y).liftN n) ∨
      EtaHead ((ProofShape.lam Y y).liftN n) ((ProofShape.lam X x).liftN n)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have HA := PA
  have HB := PB
  obtain ⟨_, _, _, _, _, _, _, RA, Ra⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, RB, Rb⟩ := PB
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hfa := (IsDefEq.lamDF HCA ha).hasType.2
  have hgb := (IsDefEq.lamDF HCB hb).hasType.2
  obtain ⟨f, HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ hfa rfl
    (show proofErase Γ (.lam A a) = .lam _ _ from if_neg hna)
    (ScopedCompute.lam RA (by simpa only [proofEraseCtx] using Ra))
  obtain ⟨g, HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ hgb rfl
    (show proofErase Γ (.lam B b) = .lam _ _ from if_neg hnb)
    (ScopedCompute.lam RB (by simpa only [proofEraseCtx] using Rb))
  obtain ⟨A', a', rfl, _, _, Ea⟩ := erase_lam_inv Ef
  obtain ⟨B', b', rfl, _, _, Eb⟩ := erase_lam_inv Eg
  apply stage_zero_terminal_lambda_payload_body_compare heq hs hΓ HT HCA HCB ha hb hΓ (Ctx.LiftN.zero []) HA HB
  simp only [List.length_nil, ProofShape.liftN_zero]
  rcases H with H | H
  · have Rβ := proofErase_eta_lambda_bodies_beta hΓ HF.hasType.2 HG.hasType.2
      (by simpa only [Ef, Eg] using H.of_liftN)
    rw [Ea, Eb] at Rβ
    exact .compute (.beta Rβ) .refl (.leaf .refl)
  · have Rβ := proofErase_eta_lambda_bodies_beta hΓ HG.hasType.2 HF.hasType.2
      (by simpa only [Ef, Eg] using H.of_liftN)
    rw [Ea, Eb] at Rβ
    exact .compute .refl (.beta Rβ) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
