import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiCodomainComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalLambdaPayload

/-! # Pi codomain payloads at an independently converted terminal binder

Each Pi retains its own written domain. Component histories are read at a fixed
terminal reference binder, and selected payload checks return to that reference
using proved terminal context transport. No annotation computation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A comparison of lifted payload bodies descends to a fixed terminal binder,
even when neither original annotation computes from that reference binder. -/
theorem stage_zero_terminal_pi_payload_codomain_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a (.sort v)) (hb : env.HasType univs (C :: Γ) b (.sort v))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (PA : StageZeroPiOrigin D Γ A a u v X x) (PB : StageZeroPiOrigin D Γ B b u v Y y)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (X.liftN n :: proofEraseCtx Γ') mode (x.liftN n 1) (y.liftN n 1)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨A', _, HAA', _, EX, _, _, Ra⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, Rb⟩ := PB
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
theorem stage_zero_terminal_pi_common_payload_codomains
    (hΓ : OnCtx Γ (env.IsType univs))
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a (.sort v)) (hb : env.HasType univs (C :: Γ) b (.sort v))
    (PA : StageZeroPiOrigin D Γ A a u v X x) (PB : StageZeroPiOrigin D Γ B b u v X x) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨_, _, _, _, _, _, _, RA⟩ := PA
  obtain ⟨_, _, _, _, _, _, _, RB⟩ := PB
  exact .compute (stage_zero_body_history_at_reference hΓ HCA ha RA)
    (stage_zero_body_history_at_reference hΓ HCB hb RB) (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
