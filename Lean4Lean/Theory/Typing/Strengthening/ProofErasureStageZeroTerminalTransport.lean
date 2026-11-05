import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalImages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Full comparison transport through terminal images at stage zero

The native application branch either retains its selected Pi or exposes a
lambda at the exact selected domain via a typed terminal path. Both outcomes
are supported by the recursive comparison grammar. Converted terminal binders
therefore need no forward annotation computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Interpreted substitutions with exact native or terminal retained images. -/
def StageZeroTerminalSubstitution (D : PureObservation.Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      StageZeroTerminalImages D Γ Γ₀ σ τ

/-- Forgetting image classification gives an ordinary interpreted substitution. -/
theorem StageZeroTerminalSubstitution.interpretation (W : StageZeroTerminalSubstitution D Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- Interpreted terminal substitutions extend through typed binders. -/
theorem StageZeroTerminalSubstitution.cons
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : StageZeroTerminalSubstitution D Δ Δ' τ) :
    StageZeroTerminalSubstitution D (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB,
      ES.lift hΓ₀ WS hB, HI.cons heq hs hΓ₀ WS ES hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One typed source realization supplies the interpreted image condition. -/
theorem StageZeroTerminalSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : StageZeroTerminalImages D Γ Γ₀ σ τ) :
    StageZeroTerminalSubstitution D (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Every comparison and carrier constructor transports under terminal-image
substitution at the unchanged expansion base. Native application uses exact
recovery or the proved selected-domain exposure; no body-check or application
repair premise remains. This theorem does not assert transport at later stages. -/
theorem ProofShape.ComputedJointCheck.transport_stage_zero_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb) :
    ComputedJointTransportResult (StageZeroTerminalSubstitution D)
      (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb := by
  apply H.transport (StageZeroTerminalSubstitution D)
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (fun W => W.cons heq hs) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R hΓ ht EΓ Ee W => R.subst_typed
      (erased_static_structure_eta_expansion_stage_descent heq hs 0)
      stage_zero_primitive_substitution hΓ ht EΓ Ee W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  rcases stage_zero_recovery_subst_terminal_images heq hs R hΓ₀ WS ES hf rfl rfl HI with
    RN | ⟨T, n, HP, ET⟩
  · exact .inl (EΓ₀ ▸ RN)
  · have HL := HP.selected_domain heq hs hΓ₀ (hf.subst henv.orderedStrong WS hΓ₀)
      (mt (isProof_subst hΓ₀ WS hf).1 hn) ET
    exact .inr (by simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HL)

/-- Any terminal typed value can replace its assigned binder in a whole
stage-zero body comparison. The assigned type need not compute from the type
certifying terminality, and both comparison modes are preserved. -/
theorem stage_zero_compare_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := P)).substEq hΓP hp
  have HI : StageZeroTerminalImages D (P :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := by
    intro i T hl _
    cases hl with
    | zero => exact .inr HT
    | succ hl =>
      apply Or.inl
      simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
      exact .bvar
  have HR := H.transport_stage_zero_terminal heq hs hΓP ha hb rfl rfl rfl
    (StageZeroTerminalSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓP hp) HI)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha, proofErase_instN hΓP hp Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR

/-- Ordinary conversion of a terminal-valued binder supplies an interpreted
terminal substitution in the expansion base, without annotation computation. -/
theorem StageZeroTerminalSubstitution.terminal_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A) :
    StageZeroTerminalSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply StageZeroTerminalSubstitution.of_typed hΓB W ES
  intro i T hl _
  cases hl with
  | zero => exact .inr (HA.convert hΓ HAB)
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    exact .bvar

/-- Full stage-zero body comparisons transport across ordinarily equal
terminal-valued binders. In particular either direction of conversion between
a universe and any equal binder is allowed. Endpoints and mode remain exact. -/
theorem stage_zero_compare_terminal_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_stage_zero_terminal heq hs hΓA ha hb rfl rfl rfl
    (StageZeroTerminalSubstitution.terminal_context hΓ HAB HA)

end Lean4Lean.VEnv.Strengthening
