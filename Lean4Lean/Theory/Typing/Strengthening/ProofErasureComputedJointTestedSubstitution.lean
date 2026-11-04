import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTestedImageSubstitution

/-! # Recursive computed-domain checking under substitution of shared typed interpretations

At stage zero the entire enlarged checker transports under substitutions whose
retained images recover exactly or have a selected shared-test path.
The shared test can specialize a generic type parameter. The result remains in
the same enlarged checker, including arbitrarily nested computed applications.
Arbitrary function and structure values remain outside the result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An interpreted substitution with shared-test or recovering images in each
typed realization of its source erasure. -/
def TestedImageSubstitution (D : PureObservation.Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ Γt ν, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      OnCtx Γt (env.IsType univs) ∧ Ctx.SubstEq env univs Γt ν ν Γ₀ ∧
      TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem TestedImageSubstitution.interpretation (W : TestedImageSubstitution D Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, Γt, ν, hΓ₀, EΓ₀, WS, ES, _, _, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The image condition extends through arbitrary typed binder realizations. -/
theorem TestedImageSubstitution.cons (W : TestedImageSubstitution D Δ Δ' τ) :
    TestedImageSubstitution D (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, Γt, ν, hΓ₀, EΓ₀, WS, ES, hΓt, WT, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, (B.subst σ).subst ν :: Γt, ν.lift,
      ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB, ES.lift hΓ₀ WS hB,
      ⟨hΓt, u, hB'.subst henv.orderedStrong WT hΓt⟩, WT.lift henv.ordered hB',
      HI.cons hΓ₀ WS ES hΓt WT hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem TestedImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (HI : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ) :
    TestedImageSubstitution D (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, Γt, ν, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, hΓt, WT, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Full recursive transport at stage zero. Both the native and computed
application cases are discharged, with no target comparison/guard premises
left over from recursive subderivations. -/
theorem ProofShape.ComputedJointCheck.transport_testedImages
    (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb) :
    ComputedJointTransportResult (TestedImageSubstitution D) (ErasedJointStage D 0) Δ kind sa sb := by
  apply H.transport (Target := ErasedJointStage D 0) (TestedImageSubstitution D)
    (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs))
    (fun W => W.cons) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R _ _ _ _ W => R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, Γt, ν, hΓ₀, EΓ₀, WS, ES, hΓt, WT, HI⟩ := W hΓ rfl
  have HH := proofErase_joint_zero_function_subst_tested_domain hs hΓ₀ WS ES hΓt WT hf hn HI R
  simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HH

/-- Common-typed comparison transports in the enlarged checker with exact
endpoint erasures and unchanged mode. -/
theorem proofErase_computed_joint_zero_compare_subst_tested
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (HI : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_testedImages hs W.wf ha hb rfl rfl rfl
    (TestedImageSubstitution.of_typed hΓ₀ W ES hΓt WT HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. No semantic carrier conversion or selected-domain replacement is used. -/
theorem proofErase_computed_joint_zero_carrier_subst_tested
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (HI : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_testedImages hs W.wf ha hb rfl rfl rfl rfl
    (TestedImageSubstitution.of_typed hΓ₀ W ES hΓt WT HI)
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  simpa only [proofErase_subst_with hΓ₀ W hA ES, proofErase_subst_with hΓ₀ W ha ES,
    proofErase_subst_with hΓ₀ W hb ES] using HH

end Lean4Lean.VEnv.Strengthening
