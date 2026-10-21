import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedDomainSubstitution

/-! # Recursive computed-domain checking under substitution of types

At stage zero the entire enlarged checker transports under substitutions whose
retained images recover exactly or have a literal assigned sort. Single
substitution of any type satisfies this condition. The result remains in the
same enlarged checker, including arbitrarily nested computed applications.
This is not substitution by arbitrary function or structure values.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An interpreted substitution with exact-sort or recovering images in each
typed realization of its source erasure. -/
def TypeImageSubstitution (D : PureObservation.Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem TypeImageSubstitution.interpretation (W : TypeImageSubstitution D Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The image condition extends through arbitrary typed binder realizations. -/
theorem TypeImageSubstitution.cons (W : TypeImageSubstitution D Δ Δ' τ) :
    TypeImageSubstitution D (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB,
      ES.lift hΓ₀ WS hB, HI.cons hΓ₀ WS ES hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem TypeImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ) :
    TypeImageSubstitution D (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Full recursive transport at stage zero. Both the native and computed
application cases are discharged, with no target comparison/guard premises
left over from recursive subderivations. -/
theorem ProofShape.ComputedJointCheck.transport_typeImages
    (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb) :
    ComputedJointTransportResult (TypeImageSubstitution D) (ErasedJointStage D 0) Δ kind sa sb := by
  apply H.transport (Target := ErasedJointStage D 0) (TypeImageSubstitution D)
    (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs))
    (fun W => W.cons) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R _ _ _ _ W => R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  have HH := proofErase_joint_zero_function_subst_selected_domain hs hΓ₀ WS ES hf hn HI R
  simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HH

/-- Common-typed comparison transports in the enlarged checker with exact
endpoint erasures and unchanged mode. -/
theorem proofErase_computed_joint_zero_compare_subst
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_typeImages hs W.wf ha hb rfl rfl rfl
    (TypeImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. No semantic carrier conversion or selected-domain replacement is used. -/
theorem proofErase_computed_joint_zero_carrier_subst
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_typeImages hs W.wf ha hb rfl rfl rfl rfl
    (TypeImageSubstitution.of_typed hΓ₀ W ES HI)
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  simpa only [proofErase_subst_with hΓ₀ W hA ES, proofErase_subst_with hΓ₀ W ha ES,
    proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Single substitution of any type, including an arbitrary proposition,
preserves recursive computed-domain comparison at stage zero. The source may
already contain arbitrarily nested computed-domain applications. -/
theorem proofErase_computed_joint_zero_compare_inst_type
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a A)
    (hb : env.HasType univs (.sort u :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (.sort u :: Γ)) mode
      (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := .sort u)).substEq hΓU hp
  have ES : ErasedSubstAgreement (.sort u :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓU hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    proofErase_computed_joint_zero_compare_subst hs hΓ W ES
      (ExactSortOrRecoveringImages.inst_type hΓ hp) ha hb H

/-- Single substitution of any type also preserves recursive carrier checking
with the literal erasure of the substituted carrier. -/
theorem proofErase_computed_joint_zero_carrier_inst_type
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a A)
    (hb : env.HasType univs (.sort u :: Γ) b A)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (.sort u :: Γ))
      (proofErase (.sort u :: Γ) A) (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (A.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := .sort u)).substEq hΓU hp
  have ES : ErasedSubstAgreement (.sort u :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓU hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    proofErase_computed_joint_zero_carrier_subst hs hΓ W ES
      (ExactSortOrRecoveringImages.inst_type hΓ hp) ha hb H

/-- Compared bodies instantiate at an arbitrary type argument and compare
both beta-redexes in the same enlarged checker. This needs no recovery of the
argument, even when the body comparison contains computed-domain applications.
It assumes a body certificate; arbitrary endpoint beta stability is not asserted. -/
theorem proofErase_computed_joint_zero_type_argument_beta
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a A)
    (hb : env.HasType univs (.sort u :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (.sort u :: Γ)) mode
      (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.app (.lam (.sort u) a) p))
      (proofErase Γ (.app (.lam (.sort u) b) p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  exact .compute
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hU ha) hp) .beta))
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hU hb) hp) .beta))
    (proofErase_computed_joint_zero_compare_inst_type hs hΓ hp ha hb H)

end Lean4Lean.VEnv.Strengthening
