import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnchoredImageSubstitution

/-! # Recursive computed-domain checking under substitution of protected family paths

At stage zero the entire enlarged checker transports under substitutions whose
retained images recover exactly or have a selected protected-family path.
This admits type families at neutral assigned domains. The result remains in
the same enlarged checker, including arbitrarily nested computed applications.
Arbitrary function and structure values remain outside the result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An interpreted substitution with protected-family or recovering images in each
typed realization of its source erasure. -/
def AnchoredImageSubstitution (D : PureObservation.Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ cut, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem AnchoredImageSubstitution.interpretation (W : AnchoredImageSubstitution D Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, cut, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The image condition extends through arbitrary typed binder realizations. -/
theorem AnchoredImageSubstitution.cons (W : AnchoredImageSubstitution D Δ Δ' τ) :
    AnchoredImageSubstitution D (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, cut, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, cut + 1, ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB,
      ES.lift hΓ₀ WS hB, HI.cons hΓ₀ WS ES hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem AnchoredImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ) :
    AnchoredImageSubstitution D (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, cut, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Full recursive transport at stage zero. Both the native and computed
application cases are discharged, with no target comparison/guard premises
left over from recursive subderivations. -/
theorem ProofShape.ComputedJointCheck.transport_anchoredImages
    (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb) :
    ComputedJointTransportResult (AnchoredImageSubstitution D) (ErasedJointStage D 0) Δ kind sa sb := by
  apply H.transport_or_inert (Target := ErasedJointStage D 0) (AnchoredImageSubstitution D)
    (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs))
    (fun W => W.cons) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R _ _ _ _ W => R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, cut, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  have HH := proofErase_joint_zero_function_subst_anchored_domain hs hΓ₀ WS ES hf hn HI R
  simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HH

/-- Common-typed comparison transports in the enlarged checker with exact
endpoint erasures and unchanged mode. -/
theorem proofErase_computed_joint_zero_compare_subst_anchored
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_anchoredImages hs W.wf ha hb rfl rfl rfl
    (AnchoredImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. No semantic carrier conversion or selected-domain replacement is used. -/
theorem proofErase_computed_joint_zero_carrier_subst_anchored
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := H.transport_anchoredImages hs W.wf ha hb rfl rfl rfl rfl
    (AnchoredImageSubstitution.of_typed hΓ₀ W ES HI)
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  simpa only [proofErase_subst_with hΓ₀ W hA ES, proofErase_subst_with hΓ₀ W ha ES,
    proofErase_subst_with hΓ₀ W hb ES] using HH


/-- Single substitution of a value with a selected protected-family path preserves
recursive comparison, including nested computed-domain application guards. -/
theorem proofErase_computed_joint_zero_compare_inst_anchored
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p T)
    (HR : AnchoredFamilyRecovery D cut Γ p (proofErase Γ T) n)
    (ha : env.HasType univs (T :: Γ) a A)
    (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    proofErase_computed_joint_zero_compare_subst_anchored hs hΓ W
      (erasedSubstAgreement_one hΓT hp) (AnchoredOrRecoveringImages.inst HR) ha hb H

/-- A type-family image at a neutral assigned domain transports the complete
recursive comparison. The function may be typed there by conversion; no native
recovery or exact annotation exposure of that function is assumed. -/
theorem proofErase_computed_joint_zero_compare_inst_neutralFamily
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE C (.sort v)))
    (HC : AnchoredCarrier 0 (proofErase Γ C))
    (ha : env.HasType univs (.forallE C (.sort v) :: Γ) a A)
    (hb : env.HasType univs (.forallE C (.sort v) :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE C (.sort v) :: Γ)) mode
      (proofErase (.forallE C (.sort v) :: Γ) a)
      (proofErase (.forallE C (.sort v) :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  exact proofErase_computed_joint_zero_compare_inst_anchored hs hΓ hp
    (AnchoredFamilyRecovery.of_family hΓ hp HC) ha hb H

/-- Selected-path arguments support paired beta-redex comparison from a body
certificate. This covers function-valued type families, but does not assert
arbitrary endpoint beta stability or heterogeneous argument substitution. -/
theorem proofErase_computed_joint_zero_anchored_argument_beta
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p T)
    (HR : AnchoredFamilyRecovery D cut Γ p (proofErase Γ T) n)
    (ha : env.HasType univs (T :: Γ) a A)
    (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.app (.lam T a) p)) (proofErase Γ (.app (.lam T b) p)) := by
  obtain ⟨_, hT⟩ := hp.isType henv hΓ
  exact .compute
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hT ha) hp) .beta))
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hT hb) hp) .beta))
    (proofErase_computed_joint_zero_compare_inst_anchored hs hΓ hp HR ha hb H)

end Lean4Lean.VEnv.Strengthening
