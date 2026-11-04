import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFrameworkTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeTransport

/-! # Full recursive checking through combined native image certificates

Finite family alignment and computationally joined output types coexist in
one substitution law, including beneath arbitrary binders. Both previous laws
embed, while their combination also permits computation before family readout.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
variable {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}
variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- An interpreted substitution with combined or exactly recovering images in each
typed realization of its source erasure. -/
def ImageSubstitution (hq : QuotRegistered env) (F : List VExpr → VExpr → Prop)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      Images hq F Γ Γ₀ σ τ

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem ImageSubstitution.interpretation (W : ImageSubstitution hq F Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The image condition extends through arbitrary typed binder realizations. -/
theorem ImageSubstitution.cons (W : ImageSubstitution hq F Δ Δ' τ) :
    ImageSubstitution hq F (A :: Δ) (A.subst τ :: Δ') τ.lift := by
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

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem ImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq F Γ Γ₀ σ τ) :
    ImageSubstitution hq F (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- All earlier finite-family interpreted substitutions embed in the combined law. -/
theorem ImageSubstitution.of_aligned
    (W : NativeFamilyFramework.ImageSubstitution (definitions hq) F Δ Δ' τ) :
    ImageSubstitution hq F Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, Images.of_aligned HI⟩

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- All common-reduct interpreted substitutions embed in the same law. -/
theorem ImageSubstitution.of_joined
    (W : JoinedNative.ImageSubstitution hq Δ Δ' τ) : ImageSubstitution hq F Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, Images.of_joined hΓ₀ WS ES HI⟩

/-- Full recursive transport at stage zero. Both the native and computed
application cases are discharged, with no target comparison/guard premises
left over from recursive subderivations. -/
theorem transport
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : ComputedJointCheck (fun _ => Step hq) Δ kind sa sb) :
    ComputedJointTransportResult (ImageSubstitution hq F) (fun _ => Step hq) Δ kind sa sb := by
  apply H.transport_application (Target := fun _ => Step hq) (ImageSubstitution hq F)
    (ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq)))
    (fun W => W.cons) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R _ _ _ _ W => R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
  intro Γ Δ' τ f x y C E A B g mode hΓ hf hx hy hn R W HF HX
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  have HF₀ : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (f.subst σ)) g := by
    simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HF
  have HX₀ : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ₀)
      (A.subst τ) (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ)) := by
    simpa only [proofErase_subst_with hΓ₀ WS hx ES,
      proofErase_subst_with hΓ₀ WS hy ES, EΓ₀] using HX
  have HH := application_subst (mode := mode) hcon hΓ₀ WS ES hf hn hx hy HI R HF₀ HX₀
  simpa only [proofErase_subst_with hΓ₀ WS hf ES, proofErase_subst_with hΓ₀ WS hx ES,
    proofErase_subst_with hΓ₀ WS hy ES, EΓ₀] using HH

/-- Common-typed comparison transports in the enlarged checker with exact
endpoint erasures and unchanged mode. -/
theorem compare_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq F Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := transport hcon H W.wf ha hb rfl rfl rfl
    (ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. The application subcases may convert a guard locally while the result retains this exact carrier. -/
theorem carrier_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq F Γ Γ₀ σ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := transport hcon H W.wf ha hb rfl rfl rfl rfl
    (ImageSubstitution.of_typed hΓ₀ W ES HI)
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  simpa only [proofErase_subst_with hΓ₀ W hA ES, proofErase_subst_with hΓ₀ W ha ES,
    proofErase_subst_with hΓ₀ W hb ES] using HH


end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
