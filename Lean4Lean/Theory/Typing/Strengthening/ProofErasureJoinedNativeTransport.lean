import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeSubstitution

/-! # Recursive checking through native images with joined carriers

Typed confluence allows recovery outputs to reduce further. The simultaneous
carrier theorem transports each argument guard forward to the recovered domain,
so the complete checker survives without exact assigned-output recovery.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private forall_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
variable [Params]
variable {hq : QuotRegistered env}

/-- An interpreted substitution whose native image types join the assigned
carriers in every typed realization of the source erasure. -/
def ImageSubstitution (hq : QuotRegistered env)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      Images hq Γ Γ₀ τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem ImageSubstitution.interpretation (W : ImageSubstitution hq Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The image condition extends through arbitrary typed binder realizations. -/
theorem ImageSubstitution.cons (W : ImageSubstitution hq Δ Δ' τ) :
    ImageSubstitution hq (A :: Δ) (A.subst τ :: Δ') τ.lift := by
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
theorem ImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq Γ Γ₀ τ) :
    ImageSubstitution hq (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Full recursive transport in the repaired core. Both native and computed
application cases are discharged, with no target comparison/guard premises
left over from recursive subderivations. -/
theorem transport
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : ComputedJointCheck (fun _ => Step hq) Δ kind sa sb) :
    ComputedJointTransportResult (ImageSubstitution hq) (fun _ => Step hq) Δ kind sa sb := by
  apply H.transport_application (Target := fun _ => Step hq) (ImageSubstitution hq)
    (ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq)))
    (fun W => W.cons) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R _ _ _ _ W => R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation)
  intro Γ Δ' τ f x y C E A B g mode hΓ hf hx hy _hn R W HF HX
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  have HF₀ : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (f.subst σ)) g := by
    simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HF
  have HX₀ : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ₀)
      (A.subst τ) (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ)) := by
    simpa only [proofErase_subst_with hΓ₀ WS hx ES,
      proofErase_subst_with hΓ₀ WS hy ES, EΓ₀] using HX
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  obtain ⟨C₀, E₀, hfPi, EC₀, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf (by simpa only [ProofShape.liftN_zero] using R)
  have hx₀ := argument_at_displayed_domain hΓ hf hfPi hx
  have hy₀ := argument_at_displayed_domain hΓ hf hfPi hy
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨_, hC₀⟩, _, _⟩ := hPi.forallE_inv henv
  have EC : proofErase Γ₀ (C₀.subst σ) = A.subst τ := by
    rw [proofErase_subst_with hΓ₀ WS hC₀ ES]
    exact congrArg (fun x : ProofShape => x.subst τ) (by simpa only [ProofShape.liftN_zero] using EC₀)
  obtain ⟨out', HR, RC⟩ := recovery_subst hcon R hΓ₀ WS ES hf rfl rfl HI
  obtain ⟨A', B', rfl, RA, _⟩ := forall_parts hq RC
  have HX' := computed_carrier_compute_forward hq hcon hΓ₀
    (hx₀.subst henv.orderedStrong WS hΓ₀) (hy₀.subst henv.orderedStrong WS hΓ₀)
    (by simpa only [EC] using HX₀) (by simpa only [EC] using RA)
  have HH := ComputedJointCheck.appCarrier (mode := mode) HR
    (by simpa only [proofErase_subst_with hΓ₀ WS hf ES] using HF₀) HX'
  simpa only [proofErase_subst_with hΓ₀ WS hx ES,
    proofErase_subst_with hΓ₀ WS hy ES, EΓ₀] using HH

/-- Common-typed comparison transports in the enlarged checker with exact
endpoint erasures and unchanged mode. -/
theorem compare_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := transport hcon H W.wf ha hb rfl rfl rfl
    (ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- Carrier checking transports recursively with the exact substituted
carrier. Internal application checks may convert an argument guard locally. -/
theorem carrier_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images hq Γ Γ₀ τ)
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


end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
