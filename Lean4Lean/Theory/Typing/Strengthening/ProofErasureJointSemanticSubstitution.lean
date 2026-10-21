import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSemanticConversion

/-! # Arbitrary substitution from semantic head exposure

The application transport uses its recursively substituted argument guard.
Some-output recovery supplies a new Pi, and semantic carrier conversion moves
the guard to that Pi's native domain. Exact recovery of substituted images and
a separate carrier-domain re-synthesis premise are unnecessary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem recovery_ne_proof (R : ScopedTypeRecovery Step Δ e T) : e ≠ .proof := by
  induction R with
  | convert _ _ ih => exact ih
  | bvar | sort | const | lam | app | forallE | proj => intro E; cases E

/-- Under semantic head exposure and primitive substitution closure, every
joint checking constructor transports through arbitrary interpreted typed
substitution. Carrier conversion is applied only to the smaller argument
guard already returned by the shared transport induction. -/
theorem ProofShape.JointCheck.subst_of_head_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (H : JointCheck Step Δ kind sa sb) :
    JointTransportResult ContextSubstitution Step Δ kind sa sb := by
  apply H.transport ContextSubstitution hstep
    (fun W => ContextSubstitution.cons W) (fun W S => ContextSubstitution.sort W S)
    (fun R _ _ _ _ W => R.subst hsubst W)
  intro Γ Δ' τ f x y D C A B hΓ hf hx hy R _ W HX
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have hnf : ¬ IsProof Γ f := fun hp => recovery_ne_proof R (proofErase_eq_proof.2 hp)
  have hnfσ : ¬ IsProof Γ₀ (f.subst σ) := mt (isProof_subst hΓ₀ WS hf).1 hnf
  obtain ⟨D₀, C₀, hf₀, ED₀, EC₀⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using R)
  simp only [ProofShape.liftN_zero] at ED₀
  have hx₀ := argument_at_displayed_domain hΓ hf hf₀ hx
  have hy₀ := argument_at_displayed_domain hΓ hf hf₀ hy
  have hfσ := hf₀.subst henv.orderedStrong WS hΓ₀
  have hxσ := hx₀.subst henv.orderedStrong WS hΓ₀
  have hyσ := hy₀.subst henv.orderedStrong WS hΓ₀
  obtain ⟨out, RF⟩ := Hheads.recovery_exists hstep hΓ₀ hfσ hnfσ
  obtain ⟨rawD, rawC, RF⟩ := Hheads.recover_pi hstep hΓ₀ hfσ RF
  obtain ⟨D', C', hfNew, ED', EC'⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ₀ hΓ₀
    (show Ctx.LiftN 0 0 Γ₀ Γ₀ from .zero []) hfσ
    (by simpa only [ProofShape.liftN_zero] using RF)
  have HDD := (hfσ.uniqU henv hΓ₀ hfNew).forallE_inv henv hΓ₀ |>.1
  obtain ⟨⟨_, hD₀⟩, _, _⟩ := (hf₀.isType henv hΓ).forallE_inv henv
  have HXσ : JointCarrierGuard Step (proofEraseCtx Γ₀) (proofErase Γ₀ (D₀.subst σ))
      (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ)) := by
    rw [proofErase_subst_with hΓ₀ WS hD₀ ES, ED₀,
      proofErase_subst_with hΓ₀ WS hx₀ ES, proofErase_subst_with hΓ₀ WS hy₀ ES, EΓ₀]
    exact HX
  have HXnew := proofErase_joint_carrier_convert_of_heads hstep hsubst Hheads hΓ₀ hxσ hyσ
    (show env.IsDefEqU univs Γ₀ (D₀.subst σ) D' from ⟨_, HDD.choose_spec⟩) HXσ
  simp only [ProofShape.liftN_zero] at ED'
  rw [ED', proofErase_subst_with hΓ₀ WS hx₀ ES,
    proofErase_subst_with hΓ₀ WS hy₀ ES, EΓ₀] at HXnew
  rw [proofErase_subst_with hΓ₀ WS hf₀ ES, EΓ₀] at RF
  exact ⟨_, _, RF, HXnew⟩

/-- Actual arbitrary typed substitution preserves both joint comparison modes
under the head-exposure premise. No image-recovery premise is imposed. -/
theorem proofErase_joint_compare_subst_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Step (proofEraseCtx Γ₀) mode (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha E, proofErase_subst_with hΓ₀ W hb E]
  exact H.subst_of_head_exposure hstep hsubst Hheads W.wf ha hb rfl rfl rfl
    (ContextSubstitution.of_typed hΓ₀ W E)

/-- Actual arbitrary substitution transports the carrier together with both
endpoints. The selected domains inside applications may change by conversion. -/
theorem proofErase_joint_carrier_subst_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Step (proofEraseCtx Γ₀) (proofErase Γ₀ (A.subst σ))
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  obtain ⟨u, hA⟩ := ha.isType henv W.wf
  rw [proofErase_subst_with hΓ₀ W hA E, proofErase_subst_with hΓ₀ W ha E,
    proofErase_subst_with hΓ₀ W hb E]
  exact H.subst_of_head_exposure hstep hsubst Hheads W.wf ha hb rfl rfl rfl rfl
    (ContextSubstitution.of_typed hΓ₀ W E)

/-- Certified checking supports arbitrary typed substitution once semantic
head exposure is supplied; its primitive closure assumptions are already proved. -/
theorem proofErase_certified_compare_subst_of_heads
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) :=
  proofErase_joint_compare_subst_of_heads (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) Hheads hΓ₀ W ha hb H

end Lean4Lean.VEnv.Strengthening
