import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming

/-! # Recovered-carrier comparison under native-image substitution

Both recovered endpoints keep their literal common output. The full carrier
guard transports at that output; no carrier completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeImageTransport
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

private theorem inferred (hstep : ErasedScopedPrimitiveDescent Source)
    (H : CarrierRecoveredCompare Source Δ false sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b) : env.IsDefEq univs Γ a b A := by
  have HH := proofErase_carrier_recovered_compare_descend hstep hΓ hΓ (Ctx.LiftN.zero []) rfl ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Ea, Eb] using H)
  exact (HH.2 rfl hna hnb).of_l henv hΓ ha

/-- Typed recovered-family comparison transports once compatible computation
transports and the target contains the native-image computation relation. -/
theorem recovered_of_compute
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (H : CarrierRecoveredCompare Source Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ImageSubstitution ImageStep Δ Δ' τ) :
    CarrierRecoveredCompare Target Δ' mode (sa.subst τ) (sb.subst τ) := by
  induction H generalizing Γ a b A Δ' τ with
  | base H => exact .base (check_of_compute hrename hstep hinclude hcompute H hΓ ha hb EΓ Ea Eb W)
  | recovered RA RB H =>
    obtain ⟨T, ha', ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ha
      (by simpa only [EΓ, Ea] using RA)
    have hb' := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha')
    exact .recovered
      (recovery_of_compute hrename hstep hinclude hcompute RA hΓ ha EΓ Ea W)
      (recovery_of_compute hrename hstep hinclude hcompute RB hΓ hb EΓ Eb W)
      (check_of_compute hrename hstep hinclude hcompute H hΓ ha' hb' EΓ ET Ea Eb W)
  | app HF HX ihf ihx =>
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := inferred hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | proj HM ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := inferred hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ih hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W)
      (ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons hrename))
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨v, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := inferred hstep HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, v, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := inferred hstep HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    exact .forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (W.cons hrename))
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .compute (hcompute RA hΓ ha EΓ Ea W) (hcompute RB hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm H ih => exact .symm (ih hΓ hb ha EΓ Eb Ea W)

end Lean4Lean.VEnv.Strengthening.NativeImageTransport
