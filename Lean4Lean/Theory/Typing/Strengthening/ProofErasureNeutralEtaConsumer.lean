import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaConsumerReduction

/-! # Actual typed consumers retain neutral eta variants through beta

An ambient function variable with a non-proof input domain supplies the raw
neutral mark. Arbitrary consumers and independent beta paths preserve paired
variants. This is residual syntax, not yet a strengthening-safe comparison
readout; full primitive simulation and proof-domain marks remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A typed ambient variable and its eta expansion give a neutral mark. The
domain guard records its beta origin, so changing annotations remain tracked. -/
theorem proofErase_neutral_eta_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero) :
    NeutralEtaVariant (fun C j => j = i ∧ ProofShape.BetaRed (proofErase Γ A) C) 0
      (proofErase Γ (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))) (proofErase Γ (.bvar i)) := by
  have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  rw [proofErase_nativeEtaExpansion hΓ hA hf hn, EF]
  simpa only [etaArgument, if_neg hu, ProofShape.liftN, liftVar, Nat.not_lt_zero,
    if_false, Nat.add_zero, ProofShape.liftN_zero, Nat.add_comm] using
    (NeutralEtaVariant.etaL (n := 0) (A := proofErase Γ A) (i := i)
      (Guard := fun C j => j = i ∧ ProofShape.BetaRed (proofErase Γ A) C) ⟨rfl, .refl⟩)

/-- Every typed consumer retains the protected neutral mark in all occurrences,
including dependent annotations. Its body can apply, duplicate or ignore the
function. No head normalization or lambda-exposure hypothesis is required. -/
theorem proofErase_neutral_eta_consumer_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T) :
    NeutralEtaVariant (fun C j => j = i ∧ ProofShape.BetaRed (proofErase Γ A) C) 0
      (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.bvar i))) := by
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
    proofErase_instN hΓF hf Ctx.InstN.zero ht]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply NeutralEtaVariant.subst_images
  intro j
  cases j with
  | zero => exact proofErase_neutral_eta_variant hΓ hA hf hn hu
  | succ j => exact .refl

/-- Independent beta residuals of the actual consumer pair can be continued to
protected variants. This does not assert a common reduct or a comparison
certificate for those variants. The remaining readout must respect typing. -/
theorem proofErase_neutral_eta_consumer_beta_residuals
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst (.bvar i))) right) :
    ∃ left' right', ProofShape.BetaRed left left' ∧ ProofShape.BetaRed right right' ∧
      NeutralEtaVariant (fun C j => j = i ∧ ProofShape.BetaRed (proofErase Γ A) C) 0 left' right' := by
  have V := proofErase_neutral_eta_consumer_variant hΓ hA hf hn hu ht
  exact V.beta_residuals (fun H R => ⟨H.1, H.2.trans R⟩) RL RR

end Lean4Lean.VEnv.Strengthening
