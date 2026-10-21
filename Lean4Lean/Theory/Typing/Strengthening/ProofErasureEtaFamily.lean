import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedEtaConfluence

/-! # Future family certificates for typed function eta

Typed head eta survives independent beta paths and interpreted substitutions.
The resulting certificate compares residuals; it does not require the two
eta endpoints to share a computational reduct.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

omit [Params] in
private theorem beta_only (H : ScopedCompute (fun _ _ _ => False) Δ a b) :
    ProofShape.BetaRed a b := by
  induction H with
  | base H => exact H.elim
  | beta H => exact H
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | proj _ ih => exact .proj ih

/-- Independent beta reductions of a typed displayed eta pair still admit a
joint comparison. Only beta confluence is used, with no primitive reductions. -/
theorem proofErase_eta_head_beta
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : EtaHead (proofErase Γ e) (proofErase Γ f))
    (RE : ProofShape.BetaRed (proofErase Γ e) left)
    (RF : ProofShape.BetaRed (proofErase Γ f) right) :
    JointCompare Step (proofEraseCtx Γ) true left right := by
  have hcon : ErasedScopedTypedConfluent (fun _ _ _ => False) := by
    intro Γ e T a b hΓ ht RA RB
    obtain ⟨out, HA, HB⟩ := proofErase_beta_confluent hΓ ht (beta_only RA) (beta_only RB)
    exact ⟨out, .beta HA, .beta HB⟩
  have HC := proofErase_scoped_eta_head_forward hcon
    (fun _ _ _ _ H => H.elim) (fun H _ => H.elim) (fun H => H.elim)
    hΓ he hf H (.beta RE) (.beta RF)
  exact HC.joint.mono (fun H => H.elim)

/-- Common-typed head eta supplies every future beta/substitution comparison.
The proof-marker eta case is justified by the original endpoint typings. -/
theorem proofErase_eta_head_family
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : EtaHead (proofErase Γ e) (proofErase Γ f)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ f) := by
  refine ⟨fun RE RF => proofErase_eta_head_beta hΓ he hf H RE RF, ?_⟩
  intro Δ' τ p q W RE RF
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have H' := H.subst (σ := τ)
  rw [← proofErase_subst_with hΓ₀ WS he ES] at RE H'
  rw [← proofErase_subst_with hΓ₀ WS hf ES] at RF H'
  rw [← EΓ₀]
  exact proofErase_eta_head_beta hΓ₀ (he.subst henv WS) (hf.subst henv WS) H' RE RF

/-- Every typed function eta expansion has a future family certificate,
including proof-valued functions whose endpoints erase to the same marker. -/
theorem proofErase_function_eta_family
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  have he := (IsDefEq.eta hf).hasType.1
  rcases proofErase_eta_forward hΓ hf with E | H
  · exact proofErase_beta_join_family hΓ he hf (E ▸ ProofShape.BetaRed.refl) .refl
  · exact proofErase_eta_head_family hΓ he hf H

end Lean4Lean.VEnv.Strengthening
