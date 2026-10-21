import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBetaStrip

/-! # Future-stable family certificates from typed beta joins

A beta join of typed erasures supplies all future beta and interpreted
substitution comparisons. This is a constructive fragment of certification;
no beta transport law for arbitrary joint comparisons is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Two beta paths from one typed erasure have a beta join, obtained by
replaying ordinary typed beta confluence and erasing its residual paths. -/
theorem proofErase_beta_confluent
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.BetaRed (proofErase Γ e) a)
    (S : ProofShape.BetaRed (proofErase Γ e) b) :
    ∃ out, ProofShape.BetaRed a out ∧ ProofShape.BetaRed b out := by
  obtain ⟨eR, RR, ER⟩ := proofErase_beta_replay hΓ ht R
  obtain ⟨eS, RS, ES⟩ := proofErase_beta_replay hΓ ht S
  have hd : PureObservation.Definitions.empty.Deterministic := fun H => H.elim
  obtain ⟨out, HR, HS⟩ := (PureObservation.Compute.of_beta (D := .empty) RR).confluent hd
    (PureObservation.Compute.of_beta (D := .empty) RS)
  exact ⟨proofErase Γ out,
    ER ▸ proofErase_beta_forward hΓ (beta_eq hΓ ht RR).hasType.2 HR.to_beta,
    ES ▸ proofErase_beta_forward hΓ (beta_eq hΓ ht RS).hasType.2 HS.to_beta⟩

private theorem future_join
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ProofShape.BetaRed (proofErase Γ a) shared)
    (RB : ProofShape.BetaRed (proofErase Γ b) shared)
    (PA : ProofShape.BetaRed (proofErase Γ a) p)
    (PB : ProofShape.BetaRed (proofErase Γ b) q) :
    JointCompare Step (proofEraseCtx Γ) true p q := by
  obtain ⟨left, RL, PL⟩ := proofErase_beta_confluent hΓ ha RA PA
  obtain ⟨right, RR, PR⟩ := proofErase_beta_confluent hΓ hb RB PB
  obtain ⟨e, RE, EE⟩ := proofErase_beta_replay hΓ ha RA
  rw [← EE] at RL RR
  obtain ⟨out, LL, LR⟩ := proofErase_beta_confluent hΓ (beta_eq hΓ ha RE).hasType.2 RL RR
  exact .compute (.beta (PL.trans LL)) (.beta (PR.trans LR)) (.leaf .refl)

/-- A typed beta join is a family certificate for any target primitive
relation. It survives every future beta path and interpreted substitution,
including substitutions that create new redexes. -/
theorem proofErase_beta_join_family
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ProofShape.BetaRed (proofErase Γ a) shared)
    (RB : ProofShape.BetaRed (proofErase Γ b) shared) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨fun PA PB => future_join hΓ ha hb RA RB PA PB, ?_⟩
  intro Δ' τ p q W PA PB
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have RA' := RA.subst (σ := τ)
  have RB' := RB.subst (σ := τ)
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at RA' PA
  rw [← proofErase_subst_with hΓ₀ WS hb ES] at RB' PB
  rw [← EΓ₀]
  exact future_join hΓ₀ (ha.subst henv WS) (hb.subst henv WS) RA' RB' PA PB

end Lean4Lean.VEnv.Strengthening
