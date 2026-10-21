import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Future-stable certificates from certified computational joins

A shared output need not be beta-normal or reached by beta alone. Certified
computation commutes with future beta paths, and beta confluence at the typed
shared output joins the resulting residuals. Substitution retains this proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem future_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) shared)
    (PA : ProofShape.BetaRed (proofErase Γ a) p)
    (PB : ProofShape.BetaRed (proofErase Γ b) q) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true p q := by
  obtain ⟨left, BL, CL⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ ha RA PA
  obtain ⟨right, BR, CR⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ hb RB PB
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓ ha rfl rfl RA
  rw [← EE] at BL BR
  obtain ⟨out, LL, LR⟩ := proofErase_beta_confluent hΓ HE.hasType.2 BL BR
  exact .compute ((CL.trans (.beta LL)).mono erased_beta_stable_joint_into_union)
    ((CR.trans (.beta LR)).mono erased_beta_stable_joint_into_union) (.leaf .refl)

/-- Certified computational joins supply all future beta/substitution family
comparisons in the union. Neither confluence of arbitrary joint computation
nor normalization of the common output is required. -/
theorem proofErase_certified_join_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨fun PA PB => future_join heq hs hΓ ha hb RA RB PA PB, ?_⟩
  intro Δ' τ p q W PA PB
  have RA' := RA.subst (erased_beta_stable_joint_subst heq hs) W
  have RB' := RB.subst (erased_beta_stable_joint_subst heq hs) W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← EΓ₀] at RA'
  rw [← proofErase_subst_with hΓ₀ WS hb ES, ← EΓ₀] at RB'
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at PA
  rw [← proofErase_subst_with hΓ₀ WS hb ES] at PB
  rw [← EΓ₀]
  exact future_join heq hs hΓ₀ (ha.subst henv WS) (hb.subst henv WS) RA' RB' PA PB

end Lean4Lean.VEnv.Strengthening
