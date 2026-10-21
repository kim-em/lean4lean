import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Certified computation before a future family comparison

The residual comparison may be eta or another certified relation rather than
literal equality. Computation/beta commutation retains the original future
certificate and allows this construction to iterate without endpoint transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem future_prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ) a' b')
    (PA : ProofShape.BetaRed (proofErase Γ a) p)
    (PB : ProofShape.BetaRed (proofErase Γ b) q) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true p q := by
  obtain ⟨left, BL, CL⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ ha RA PA
  obtain ⟨right, BR, CR⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ hb RB PB
  exact .compute (CL.mono erased_beta_stable_joint_into_union)
    (CR.mono erased_beta_stable_joint_into_union) (H.1 BL BR)

/-- Prefixing a future family certificate by two certified computations gives
another future certificate. The residual endpoints need not be equal or have
a computational join; their stored comparisons handle every future residual. -/
theorem BetaStableFamily.certified_prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ) a' b') :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨fun PA PB => future_prefixes heq hs hΓ ha hb RA RB H PA PB, ?_⟩
  intro Δ' τ p q W PA PB
  have RA' := RA.subst (erased_beta_stable_joint_subst heq hs) W
  have RB' := RB.subst (erased_beta_stable_joint_subst heq hs) W
  have H' := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← EΓ₀] at RA'
  rw [← proofErase_subst_with hΓ₀ WS hb ES, ← EΓ₀] at RB'
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at PA
  rw [← proofErase_subst_with hΓ₀ WS hb ES] at PB
  rw [← EΓ₀] at H' ⊢
  exact future_prefixes heq hs hΓ₀ (ha.subst henv WS) (hb.subst henv WS) RA' RB' H' PA PB

end Lean4Lean.VEnv.Strengthening
