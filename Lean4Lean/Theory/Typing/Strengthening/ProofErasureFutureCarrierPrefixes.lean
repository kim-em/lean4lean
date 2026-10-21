import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Certified computation preserves full future carrier certificates

Both endpoint computation and computation of the supplied type retain every
future carrier/endpoint beta path and interpreted substitution. Type computation
is used in the pullback direction: a certificate at the output gives one at the
input. No arbitrary type-conversion or typed-composition law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Certified endpoint prefixes preserve the future certificate at the same
carrier. Endpoint types may differ: only the computation commutation requires
their actual typings, and no intermediate typing conversion is inferred. -/
theorem BetaStableCarrier.certified_prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) C a' b') :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) C (proofErase Γ a) (proofErase Γ b) := by
  have local_prefix {Γ a A b B C a' b' p q C'} (hΓ : OnCtx Γ (env.IsType univs))
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) a')
      (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) b')
      (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) C a' b')
      (RC : ProofShape.BetaRed C C') (PA : ProofShape.BetaRed (proofErase Γ a) p)
      (PB : ProofShape.BetaRed (proofErase Γ b) q) :
      JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) C' p q := by
    obtain ⟨left, BL, CL⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ ha RA PA
    obtain ⟨right, BR, CR⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ hb RB PB
    exact .carrierReduce (CL.mono erased_beta_stable_joint_into_union)
      (CR.mono erased_beta_stable_joint_into_union) (H.1 RC BL BR)
  refine ⟨fun RC PA PB => local_prefix hΓ ha hb RA RB H RC PA PB, ?_⟩
  intro Δ' τ C' p q W RC PA PB
  have RA' := RA.subst (erased_beta_stable_joint_subst heq hs) W
  have RB' := RB.subst (erased_beta_stable_joint_subst heq hs) W
  have H' := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← EΓ₀] at RA'
  rw [← proofErase_subst_with hΓ₀ WS hb ES, ← EΓ₀] at RB'
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at PA
  rw [← proofErase_subst_with hΓ₀ WS hb ES] at PB
  rw [← EΓ₀] at H' ⊢
  exact local_prefix hΓ₀ (ha.subst henv WS) (hb.subst henv WS) RA' RB' H' RC PA PB

/-- Pull back a full future certificate through certified computation of its
supplied carrier. The endpoints need no chosen typed realizations: only the
carrier is replayed to commute its computation with every future beta path. -/
theorem BetaStableCarrier.certified_carrier_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A) B)
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) B a b) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a b := by
  have local_prefix {Γ A u B a b C p q} (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u))
      (R : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A) B)
      (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) B a b)
      (RC : ProofShape.BetaRed (proofErase Γ A) C)
      (PA : ProofShape.BetaRed a p) (PB : ProofShape.BetaRed b q) :
      JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) C p q := by
    obtain ⟨shared, BS, RS⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ hA R RC
    exact .carrierCompute (RS.mono erased_beta_stable_joint_into_union) (H.1 BS PA PB)
  refine ⟨fun RC PA PB => local_prefix hΓ hA R H RC PA PB, ?_⟩
  intro Δ' τ C p q W RC PA PB
  have R' := R.subst (erased_beta_stable_joint_subst heq hs) W
  have H' := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← proofErase_subst_with hΓ₀ WS hA ES, ← EΓ₀] at R'
  rw [← proofErase_subst_with hΓ₀ WS hA ES] at RC
  rw [← EΓ₀] at H' ⊢
  exact local_prefix hΓ₀ (hA.subst henv WS) R' H' RC PA PB

end Lean4Lean.VEnv.Strengthening
