import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPrimitiveRenaming

/-! # Same-stage weakening of the concrete joint checker

These results apply to every sound core, including the quotient repair. They
preserve the selected recovery output and every finite stage across insertion
of an arbitrary block, without domain re-synthesis or inverse weakening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private ProofShape.subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Every concrete joint computation weakens at its original finite stage. -/
theorem proofErase_joint_compute_weakN (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ProofShape.ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (e.liftN n k)) (out.liftN n k) := by
  rw [proofErase_liftN hΓ hΓ' W ht]
  simpa only [ProofShape.subst_bvar_liftN] using
    R.rename (erased_joint_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)

/-- Selected recovery types are preserved exactly by actual binder insertion,
including the domain and codomain of a recovered Pi. No re-synthesis is needed. -/
theorem proofErase_joint_recovery_weakN (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ProofShape.ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (e.liftN n k)) (out.liftN n k) := by
  rw [proofErase_liftN hΓ hΓ' W ht]
  simpa only [ProofShape.subst_bvar_liftN] using
    R.rename (erased_joint_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)

/-- Both comparison modes weaken at the same finite stage; the supplied
endpoint typings may be independent. -/
theorem proofErase_joint_compare_weakN (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ') mode
      (proofErase Γ' (a.liftN n k)) (proofErase Γ' (b.liftN n k)) := by
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb]
  simpa only [ProofShape.JointCheckKind.subst, ProofShape.subst_bvar_liftN] using
    H.rename (erased_joint_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)

/-- Explicit carrier checking weakens with its actual carrier and endpoints,
without changing the finite stage or assuming arbitrary substitution closure. -/
theorem proofErase_joint_carrier_weakN (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (A.liftN n k)) (proofErase Γ' (a.liftN n k)) (proofErase Γ' (b.liftN n k)) := by
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  rw [proofErase_liftN hΓ hΓ' W hA, proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb]
  simpa only [ProofShape.JointCheckKind.subst, ProofShape.subst_bvar_liftN] using
    H.rename (erased_joint_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)

end Lean4Lean.VEnv.Strengthening
