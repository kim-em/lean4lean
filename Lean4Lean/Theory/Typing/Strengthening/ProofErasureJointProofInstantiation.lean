import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRetainedPrimitives

/-! # Proof-argument substitution in the concrete joint stages

Proof arguments all erase to the same marker. Retained-variable transport
therefore instantiates computations, selected recovered types, comparisons,
and explicit carriers without assuming general domain re-synthesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A joint computation of a typed body instantiates at any proof argument,
with its exact substituted endpoint and the original finite stage. -/
theorem proofErase_joint_compute_inst_proof (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (he : env.HasType univs (P :: Γ) e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst .proof) := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have H := R.rename_retained (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_retained heq hs stage) hΓP he rfl rfl (RetainedRenaming.proof_inst hΓ hP hp)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero he, proofErase_eq_proof.2 ⟨P, hp, hP⟩]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Proof substitution preserves the selected recovered type exactly. The
proof marker itself is never required to have a recovery derivation. -/
theorem proofErase_joint_recovery_inst_proof (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (he : env.HasType univs (P :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst .proof) := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have H := R.rename_retained (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_retained heq hs stage) hΓP he rfl rfl (RetainedRenaming.proof_inst hΓ hP hp)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero he, proofErase_eq_proof.2 ⟨P, hp, hP⟩]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Compared typed bodies instantiate at two independently supplied proofs of
the same proposition. Both comparison modes and the finite stage are retained. -/
theorem proofErase_joint_compare_inst_proofs (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst q)) := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have H' := H.rename_retained (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_retained heq hs stage) hΓP ha hb rfl rfl rfl (RetainedRenaming.proof_inst hΓ hP hp)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha, proofErase_instN hΓP hq Ctx.InstN.zero hb,
    proofErase_eq_proof.2 ⟨P, hp, hP⟩, proofErase_eq_proof.2 ⟨P, hq, hP⟩]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

/-- Explicit carrier certificates also instantiate at independent proof
arguments. The chosen lower carrier is the first substituted carrier. -/
theorem proofErase_joint_carrier_inst_proofs (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) A) (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (A.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst q)) := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  obtain ⟨u, hA⟩ := ha.isType henv hΓP
  have H' := H.rename_retained (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_retained heq hs stage) hΓP ha hb rfl rfl rfl rfl (RetainedRenaming.proof_inst hΓ hP hp)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero hA, proofErase_instN hΓP hp Ctx.InstN.zero ha,
    proofErase_instN hΓP hq Ctx.InstN.zero hb, proofErase_eq_proof.2 ⟨P, hp, hP⟩,
    proofErase_eq_proof.2 ⟨P, hq, hP⟩]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

end Lean4Lean.VEnv.Strengthening
