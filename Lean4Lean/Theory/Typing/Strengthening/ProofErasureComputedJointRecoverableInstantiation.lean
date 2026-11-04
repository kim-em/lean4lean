import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointRecoveringPrimitives

/-! # Concrete instantiation by exactly recoverable expressions

Images may be non-proof data or functions. Recovery at their assigned type is
an explicit premise, and its finite stage adds to the body's stage. These laws
do not cover arbitrary converted image types or arbitrary paired substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A typed body computation instantiates at an exactly recoverable image.
Its output is the exact substituted shape, at the sum of the two stage bounds. -/
theorem proofErase_computed_joint_compute_inst_recoverable (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (he : env.HasType univs (P :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have H := R.subst_recovering (erased_computed_joint_stage_descent heq hs stage)
    (erased_computed_joint_stage_rename heq hs imageStage)
    (erased_computed_joint_stage_recovering heq hs imageStage stage)
    hΓP he rfl rfl (RecoveringSubstitution.inst hΓ hp HR)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero he]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Exact image recovery preserves the entire selected body recovery output,
not merely its outer head. No domain re-synthesis premise is used. -/
theorem proofErase_computed_joint_recovery_inst_recoverable (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (he : env.HasType univs (P :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedComputedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedTypeRecovery (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have H := R.subst_recovering (erased_computed_joint_stage_descent heq hs stage)
    (erased_computed_joint_stage_rename heq hs imageStage)
    (erased_computed_joint_stage_mono (Nat.le_add_right imageStage stage))
    (erased_computed_joint_stage_recovering heq hs imageStage stage)
    hΓP he rfl rfl (RecoveringSubstitution.inst hΓ hp HR)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero he]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Either comparison mode instantiates diagonally at an exactly recoverable
argument, including non-proof lambda arguments. -/
theorem proofErase_computed_joint_compare_inst_recoverable (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedComputedJointStage D stage) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have H' := H.subst_recovering (erased_computed_joint_stage_descent heq hs stage)
    (erased_computed_joint_stage_rename heq hs imageStage)
    (erased_computed_joint_stage_mono (Nat.le_add_right imageStage stage))
    (erased_computed_joint_stage_recovering heq hs imageStage stage)
    hΓP ha hb rfl rfl rfl (RecoveringSubstitution.inst hΓ hp HR)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha, proofErase_instN hΓP hp Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

/-- Explicit carriers and both endpoints instantiate together at the same
additive stage bound, through all recursive field and function guards. -/
theorem proofErase_computed_joint_carrier_inst_recoverable (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCarrierGuard (ErasedComputedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) A) (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (A.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  obtain ⟨v, hA⟩ := ha.isType henv hΓP
  have H' := H.subst_recovering (erased_computed_joint_stage_descent heq hs stage)
    (erased_computed_joint_stage_rename heq hs imageStage)
    (erased_computed_joint_stage_mono (Nat.le_add_right imageStage stage))
    (erased_computed_joint_stage_recovering heq hs imageStage stage)
    hΓP ha hb rfl rfl rfl rfl (RecoveringSubstitution.inst hΓ hp HR)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero hA, proofErase_instN hΓP hp Ctx.InstN.zero ha,
    proofErase_instN hΓP hp Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

/-- A displayed beta redex followed by a body computation has an exact joint
path at the additive stage bound, provided its non-proof argument recovers its
assigned domain. This is diagonal beta transport, not paired instantiation. -/
theorem proofErase_computed_joint_beta_compute_recoverable (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort u))
    (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (he : env.HasType univs (P :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam P e) p)) (out.inst (proofErase Γ p)) := by
  have RB := proofErase_beta_forward hΓ (HasType.app (HasType.lam hP he) hp) BetaRed.beta
  exact (ScopedCompute.beta RB).trans
    (proofErase_computed_joint_compute_inst_recoverable heq hs hΓ hp HR he R)

end Lean4Lean.VEnv.Strengthening
