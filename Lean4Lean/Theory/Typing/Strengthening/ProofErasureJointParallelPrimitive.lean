import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointParallelSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelPrimitiveResidual

/-! # Parallel beta residuals for every primitive of the joint union

The ordinary branch is syntactic. General singleton guards use proposition
beta stability, and specialized Eq uses its general singleton presentation.
Thus every typed primitive/beta peak has one primitive on its residual side
and one parallel beta step on its output side. Compatible-path commutation remains separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Under proposition beta stability, any parallel beta development competing with
one typed joint primitive has an exact primitive residual. The old primitive
output beta reduces to the residual output. This covers every primitive branch
without confluence, pattern-completeness, or an additional guard-stability law. -/
theorem proofErase_joint_primitive_parallel_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ErasedJointUnion D (proofEraseCtx Γ) (proofErase Γ e) out)
    (RB : ProofShape.BetaPar (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaPar out shared ∧
      ErasedJointUnion D (proofEraseCtx Γ) reduced shared := by
  rcases erased_joint_union_iff.1 H with H | H | H
  · obtain ⟨shared, R, H⟩ := erased_iota_primitive_parallel_beta_residual H RB
    exact ⟨shared, R, erased_joint_union_iff.2 (.inl H)⟩
  · obtain ⟨shared, R, H⟩ := proofErase_joint_singleton_parallel_beta_residual heq hs Hbeta H RB
    exact ⟨shared, R, erased_joint_union_iff.2 (.inr (.inl H))⟩
  · obtain ⟨shared, R, H⟩ := proofErase_joint_prefix_parallel_beta_residual heq hs hregistry Hbeta hΓ ht H RB
    exact ⟨shared, R, erased_joint_union_iff.2 (.inr (.inl H))⟩

end Lean4Lean.VEnv.Strengthening
