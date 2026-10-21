import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStablePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitutableParallelStrip
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelPrimitiveResidual

/-! # The remaining local certificate for source-stage parallel commutation

The target primitive carries all future typed substitutions. Once primitive
beta squares produce that certificate, the compatible-path theorem handles
the application case without reapplying beta stability to target paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Missing local obligation at nonzero stages: every typed primitive parallel
beta square has a residual primitive stable under all typed substitutions.
This includes more than an ordinary union residual, and no general proof for
singleton or specialized Eq roots is asserted here. -/
def JointStageStableParallelResidual (D : PureObservation.Definitions) (stage : Nat) : Prop :=
  ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ErasedJointStage D stage (proofEraseCtx Γ) (proofErase Γ e) out →
    BetaPar (proofErase Γ e) reduced →
    ∃ shared, BetaPar out shared ∧
      SubstitutionStablePrimitive (ErasedJointUnion D) (proofEraseCtx Γ) reduced shared

/-- Ordinary core primitives have substitution-stable parallel residuals
syntactically. This closes the computation base stage without proposition
beta stability, canonical Eq, or declaration soundness. -/
theorem joint_zero_stable_parallel_residual : JointStageStableParallelResidual D 0 := by
  intro Γ e T out reduced _ _ H P
  obtain ⟨shared, PB, HR⟩ := erased_iota_primitive_parallel_beta_residual H P
  exact ⟨shared, PB, ⟨0, HR⟩, fun _ => ⟨0, erased_iota_primitive_subst HR⟩⟩

/-- Stable primitive residuals lift to full stage-indexed paths with one
parallel output residual. The produced path still carries substitution
certificates, so its body segments can be instantiated without a new global
stability premise. The local nonzero-stage obligation remains explicit. -/
theorem proofErase_joint_stable_parallel_beta_strip
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hres : JointStageStableParallelResidual D stage)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (SubstitutionStablePrimitive (ErasedJointUnion D))
        (proofEraseCtx Γ) reduced shared := by
  apply proofErase_scoped_parallel_beta_strip_to (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_head stage)
    (substitution_stable_primitive_descent (erased_joint_union_descent heq hs))
    (fun H => erased_joint_union_head H.1) SubstitutionStablePrimitive.subst ?_ hΓ ht R P
  intro Γ e T out reduced hΓ ht H P
  obtain ⟨shared, PB, HR⟩ := Hres hΓ ht H P
  exact ⟨shared, PB, .base HR⟩

end Lean4Lean.VEnv.Strengthening
