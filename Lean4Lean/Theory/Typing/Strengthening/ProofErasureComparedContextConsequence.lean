import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedContextBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction

/-! # Full type-endpoint computation forced by compared recovery transport

At the joint union, permitting a new selected output after a compared binder
change still entails transport of type comparisons across arbitrary finite
computation. Exactly recovered proposition-producing functions remove the
auxiliary binder from the boundary argument, retaining an actual certificate
in the original context. This is a necessary consequence, not a proof of the
transport law or an equivalence with the proposition front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private compute_above
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedContextBoundary
variable [Params]

/-- Compared-context variable recovery at the full union forces inferred type
comparison to survive every finite computation of the right endpoint in the
original context. An arbitrary later stage is allowed. Thus stage growth does
not remove the endpoint-computation obligation hidden in that invariant. -/
theorem JointVariableRecoveryContextComparison.union_type_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hctx : JointVariableRecoveryContextComparison (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort u))
    (H : JointCompare (ErasedJointStage D compareStage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b))
    (R : ScopedCompute (ErasedJointStage D computeStage) (proofEraseCtx Γ)
      (proofErase Γ b) out) :
    ∃ later, compareStage ≤ later ∧ computeStage ≤ later ∧
      JointCompare (ErasedJointStage D later) (proofEraseCtx Γ) false (proofErase Γ a) out := by
  have HC := compute_above (erased_joint_union_descent heq hs) (@erased_joint_union_head _ D)
    (erased_joint_union_rename heq hs) Hctx hΓ ha hb
    ((JointCompare.common H).mono (fun H => ⟨compareStage, H⟩))
    (R.mono (fun R => ⟨computeStage, R⟩))
  obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
  obtain ⟨b', Hb, Eb⟩ := proofErase_scoped_compute_realize
    (erased_joint_stage_descent heq hs computeStage) hΓ hb rfl rfl R
  rw [← Eb] at HC
  have HC' := proofErase_joint_compare_drop_prop_function heq hs hΓ ha ha Hb.hasType.2 HC
  have HI := proofErase_joint_types_inferred (erased_joint_stage_descent heq hs stage)
    hΓ ha Hb.hasType.2 HC'
  rw [Eb] at HI
  refine ⟨max stage (max compareStage computeStage), by omega, by omega, ?_⟩
  exact HI.mono (erased_joint_stage_mono (by omega))

end Lean4Lean.VEnv.Strengthening
