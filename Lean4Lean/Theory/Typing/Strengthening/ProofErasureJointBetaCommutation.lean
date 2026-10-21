import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointParallelStrip

/-! # Full joint computation commutes with arbitrary finite beta paths

Serialize the beta path into parallel developments, preserving typed original
intermediates. The parallel strip theorem moves each development past the
current joint path; its single-step output residuals compose into beta.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private Compute.toParallel parallel_toCompute
  from Lean4Lean.Theory.Typing.Strengthening.DeclarationConfluence
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Under proposition beta stability, every full joint path from a typed source
commutes with every finite raw beta path. The joint output reaches a common
term using beta alone; the beta output reaches it by actual joint computation.
This is not confluence of two arbitrary joint paths. -/
theorem proofErase_joint_beta_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) reduced shared := by
  obtain ⟨eB, RB, EB⟩ := proofErase_beta_replay hΓ ht B
  have transport {e'} (P : ReflTransGen (ComputePar .empty) e e') :
      ∃ shared, ProofShape.BetaRed out shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e') shared := by
    induction P with
    | rfl => exact ⟨out, .refl, R⟩
    | tail initial step ih =>
      obtain ⟨middle, BM, RM⟩ := ih
      have hmid := (beta_eq hΓ ht (parallel_toCompute initial).to_beta).hasType.2
      have PB := proofErase_parallel_beta_forward hΓ hmid step
      obtain ⟨shared, PS, RS⟩ := proofErase_joint_parallel_beta_strip heq hs hregistry Hbeta
        hΓ hmid RM PB
      exact ⟨shared, BM.trans PS.toBeta, RS⟩
  obtain ⟨shared, BS, RS⟩ := transport (Compute.toParallel (Compute.of_beta (D := .empty) RB))
  exact ⟨shared, BS, EB ▸ RS⟩

/-- Finite-stage input computation has a finite later-stage beta residual,
with the exact original endpoints and no recovery premise on any argument. -/
theorem proofErase_joint_beta_commute_later
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ later shared, stage ≤ later ∧ ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ) reduced shared := by
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_beta_commute heq hs hregistry Hbeta
    hΓ ht (R.mono (fun H => ⟨stage, H⟩)) B
  obtain ⟨later, RS⟩ := RS.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, shared, Nat.le_max_left _ _, BS,
    RS.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

end Lean4Lean.VEnv.Strengthening
