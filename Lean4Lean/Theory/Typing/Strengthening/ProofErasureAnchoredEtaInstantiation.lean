import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointAnchoredSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedDomainEtaBoundary

/-! # Full body substitution at the eta-converted lambda boundary

The function is the lambda used by SelectedDomainEtaBoundary: its written
domain and assigned domain are distinct neutral normal forms related by eta.
Its exact recovery/exposure failure does not prevent this recursive transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned assignedRaw context_wf native_typed
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

/-- The concrete lambda with eta-converted assigned domain transports every
common-typed body comparison at stage zero, including nested carrier and
computed-domain checks. The boundary theorem still rules out exact native
recovery, sort-rooted recovery, and lambda exposure at that assigned domain.
This statement concerns shared-argument substitution, not arbitrary beta stability. -/
theorem proofErase_computed_joint_eta_assigned_lambda_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (.forallE (assigned) (.sort (.succ .zero)) :: context Γ) a A)
    (hb : env.HasType univs (.forallE (assigned) (.sort (.succ .zero)) :: context Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE (assigned) (.sort (.succ .zero)) :: context Γ)) mode
      (proofErase (.forallE (assigned) (.sort (.succ .zero)) :: context Γ) a)
      (proofErase (.forallE (assigned) (.sort (.succ .zero)) :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst (.lam native (.sort .zero))))
      (proofErase (context Γ) (b.inst (.lam native (.sort .zero)))) := by
  have hC := context_wf hΓ
  have ht : env.HasType univs (context Γ) (.lam native (.sort .zero))
      (.forallE assigned (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))).defeq
      (HasType.lam native_typed (HasType.sort (by trivial)))
  have HC : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  exact proofErase_computed_joint_zero_compare_inst_neutralFamily hs hC ht HC ha hb H

end Lean4Lean.VEnv.Strengthening
