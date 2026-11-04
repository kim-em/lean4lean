import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointFirstStageSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedDomainEtaBoundary

/-! # First-layer computation at the eta-converted lambda boundary

The lambda whose exact assigned-domain recovery fails nevertheless substitutes
through actual singleton and Eq computations, using protected neutral carriers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned context_wf native_typed types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

/-- Every typed first-layer computation may be instantiated by the concrete
eta-assigned lambda from the recovery boundary. Its exact substituted target
and stage are retained, despite failure of exact domain exposure. -/
theorem proofErase_computed_joint_one_eta_assigned_lambda_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (.forallE assigned (.sort (.succ .zero)) :: context Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE assigned (.sort (.succ .zero)) :: context Γ))
      (proofErase (.forallE assigned (.sort (.succ .zero)) :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst (.lam native (.sort .zero))))
      (out.inst (proofErase (context Γ) (.lam native (.sort .zero)))) := by
  have hC := context_wf hΓ
  have ht : env.HasType univs (context Γ) (.lam native (.sort .zero))
      (.forallE assigned (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))).defeq
      (HasType.lam native_typed (HasType.sort (by trivial)))
  have HC : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  exact proofErase_computed_joint_one_compute_inst_neutralFamily heq hs hC ht HC he R

end Lean4Lean.VEnv.Strengthening
