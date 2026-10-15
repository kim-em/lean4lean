import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Head beta against full joint computation at a later stage

The function and argument may compute independently using arbitrary joint
guards. An exactly recoverable original argument suffices to instantiate the
body path. Computing its images afterwards needs no recovery of the new image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Head beta commutes with finite joint computation of its lambda and argument,
including changing lambda annotations. The join may use a later finite stage.
Only the original non-proof argument needs exact recovery at its assigned type;
there is no recovery requirement for the computed argument, confluence premise,
or arbitrary paired-substitution assumption. -/
theorem proofErase_joint_beta_exchange_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RF : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) argumentOut) :
    ∃ later A' bodyOut, stage ≤ later ∧ functionOut = .lam A' bodyOut ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) := by
  obtain ⟨bodyStage, A', bodyOut, hstage, rfl, _, RB⟩ :=
    proofErase_joint_lam_inv_later heq hs hΓ hA hb hn RF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have RI := proofErase_joint_compute_inst_recoverable heq hs hΓ hx HR hb RB
  have WI : Ctx.LiftN 0 0 (A :: Γ) (A :: Γ) := .zero []
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend
    (erased_joint_stage_descent heq hs bodyStage) hΓA hΓA WI hb rfl
    (by simpa only [ProofShape.liftN_zero] using RB)
  simp only [ProofShape.liftN_zero] at EB
  have RX' := proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at RX'
  refine ⟨imageStage + bodyStage, A', bodyOut, by omega, rfl, ?_, .beta⟩
  exact RI.trans (RX'.mono (erased_joint_stage_mono (by omega)))

end Lean4Lean.VEnv.Strengthening
