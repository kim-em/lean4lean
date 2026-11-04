import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedRecoverableInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedStructuralEtaInstantiation

/-! # Structural eta image substitution at every finite computed stage

The witness recovers at its written type at stage zero. Conversion to that type
therefore allows instantiation without increasing the body computation stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned context_wf native_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private image_conversion erase_pi_sort
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedStructuralEtaInstantiation
variable [Params]

private theorem native_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedComputedJointStage D 0) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero)))
      (proofErase (context Γ) (.forallE (.forallE native (.sort .zero)) (.sort (.succ .zero)))) := by
  have hC := context_wf hΓ
  have hX := HasType.forallE (Γ := context Γ) native_typed (HasType.sort (l := .zero) (by trivial))
  have hp := HasType.lam hX (HasType.sort (l := .zero) (by trivial))
  have hCX : OnCtx (.forallE native (.sort .zero) :: context Γ) (env.IsType univs) := ⟨hC, _, hX⟩
  rw [show proofErase (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hC hp),
    show proofErase (.forallE native (.sort .zero) :: context Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hCX (HasType.sort (by trivial))),
    erase_pi_sort hC hX (by trivial)]
  exact .lam (.sort (by trivial))

/-- The structural eta lambda instantiates complete body comparisons at every
finite computed stage without increasing that stage. Recovery is used only at
its written type, after the whole body has changed binder context. -/
theorem proofErase_computed_joint_structural_eta_lambda_inst_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) a A)
    (hb : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) b A)
    (H : ComputedJointCompare (ErasedComputedJointStage D stage)
      (proofEraseCtx (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ)) mode
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) a)
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) b)) :
    ComputedJointCompare (ErasedComputedJointStage D stage) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst (.lam (.forallE native (.sort .zero)) (.sort .zero))))
      (proofErase (context Γ) (b.inst (.lam (.forallE native (.sort .zero)) (.sort .zero)))) := by
  obtain ⟨_, HTU, HT, hp, _⟩ := image_conversion (D := D) hΓ
  simpa only [Nat.zero_add] using
    proofErase_computed_joint_compare_inst_converted_recoverable heq hs (context_wf hΓ)
      HTU HT hp (fun _ => native_recovery (D := D) hΓ) ha hb H

/-- The same witness instantiates computations with their exact output at any
finite stage, including arbitrarily nested singleton and Eq guards. -/
theorem proofErase_computed_joint_structural_eta_compute_inst_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs
      (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D stage)
      (proofEraseCtx (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ))
      (proofErase (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)) :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst (.lam (.forallE native (.sort .zero)) (.sort .zero))))
      (out.inst (proofErase (context Γ) (.lam (.forallE native (.sort .zero)) (.sort .zero)))) := by
  obtain ⟨_, HTU, HT, hp, _⟩ := image_conversion (D := D) hΓ
  simpa only [Nat.zero_add] using
    proofErase_computed_joint_compute_inst_converted_recoverable heq hs (context_wf hΓ)
      HTU HT hp (fun _ => native_recovery (D := D) hΓ) he R

end Lean4Lean.VEnv.Strengthening
