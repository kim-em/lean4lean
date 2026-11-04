import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointUnion

/-! # Instantiation at a beta-expanded assigned universe

The image `Prop` is typed at a beta-expanded `Type`. Native recovery, even in
the full computed union, cannot produce that expanded assigned type. Terminal
typing nevertheless instantiates every recursive body certificate and every
first-layer computation at that binder.
-/
namespace Lean4Lean.VEnv.Strengthening.ExpandedSortInstantiation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A beta-expanded `Type`, used as an actual binder annotation. -/
def assigned : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero)

private theorem assigned_eq : env.IsDefEq univs Γ assigned (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  IsDefEq.beta (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem image_typed : env.HasType univs Γ (.sort .zero) assigned :=
  assigned_eq.symm.defeq (HasType.sort (by trivial))

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ assigned =
      .app (.lam (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero) ∧
    proofErase Γ (.sort .zero) = .sort .zero := by
  have hU : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have hbody : env.HasType univs (.sort (.succ .zero) :: Γ)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hlam := HasType.lam hU hbody
  have hnlam := not_isProof_function_to_sort hΓ hlam
  have hp : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  constructor
  · rw [show proofErase Γ assigned = .app _ _ from
      if_neg (not_isProof_of_sort hΓ assigned_eq.hasType.1)]
    simp only [proofErase, if_neg hnlam, if_neg (not_isProof_of_sort hΓ hU),
      if_neg (not_isProof_of_sort hΓU hbody), if_neg (not_isProof_of_sort hΓ hp)]
  · exact if_neg (not_isProof_of_sort hΓ hp)

/-- The assigned type is a genuine typed recovery gap even for all computed
stages together, while the image has an unconditional terminal certificate. -/
theorem typed_assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs Γ (.sort .zero) assigned ∧ TerminalImage Γ (.sort .zero) ∧
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.sort .zero)) (proofErase Γ assigned) := by
  refine ⟨image_typed, .type (HasType.sort (by trivial)), ?_⟩
  intro R
  rw [(erasures hΓ).1, (erasures hΓ).2] at R
  cases R.sort_compute.sort_fixed erased_computed_joint_union_head

/-- Every common-typed recursive body comparison instantiates at the expanded
binder despite the exact assigned-recovery failure. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a A)
    (hb : env.HasType univs (assigned :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst (.sort .zero))) (proofErase Γ (b.inst (.sort .zero))) :=
  proofErase_computed_joint_zero_compare_inst_terminal hs hΓ image_typed
    (.type (HasType.sort (by trivial))) ha hb H

/-- The same image retains exact outputs throughout first-layer computation. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst (.sort .zero))) (out.inst (proofErase Γ (.sort .zero))) :=
  proofErase_computed_joint_one_compute_inst_terminal heq hs hΓ image_typed
    (.type (HasType.sort (by trivial))) ht R

end Lean4Lean.VEnv.Strengthening.ExpandedSortInstantiation
