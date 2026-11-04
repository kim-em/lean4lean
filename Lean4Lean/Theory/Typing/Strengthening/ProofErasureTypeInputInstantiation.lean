import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage

/-! # Recursive instantiation through callable elimination trees

The finite tree remains available after retained projections and type-input calls.
It therefore supports arbitrary typed body comparisons rather than requiring
a predetermined projection path or an exact native type for the image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Callable-tree images instantiate the entire finite stage-zero checker
at any actual assigned type, retaining the comparison mode and endpoints. -/
theorem proofErase_computed_joint_zero_compare_inst_typeInput
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (HI : TypeInputImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs hΓ hp
    (StructuralFamilyRecovery.typeInput (cut := 0) HI) ha hb H

/-- Every first-layer computation survives the same instantiation with its
exact substituted result and all recursively checked guards. -/
theorem proofErase_computed_joint_one_compute_inst_typeInput
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HI : TypeInputImage Γ p)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs hΓ hp
    (StructuralFamilyRecovery.typeInput (cut := 0) HI) ht R

end Lean4Lean.VEnv.Strengthening
