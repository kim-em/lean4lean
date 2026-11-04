import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralEtaInstantiation

/-! # Structural eta-domain instantiation with a dependent inner codomain

The eta-converted domain discrepancy persists in arbitrary typed dependent
function carriers. The new recovery leaf supplies full body substitution and
first-layer computation transport for these images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned assignedRaw context_wf types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

private def dependentImage (C : VExpr) : VExpr := .lam (.forallE native C) (.sort .zero)
private def dependentType (C : VExpr) : VExpr := .forallE (.forallE assigned C) (.sort (.succ .zero))

private theorem image_typed
    (hC : env.HasType univs (assigned :: context Γ) C (.sort v)) :
    env.HasType univs (context Γ) (dependentImage C) (dependentType C) := by
  have HXY := IsDefEq.forallEDF types_equal hC
  exact (IsDefEq.forallEDF HXY.symm (HasType.sort (by trivial))).defeq
    (HasType.lam HXY.hasType.2 (HasType.sort (by trivial)))

private theorem image_path (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs (assigned :: context Γ) C (.sort v)) :
    StructuralFamilyRecovery D 0 (context Γ) (dependentImage C)
      (proofErase (context Γ) (dependentType C)) 0 := by
  have HA : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  exact StructuralFamilyRecovery.of_dependent_structural (context_wf hΓ) (image_typed hC) HA .refl

/-- The structural eta-domain image with any typed dependent inner codomain
instantiates every common-typed recursive body comparison at stage zero. -/
theorem proofErase_computed_joint_dependent_structural_eta_body_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs (assigned :: context Γ) C (.sort v))
    (ha : env.HasType univs (dependentType C :: context Γ) a T)
    (hb : env.HasType univs (dependentType C :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (dependentType C :: context Γ)) mode
      (proofErase (dependentType C :: context Γ) a) (proofErase (dependentType C :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst (dependentImage C)))
      (proofErase (context Γ) (b.inst (dependentImage C))) :=
  proofErase_computed_joint_zero_compare_inst_structural hs (context_wf hΓ) (image_typed hC)
    (image_path hΓ hC) ha hb H

/-- Dependent structural eta-domain images also instantiate all first-layer
computations with finite recursive guards, retaining the exact output. -/
theorem proofErase_computed_joint_dependent_structural_eta_firstStage_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs (assigned :: context Γ) C (.sort v))
    (he : env.HasType univs (dependentType C :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (dependentType C :: context Γ))
      (proofErase (dependentType C :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst (dependentImage C)))
      (out.inst (proofErase (context Γ) (dependentImage C))) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs (context_wf hΓ) (image_typed hC)
    (image_path hΓ hC) he R

end Lean4Lean.VEnv.Strengthening
