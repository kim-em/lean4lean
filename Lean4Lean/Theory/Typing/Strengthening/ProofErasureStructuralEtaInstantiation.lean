import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary

/-! # Recursive substitution at the structural eta-domain obstruction

The concrete lambda excluded by the previous three-way recovery invariant
now instantiates arbitrary typed stage-zero body comparisons and first-layer
computations. This consumes the recursive transport theorem, not just one
application repair.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned assignedRaw context_wf native_typed
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

private def structuralImage : VExpr := .lam (.forallE native (.sort .zero)) (.sort .zero)
private def structuralType : VExpr := .forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))

private theorem image_typed : env.HasType univs (context Γ) structuralImage structuralType := by
  have hX := HasType.forallE (Γ := context Γ) native_typed (HasType.sort (l := .zero) (by trivial))
  have hXY := IsDefEq.forallEDF (Γ := context Γ) types_equal.symm (HasType.sort (l := .zero) (by trivial))
  exact (IsDefEq.forallEDF hXY (HasType.sort (by trivial))).defeq
    (HasType.lam hX (HasType.sort (by trivial)))

private theorem image_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 0 (context Γ) structuralImage (proofErase (context Γ) structuralType) 0 := by
  have HA : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  exact StructuralFamilyRecovery.of_structural (context_wf hΓ) image_typed HA .refl

/-- The Pi-wrapped eta-domain witness substitutes into every common-typed
stage-zero recursive body comparison, including nested carrier checking.
Its failure of old native/anchored recovery is not used as an assumption. -/
theorem proofErase_computed_joint_structural_eta_body_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (structuralType :: context Γ) a T)
    (hb : env.HasType univs (structuralType :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (structuralType :: context Γ)) mode
      (proofErase (structuralType :: context Γ) a) (proofErase (structuralType :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst structuralImage))
      (proofErase (context Γ) (b.inst structuralImage)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs (context_wf hΓ) image_typed
    (image_path hΓ) ha hb H

/-- The same previously excluded structural eta-domain witness instantiates
all first-layer computations with finite recursive stage-zero guards,
preserving both the layer and the exact substituted output. -/
theorem proofErase_computed_joint_structural_eta_firstStage_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (structuralType :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (structuralType :: context Γ))
      (proofErase (structuralType :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst structuralImage))
      (out.inst (proofErase (context Γ) structuralImage)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs (context_wf hΓ) image_typed
    (image_path hΓ) he R

end Lean4Lean.VEnv.Strengthening
