import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedBodyInstantiation

/-! # Recursive instantiation through dependent generic-value family inputs

The dependent input laws preserve certificates through substitution and prove
whole-carrier readout at every finite level. The existing structural recovery
route therefore admits these domains without changing its checker induction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An image beta-exposing a lambda with an input whose finite family certificate may return generic values and a finite body path
instantiates every common-typed recursive comparison. The result type E has
no shape restriction; no target comparison is assumed for future bodies. -/
theorem proofErase_computed_joint_zero_compare_inst_valueFamily
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S B (.sort u))
    (HBdom : NativeFamilyFramework.ValueRanked rank Γ B)
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam B body))
    (HB : StructuralFamilyRecovery D 1 (B :: Γ) body
      (proofErase (B :: Γ) E) n)
    (ha : env.HasType univs (.forallE S E :: Γ) a T)
    (hb : env.HasType univs (.forallE S E :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE S E :: Γ)) mode
      (proofErase (.forallE S E :: Γ) a)
      (proofErase (.forallE S E :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP (.valueFamily HE HBdom) HB ha hb H

/-- The same converted family-input body path supports all first-layer
computations with recursive guards and the exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_valueFamily
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S B (.sort u))
    (HBdom : NativeFamilyFramework.ValueRanked rank Γ B)
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam B body))
    (HB : StructuralFamilyRecovery D 1 (B :: Γ) body
      (proofErase (B :: Γ) E) n)
    (he : env.HasType univs (.forallE S E :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE S E :: Γ))
      (proofErase (.forallE S E :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP (.valueFamily HE HBdom) HB he R


end Lean4Lean.VEnv.Strengthening
