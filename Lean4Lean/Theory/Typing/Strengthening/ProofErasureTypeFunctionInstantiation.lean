import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedBodyInstantiation

/-! # Instantiation through converted type-valued function inputs

The selected input may be any actual type equal to a function into a universe.
Its input binder is terminal; source carrier computations and changed codomains
are handled by the full guard conversion theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An image beta-exposing a lambda with a dependent type-family input and a finite body path
instantiates every common-typed recursive comparison. The result type E has
no shape restriction; no target comparison is assumed for future bodies. -/
theorem proofErase_computed_joint_zero_compare_inst_typeFamily
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S B (.sort u))
    (HBdom : TerminalTypeFamily Γ B)
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
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP (.typeFamily HE HBdom) HB ha hb H

/-- The same converted family-input body path supports all first-layer
computations with recursive guards and the exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_typeFamily
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S B (.sort u))
    (HBdom : TerminalTypeFamily Γ B)
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
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP (.typeFamily HE HBdom) HB he R


/-- An image beta-exposing a lambda with a type-valued function input and a finite body path
instantiates every common-typed recursive comparison. The result type E has
no shape restriction; no target comparison is assumed for future bodies. -/
theorem proofErase_computed_joint_zero_compare_inst_typeFunction
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S (.forallE B (.sort v)) (.sort u))
    (HBdom : TerminalDomain Γ B)
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam (.forallE B (.sort v)) body))
    (HB : StructuralFamilyRecovery D 1 (.forallE B (.sort v) :: Γ) body
      (proofErase (.forallE B (.sort v) :: Γ) E) n)
    (ha : env.HasType univs (.forallE S E :: Γ) a T)
    (hb : env.HasType univs (.forallE S E :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE S E :: Γ)) mode
      (proofErase (.forallE S E :: Γ) a)
      (proofErase (.forallE S E :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP (.typeFunction HE HBdom) HB ha hb H

/-- The same converted function-input body path supports all first-layer
computations with recursive guards and the exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_typeFunction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ S (.forallE B (.sort v)) (.sort u))
    (HBdom : TerminalDomain Γ B)
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam (.forallE B (.sort v)) body))
    (HB : StructuralFamilyRecovery D 1 (.forallE B (.sort v) :: Γ) body
      (proofErase (.forallE B (.sort v) :: Γ) E) n)
    (he : env.HasType univs (.forallE S E :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE S E :: Γ))
      (proofErase (.forallE S E :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP (.typeFunction HE HBdom) HB he R

end Lean4Lean.VEnv.Strengthening
