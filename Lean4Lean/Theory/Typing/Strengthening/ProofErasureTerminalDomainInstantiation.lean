import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedBodyInstantiation

/-! # Instantiating higher-order images with terminal-valued input domains

Ordinary conversion of the inner input domain is enough when its generic
variable is terminal. This includes universes and rigid or all-proof-field data,
without requiring a protected neutral head or an exact raw annotation match.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An image beta-exposing a lambda whose function input has a terminal-valued domain with a finite body path
instantiates every common-typed recursive comparison. The result type E has
no shape restriction; no target comparison is assumed for future bodies. -/
theorem proofErase_computed_joint_zero_compare_inst_terminalDomain
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (hp : env.HasType univs Γ p (.forallE (.forallE A C) E))
    (RP : VExpr.BetaRed p (.lam (.forallE B C) body))
    (HB : StructuralFamilyRecovery D 1 (.forallE B C :: Γ) body
      (proofErase (.forallE B C :: Γ) E) n)
    (ha : env.HasType univs (.forallE (.forallE A C) E :: Γ) a T)
    (hb : env.HasType univs (.forallE (.forallE A C) E :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0)
      (proofEraseCtx (.forallE (.forallE A C) E :: Γ)) mode
      (proofErase (.forallE (.forallE A C) E :: Γ) a)
      (proofErase (.forallE (.forallE A C) E :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP (.dependentTerminal HAB HA) HB ha hb H

/-- The same terminal-domain body path supports all first-layer
computations with recursive guards and the exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_terminalDomain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (hp : env.HasType univs Γ p (.forallE (.forallE A C) E))
    (RP : VExpr.BetaRed p (.lam (.forallE B C) body))
    (HB : StructuralFamilyRecovery D 1 (.forallE B C :: Γ) body
      (proofErase (.forallE B C :: Γ) E) n)
    (he : env.HasType univs (.forallE (.forallE A C) E :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE (.forallE A C) E :: Γ))
      (proofErase (.forallE (.forallE A C) E :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP (.dependentTerminal HAB HA) HB he R

end Lean4Lean.VEnv.Strengthening
