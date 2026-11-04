import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage

/-! # Recursive instantiation with converted domains and finite body recovery

The lambda body's selected output need not be a sort or neutral. A finite
body recovery certificate replaces those terminal shape restrictions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A beta-exposed lambda with a certified selected domain and any finite
body recovery path instantiates the entire stage-zero comparison. Selected
domains may be exact, protected neutral, or convertible dependent functions. -/
theorem proofErase_computed_joint_zero_compare_inst_selectedBody
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam A body))
    (HD : SelectedLambdaDomain 0 Γ (proofErase Γ S) A)
    (HB : StructuralFamilyRecovery D 1 (A :: Γ) body (proofErase (A :: Γ) E) n)
    (ha : env.HasType univs (.forallE S E :: Γ) a T)
    (hb : env.HasType univs (.forallE S E :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (.forallE S E :: Γ)) mode
      (proofErase (.forallE S E :: Γ) a) (proofErase (.forallE S E :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs hΓ hp
    (StructuralFamilyRecovery.of_beta_selected_body hΓ hp RP HD HB) ha hb H

/-- The same selected-domain criterion instantiates every first-layer
computation and retains the exact substituted target. -/
theorem proofErase_computed_joint_one_compute_inst_selectedBody
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam A body))
    (HD : SelectedLambdaDomain 0 Γ (proofErase Γ S) A)
    (HB : StructuralFamilyRecovery D 1 (A :: Γ) body (proofErase (A :: Γ) E) n)
    (he : env.HasType univs (.forallE S E :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (.forallE S E :: Γ))
      (proofErase (.forallE S E :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs hΓ hp
    (StructuralFamilyRecovery.of_beta_selected_body hΓ hp RP HD HB) he R

/-- An image beta-exposing a converted-domain lambda with a finite body path
instantiates every common-typed recursive comparison. The result type E has
no shape restriction; no target comparison is assumed for future bodies. -/
theorem proofErase_computed_joint_zero_compare_inst_convertedBody
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
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
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP (.dependent HAB HA) HB ha hb H

/-- The same finite converted-domain body path supports all first-layer
computations with recursive guards and the exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_convertedBody
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
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
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP (.dependent HAB HA) HB he R

end Lean4Lean.VEnv.Strengthening
