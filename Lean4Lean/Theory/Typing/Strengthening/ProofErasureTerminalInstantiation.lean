import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedBodyInstantiation

/-! # Instantiation by terminal values and terminal-valued lambda bodies

Rigid data without projections and structures with no retained fields need no
native image recovery, regardless of the computation or conversions used to
type the image. The same terminal criterion can close any finite lambda-body
recovery path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Any terminal typed image instantiates a complete recursive comparison.
Its selected assigned type may be different from the type certifying terminality. -/
theorem proofErase_computed_joint_zero_compare_inst_terminal
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_structural (cut := 0) hs hΓ hp
    (.terminal HT) ha hb H

/-- A terminal image preserves every first-layer computation and its exact
instantiated result. There is no reduction or normality premise on the image. -/
theorem proofErase_computed_joint_one_compute_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_structural (cut := 0) heq hs hΓ hp
    (.terminal HT) ht R

/-- Every value at a rigid type without registered projections can replace a
binder at any of its actual assigned types in recursive checking. -/
theorem proofErase_computed_joint_zero_compare_inst_rigidData
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hr : env.Rigid c) (hn : ∀ info, ¬ env.projections c info)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_terminal hs hΓ hp (.data hdata hr hn) ha hb H

/-- Rigid data without projections also preserves actual singleton and Eq
computations throughout the first recursive computation layer. -/
theorem proofErase_computed_joint_one_compute_inst_rigidData
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hr : env.Rigid c) (hn : ∀ info, ¬ env.projections c info)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_terminal heq hs hΓ hp (.data hdata hr hn) ht R

/-- A beta-exposed lambda with a terminal-valued body instantiates every
recursive body comparison. The result type has no syntactic shape restriction;
the selected/written input domains retain their explicit conversion certificate. -/
theorem proofErase_computed_joint_zero_compare_inst_terminalBody
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam A body))
    (HD : SelectedLambdaDomain 0 Γ (proofErase Γ S) A)
    (HT : TerminalImage (A :: Γ) body)
    (ha : env.HasType univs (.forallE S E :: Γ) a T)
    (hb : env.HasType univs (.forallE S E :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (.forallE S E :: Γ)) mode
      (proofErase (.forallE S E :: Γ) a) (proofErase (.forallE S E :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_selectedBody hs hΓ hp RP HD (.terminal HT) ha hb H

/-- Terminal-valued lambda bodies also instantiate first-layer computations,
with exact outputs, including at convertible selected input domains. -/
theorem proofErase_computed_joint_one_compute_inst_terminalBody
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE S E))
    (RP : VExpr.BetaRed p (.lam A body))
    (HD : SelectedLambdaDomain 0 Γ (proofErase Γ S) A)
    (HT : TerminalImage (A :: Γ) body)
    (ht : env.HasType univs (.forallE S E :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (.forallE S E :: Γ))
      (proofErase (.forallE S E :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_selectedBody heq hs hΓ hp RP HD (.terminal HT) ht R

end Lean4Lean.VEnv.Strengthening
