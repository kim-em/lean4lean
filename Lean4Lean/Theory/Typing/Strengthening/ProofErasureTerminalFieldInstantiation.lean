import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage

/-! # Recursive instantiation by structures with retained terminal fields

The image need not expose a constructor or recover its assigned type. A static
constructor-telescope certificate handles all retained projections encountered
inside an arbitrary typed body, while existing structural paths handle the
other elimination cases.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A terminal or terminal-field structure image instantiates every common-typed
stage-zero recursive comparison at any actual assigned type. -/
theorem proofErase_computed_joint_zero_compare_inst_projectable
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (HI : ProjectionTerminalImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs hΓ hp
    (StructuralFamilyRecovery.projectable (cut := 0) HI) ha hb H

/-- The same images preserve every first-layer computation and its exact
substituted output, including the recursively checked guards. -/
theorem proofErase_computed_joint_one_compute_inst_projectable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HI : ProjectionTerminalImage Γ p)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs hΓ hp
    (StructuralFamilyRecovery.projectable (cut := 0) HI) ht R

/-- A closed terminal-field telescope supplies the image certificate. The major
may be indexed, and its assigned type may differ by ordinary conversion. -/
theorem proofErase_computed_joint_zero_compare_inst_terminalFields
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hi : env.projections c info) (HF : StructureReplay.TerminalFields env info)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_projectable hs hΓ hp (.fields hdata hi HF) ha hb H

/-- Terminal-field images also retain exact outputs through the first recursive
computation layer. No native recovery or constructor normalization is assumed. -/
theorem proofErase_computed_joint_one_compute_inst_terminalFields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hi : env.projections c info) (HF : StructureReplay.TerminalFields env info)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_projectable heq hs hΓ hp (.fields hdata hi HF) ht R

end Lean4Lean.VEnv.Strengthening
