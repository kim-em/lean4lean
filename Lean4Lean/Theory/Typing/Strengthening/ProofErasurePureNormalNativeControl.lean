import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePureNormalTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeApplicationTailJoin

/-! # Compared native control result types through non-eta tails

The selected instantiated types may compare without a core join. Pure normal
selected results nevertheless support independent final conversion tails: each
tail returns to its own selected type, where the original comparison applies.
This is a fragment theorem; normality is not asserted for general native outputs.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Compared selected native Pis give a comparison of complete control result
types after arbitrary non-eta union tails, provided the instantiated selected
types are pure and beta-normal in a pure context. The functions, arguments and
selected domains may differ. No common reduct of the selected Pis is required;
normality is required only of the selected result types before the final tails.
Removing these purity and normality premises remains open. -/
theorem stage_zero_pure_normal_native_control_tails_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (HC : env.IsDefEq univs Γ (.sort (.succ u)) C (.sort v))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) xMode
      (.sort u) (proofErase Γ x))
    (HY : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) yMode
      (.sort u) (proofErase Γ y))
    (HΔ : PureContext (proofEraseCtx Γ))
    (HP : PureLambda (Y.inst (proofErase Γ x)))
    (HQ : PureLambda (W.inst (proofErase Γ y)))
    (HNP : NormalSyntax (fun _ _ => False) (Y.inst (proofErase Γ x)))
    (HNQ : NormalSyntax (fun _ _ => False) (W.inst (proofErase Γ y)))
    (RL : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (Y.inst (proofErase Γ x)) outL)
    (RR : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (W.inst (proofErase Γ y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false outL outR := by
  have H := stage_zero_native_control_result_types_compare heq hs hΓ hu HC hf hg hx hy RF RG HT HX HY
  obtain ⟨P, _, hP, EP⟩ := stage_zero_native_result_type_realize heq hs hΓ hf hx RF
  obtain ⟨Q, _, hQ, EQ⟩ := stage_zero_native_result_type_realize heq hs hΓ hg hy RG
  rw [← EP] at HP HNP RL H
  rw [← EQ] at HQ HNQ RR H
  exact proofErase_pure_normal_expansion_tails_compare (fun H => .inl (.inr H))
    hΓ hP hQ HΔ HP HQ HNP HNQ H RL RR

end Lean4Lean.VEnv.Strengthening
