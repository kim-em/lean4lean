import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelUnionClosure

/-! # Literal changed-binder transport at arbitrary finite stage

The source binder is Sort (max 0 0), and the target binder is Sort 0. Their raw
contexts are provably distinct. Any typed finite stage computation, including
guarded singleton/Eq steps at any finite nesting depth, transports with its
exact output and without increasing the stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A nonliteral universe change of one binder preserves every finite stage
computation and its exact raw output, including generated prefix lambdas. -/
theorem carrier_aligned_level_stage_literal_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs (.sort (.max .zero .zero) :: Γ) e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D stage)
      (proofEraseCtx (.sort (.max .zero .zero) :: Γ))
      (proofErase (.sort (.max .zero .zero) :: Γ) e) out) :
    proofEraseCtx (.sort (.max .zero .zero) :: Γ) ≠ proofEraseCtx (.sort .zero :: Γ) ∧
    ScopedCompute (ErasedLevelRecoveredStage D stage) (proofEraseCtx (.sort .zero :: Γ))
      (proofErase (.sort (.max .zero .zero) :: Γ) e) out := by
  have hA : env.HasType univs Γ (.sort (.max .zero .zero)) (.sort (.succ (.max .zero .zero))) := .sort (by trivial)
  have hB : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΓA : OnCtx (.sort (.max .zero .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hΓB : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have EA : proofErase Γ (.sort (.max .zero .zero)) = .sort (.max .zero .zero) :=
    if_neg (not_isProof_of_sort hΓ hA)
  have EB : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hB)
  have HO : List.Forall₂ StructuralVariant (proofEraseCtx (.sort (.max .zero .zero) :: Γ))
      (proofEraseCtx (.sort .zero :: Γ)) := by
    simp only [proofEraseCtx, EA, EB]
    exact .cons (.sort (by rfl)) (.rfl (fun _ _ => .refl))
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) :=
    erased_level_recovered_stage_descent heq hs stage
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredStage D stage)
    hstep hΓA hΓB HO
  refine ⟨?_, structuralVariantComputeContext_level_stage heq hs stage hΓA ht W HO rfl rfl R⟩
  intro H
  simp only [proofEraseCtx, EA, EB] at H
  cases H

end Lean4Lean.VEnv.Strengthening
