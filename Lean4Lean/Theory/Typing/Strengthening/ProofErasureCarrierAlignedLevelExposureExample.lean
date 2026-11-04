import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelGuardTransfer

/-! # The original head interface fails in every level-extended stage

A nonliteral sort conversion is an actual typed primitive at every stage. Pi
exclusion and stable-family exposure therefore cannot be obtained by assuming
the old constant/projection-only head interface for this extended relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A nonliteral, typed sort conversion witnesses failure of the old root-head
interface at every finite stage, independently of any guarded computation. -/
theorem carrier_aligned_level_stage_sort_root (stage : Nat) :
    env.HasType univs Γ (.sort (.max .zero .zero)) (.sort (.succ (.max .zero .zero))) ∧
    env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) ∧
    ErasedLevelRecoveredStage D stage Δ (.sort (.max .zero .zero)) (.sort .zero) ∧
    (ProofShape.sort (.max .zero .zero) ≠ .sort .zero) ∧
    ¬ PrimitiveHead (.sort (.max .zero .zero)) := by
  refine ⟨.sort (by trivial), .sort (by trivial),
    erased_level_primitive_into_stage (.sort (by rfl) (by trivial)) stage, ?_, ?_⟩
  · intro H; cases H
  · intro H; exact H

/-- Every finite level-extended stage violates the older primitive-head
hypothesis, so its new exposure consumers genuinely require the weaker laws. -/
theorem carrier_aligned_level_stage_not_old_head (stage : Nat) :
    ¬ (∀ {Δ a b}, ErasedLevelRecoveredStage D stage Δ a b → PrimitiveHead a) := by
  intro H
  exact (carrier_aligned_level_stage_sort_root (D := D) (Γ := []) (Δ := []) stage).2.2.2.2
    (H (carrier_aligned_level_stage_sort_root (D := D) (Γ := []) (Δ := []) stage).2.2.1)

end Lean4Lean.VEnv.Strengthening
