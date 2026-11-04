import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecoveredVariants

/-! # Recovered singleton stages with explicit universe conversion

The level-extended base preserves the existing singleton and Eq-prefix guards.
All old recovered stages embed at the same finite index, and every new stage
has typed binder descent. Context/variant closure is proved separately in LevelStageClosure; semantic
descent alone does not imply certificate transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- Existing recovered-family and joint-prefix stages over the level-extended core. -/
def ErasedLevelRecoveredStage (D : Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedLevelCore D
  | stage + 1 => fun Δ a b => ErasedLevelRecoveredStage D stage Δ a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedLevelRecoveredStage D stage) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedLevelRecoveredStage D stage) Δ a b

/-- Every old recovered stage embeds at its unchanged finite index. -/
theorem erased_recovered_into_level_stage : ∀ stage {Δ a b},
    ErasedCarrierRecoveredStage D stage Δ a b → ErasedLevelRecoveredStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact Or.inl
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr (H.mono ih))

/-- Explicit universe conversion is available at every finite stage. -/
theorem erased_level_primitive_into_stage (H : LevelPrimitive univs a b) :
    ∀ stage, ErasedLevelRecoveredStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact .inr H
  | succ stage ih => exact .inl ih

/-- Every level-extended recovered stage descends through arbitrary binder blocks. -/
theorem erased_level_recovered_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) := by
  intro stage
  induction stage with
  | zero => exact erased_level_core_descent hs
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_carrier_recovered_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_computed_joint_prefix_descent heq ih hΓ hΓ' W ht H

/-- The union includes computations from any finite level-extended recovered stage. -/
def ErasedLevelRecoveredUnion (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ stage, ErasedLevelRecoveredStage D stage Δ a b

/-- The old recovered union is a subrelation of the new union. -/
theorem erased_recovered_into_level_union (H : ErasedCarrierRecoveredUnion D Δ a b) :
    ErasedLevelRecoveredUnion D Δ a b := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_recovered_into_level_stage stage H⟩

/-- The level-extended union has source-typed arbitrary-block descent. -/
theorem erased_level_recovered_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedLevelRecoveredUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_level_recovered_stage_descent heq hs stage hΓ hΓ' W ht H

end Lean4Lean.VEnv.Strengthening
