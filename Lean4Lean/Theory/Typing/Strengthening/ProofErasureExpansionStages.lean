import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeIdentityExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelStageRenaming

/-! # Recovered stages with controlled beta expansion

The base admits constant expansion as well as universe conversion and core
computation. Singleton, Eq and native identity guards use the entire preceding expanded stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- The expanded base, followed by unrestricted finite recovered guard layers. -/
def ErasedExpansionStage (D : Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ a b => ErasedLevelCore D a b ∨ ConstantExpansion a b
  | stage + 1 => fun Δ a b => ErasedExpansionStage D stage Δ a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedExpansionStage D stage) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedExpansionStage D stage) Δ a b ∨
      NativeIdentityExpansion (ErasedExpansionStage D stage) Δ a b

/-- Existing universe-converted stages embed at the same finite index. -/
theorem erased_level_into_expansion_stage : ∀ stage {Δ a b},
    ErasedLevelRecoveredStage D stage Δ a b → ErasedExpansionStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact Or.inl
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr (.inl (H.mono ih)))

/-- Expanded stages increase monotonically. -/
theorem erased_expansion_stage_mono (hle : stage ≤ later) {Δ a b}
    (H : ErasedExpansionStage D stage Δ a b) : ErasedExpansionStage D later Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- The expanded guarded system descends through arbitrary binder blocks. -/
theorem erased_expansion_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedExpansionStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H
    · exact erased_level_core_descent hs hΓ hΓ' W ht H
    · exact erased_constantExpansion_descent hΓ hΓ' W ht H
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_carrier_recovered_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_computed_joint_prefix_descent heq ih hΓ hΓ' W ht H
    · exact erased_nativeIdentityExpansion_descent ih hΓ hΓ' W ht H

/-- Exact interpreted renaming preserves every expansion and guard. -/
theorem erased_expansion_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage {Δ Δ' a b τ}, ErasedExpansionStage D stage Δ a b →
      ContextRenaming Δ Δ' τ → ErasedExpansionStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero =>
    intro Δ Δ' a b τ H W
    rcases H with (H | H) | H
    · exact .inl (.inl (erased_iota_primitive_subst H))
    · exact .inl (.inr H.subst)
    · exact .inr (H.rename W)
  | succ stage ih =>
    intro Δ Δ' a b τ H WR
    rcases H with H | H | H | H
    · exact .inl (ih H WR)
    · exact .inr (.inl (H.rename heq (erased_expansion_stage_descent heq hs stage)
        (erased_expansion_stage_descent heq hs stage) ih WR))
    · exact .inr (.inr (.inl (H.rename ih WR)))
    · exact .inr (.inr (.inr (H.rename ih WR)))

/-- Arbitrary finite expanded guard depth. -/
def ErasedExpansionUnion (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ stage, ErasedExpansionStage D stage Δ a b

/-- Union certificates retain source-typed binder descent. -/
theorem erased_expansion_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_expansion_stage_descent heq hs stage hΓ hΓ' W ht H

/-- All previous union certificates remain valid. -/
theorem erased_level_into_expansion_union (H : ErasedLevelRecoveredUnion D Δ a b) :
    ErasedExpansionUnion D Δ a b := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_level_into_expansion_stage stage H⟩

/-- The finite-stage union is closed under its own recovered guards, including
native identity annotations. Each guard has a finite certificate bound. -/
theorem erased_expansion_union_iff :
    ErasedExpansionUnion D Δ a b ↔ (ErasedLevelCore D a b ∨ ConstantExpansion a b) ∨
      CarrierRecoveredSingletonPrimitive (ErasedExpansionUnion D) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedExpansionUnion D) Δ a b ∨
      NativeIdentityExpansion (ErasedExpansionUnion D) Δ a b := by
  constructor
  · rintro ⟨stage, H⟩
    induction stage with
    | zero => exact .inl H
    | succ stage ih =>
      rcases H with H | H | H | H
      · exact ih H
      · exact .inr (.inl (H.mono (fun H => ⟨stage, H⟩)))
      · exact .inr (.inr (.inl (H.mono (fun H => ⟨stage, H⟩))))
      · exact .inr (.inr (.inr (H.mono (fun H => ⟨stage, H⟩))))
  · intro H
    rcases H with H | H | H | H
    · exact ⟨0, H⟩
    · obtain ⟨stage, H⟩ := H.finite_stage erased_expansion_stage_mono
      exact ⟨stage + 1, .inr (.inl H)⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_expansion_stage_mono
        exact ⟨stage + 1, .inr (.inr (.inl (.intro HC)))⟩
    · cases H with
      | intro R =>
        obtain ⟨stage, R⟩ := R.finite_stage (Stages := ErasedExpansionStage D)
          (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
        exact ⟨stage + 1, .inr (.inr (.inr (.intro R)))⟩

end Lean4Lean.VEnv.Strengthening
