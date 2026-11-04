import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredStages

/-! # Finite bounds and closure of recovered-carrier singleton stages -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]
namespace ProofShape

/-- Each compatible recovered-carrier comparison over a union has one finite
bound, including both native recoveries and its old computed carrier guard. -/
theorem CarrierRecoveredCompare.finite_stage (hmono : ScopedStagesMonotone Stages)
    (H : CarrierRecoveredCompare (ScopedStageUnion Stages) Δ mode a b) :
    ∃ stage, CarrierRecoveredCompare (Stages stage) Δ mode a b := by
  induction H with
  | base H => obtain ⟨n, H⟩ := H.finite_stage hmono; exact ⟨n, .base H⟩
  | recovered RA RB H =>
    obtain ⟨n, RA⟩ := RA.finite_stage hmono
    obtain ⟨m, RB⟩ := RB.finite_stage hmono
    obtain ⟨k, H⟩ := H.finite_stage hmono
    refine ⟨max n (max m k), .recovered (RA.mono (hmono ?_)) (RB.mono (hmono ?_))
      (H.mono (hmono ?_))⟩ <;> omega
  | app _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .app (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | proj _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .proj H⟩
  | lam _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .lam (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | forallE _ _ ih₁ ih₂ =>
    obtain ⟨n, H⟩ := ih₁; obtain ⟨m, K⟩ := ih₂
    exact ⟨max n m, .forallE (H.mono (hmono (Nat.le_max_left _ _))) (K.mono (hmono (Nat.le_max_right _ _)))⟩
  | compute RA RB _ ih =>
    obtain ⟨n, H⟩ := ih
    obtain ⟨m, A⟩ := RA.finite_stage hmono
    obtain ⟨k, B⟩ := RB.finite_stage hmono
    refine ⟨max n (max m k), .compute (A.mono (hmono ?_)) (B.mono (hmono ?_)) (H.mono (hmono ?_))⟩ <;> omega
  | symm _ ih => obtain ⟨n, H⟩ := ih; exact ⟨n, .symm H⟩

/-- Union comparison is exactly finite-stage comparison. -/
theorem carrier_recovered_compare_union_iff (hmono : ScopedStagesMonotone Stages) :
    CarrierRecoveredCompare (ScopedStageUnion Stages) Δ mode a b ↔
      ∃ stage, CarrierRecoveredCompare (Stages stage) Δ mode a b :=
  ⟨fun H => H.finite_stage hmono, fun ⟨stage, H⟩ => H.mono (fun H => ⟨stage, H⟩)⟩

/-- General recovered-carrier singleton guards over a union choose one finite stage;
the source realization and exact generated program do not change. -/
theorem CarrierRecoveredSingletonPrimitive.finite_stage (hmono : ScopedStagesMonotone Stages)
    (H : CarrierRecoveredSingletonPrimitive (ScopedStageUnion Stages) Δ a b) :
    ∃ stage, CarrierRecoveredSingletonPrimitive (Stages stage) Δ a b := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨stage, HG⟩ := CarrierRecoveredCompare.finite_stage hmono HG
    exact ⟨stage, HT, .intro V ha hcalc HG⟩
end ProofShape

/-- The union is closed under its own general singleton and joint Eq guards. -/
theorem erased_carrier_recovered_union_iff :
    ErasedCarrierRecoveredUnion D Δ a b ↔ ErasedIotaPrimitive D a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedCarrierRecoveredUnion D) Δ a b ∨ ComputedJointPrefixPrimitive (ErasedCarrierRecoveredUnion D) Δ a b := by
  constructor
  · rintro ⟨stage, H⟩
    induction stage with
    | zero => exact .inl H
    | succ stage ih =>
      rcases H with H | H | H
      · exact ih H
      · exact .inr (.inl (H.mono (fun H => ⟨stage, H⟩)))
      · exact .inr (.inr (H.mono (fun H => ⟨stage, H⟩)))
  · intro H
    rcases H with H | H | H
    · exact ⟨0, H⟩
    · obtain ⟨stage, H⟩ := H.finite_stage erased_carrier_recovered_stage_mono
      exact ⟨stage + 1, .inr (.inl H)⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_carrier_recovered_stage_mono
        exact ⟨stage + 1, .inr (.inr (.intro HC))⟩

/-- The closed recovered-carrier union retains arbitrary-block source-typed descent. -/
theorem erased_carrier_recovered_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedCarrierRecoveredUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_carrier_recovered_stage_descent heq hs stage hΓ hΓ' W ht H

/-- Union primitives still only contract constant/projection heads. -/
theorem erased_carrier_recovered_union_head (H : ErasedCarrierRecoveredUnion D Δ a b) : PrimitiveHead a := by
  obtain ⟨stage, H⟩ := H
  exact erased_carrier_recovered_stage_head stage H

/-- Every union primitive replays through an actual original prefix computation. -/
theorem erased_carrier_recovered_union_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ErasedCarrierRecoveredUnion D) := by
  intro Γ e T out hΓ ht H
  obtain ⟨stage, H⟩ := H
  exact erased_carrier_recovered_stage_replay heq hs hregistry stage hΓ ht H

end Lean4Lean.VEnv.Strengthening
