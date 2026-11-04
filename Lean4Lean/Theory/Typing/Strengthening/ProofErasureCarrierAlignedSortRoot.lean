import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelExposure

/-! # Sort computation with explicit universe conversion

Sort roots preserve universe equivalence in the level-extended stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape

/-- Primitive sort roots preserve the sort constructor and level equivalence. -/
def SortRootLevels (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Δ u out}, Step Δ (.sort u) out → ∃ v, out = .sort v ∧ u ≈ v

private theorem beta_sort (R : BetaRed a b) (E : a = .sort u) : b = .sort u := by
  induction R with
  | refl => exact E
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ E)
  | app | proj | lam | forallE | beta => cases E

/-- A finite computation from a sort retains an equivalent universe. -/
theorem ScopedCompute.sort_levels_inv (hn : SortRootLevels Step)
    (R : ScopedCompute Step Δ (.sort u) out) :
    ∃ v, out = .sort v ∧ u ≈ v := by
  generalize E : ProofShape.sort u = source at R
  induction R generalizing u with
  | base H => exact hn (E ▸ H)
  | beta H => exact ⟨u, beta_sort H E.symm, by rfl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨v, rfl, HL⟩ := ih₁ E
    obtain ⟨w, HE, HL'⟩ := ih₂ rfl
    exact ⟨w, HE, HL.trans HL'⟩
  | app | proj | lam | forallE => cases E

end ProofShape
variable [Params]

/-- Every finite level-extended stage has stable sort roots. -/
theorem erased_level_recovered_stage_sort_levels (stage : Nat) :
    SortRootLevels (ErasedLevelRecoveredStage D stage) := by
  intro Δ u out H
  rcases erased_level_recovered_stage_root stage H with H | H
  · exact H.elim
  · cases H with
    | sort HL hw => exact ⟨_, rfl, HL⟩

/-- The closed level-extended union has stable sort roots. -/
theorem erased_level_recovered_union_sort_levels :
    SortRootLevels (ErasedLevelRecoveredUnion D) := by
  rintro Δ u out ⟨stage, H⟩
  exact erased_level_recovered_stage_sort_levels stage H

end Lean4Lean.VEnv.Strengthening
