import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelClosure

/-! # Universe-compatible deterministic unfoldings

Equivalent universe arguments may change the syntax of an unfolding's result.
Normal simulation only needs structural level equivalence of those results.
Unlike exact level saturation, this condition permits deterministic unfoldings.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {D : Definitions}

/-- Equivalent well-formed universe arguments enable an unfolding with a
structurally level-equivalent result. Literal result equality is not required. -/
def Definitions.LevelCompatible (D : Definitions) (U : Nat) : Prop :=
  ∀ {c ls ls' rhs}, D.unfolds c ls rhs → (∀ l ∈ ls', l.WF U) →
    List.Forall₂ (· ≈ ·) ls ls' → ∃ rhs', D.unfolds c ls' rhs' ∧ LEquiv U rhs rhs'

/-- Exact universe stability is a special case of structural compatibility. -/
theorem Definitions.LevelStable.compatible (H : D.LevelStable U) : D.LevelCompatible U := by
  intro c ls ls' rhs HR hw he
  exact ⟨rhs, H HR hw he, .refl⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
