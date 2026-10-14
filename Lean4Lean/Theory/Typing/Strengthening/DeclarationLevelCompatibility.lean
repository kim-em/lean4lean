import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelTransport
import Lean4Lean.Theory.Typing.Strengthening.DeclarationDeterminism

/-! # Universe compatibility of actual stored definitions -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Actual stored definitions are universe-compatible without enlarging the
collection of equations, including definitions with recursive values. -/
theorem Definitions.ofEnv_levelCompatible (henv : env.WF) :
    (Definitions.ofEnv env U henv).LevelCompatible U := by
  intro name ls ls' rhs H hw' he
  obtain ⟨value, hv, hn, rfl⟩ := Definitions.ofEnv_origin henv H
  have hreg := (definitionRegistry_registered hv).1
  obtain ⟨T, HT⟩ := Definitions.ofEnv_sound henv [] name ls _ H
  obtain ⟨ci, hc, hw, hl⟩ := HT.hasType.1.const_inv henv (by trivial)
  rw [← hn, hreg.1] at hc
  cases hc
  have hl' : ls'.length = value.uvars := he.length_eq.symm.trans hl
  refine ⟨value.value.instL ls', ?_, .instL_expr _ hw hw' he⟩
  exact ⟨value.toDefEq, ls', hreg.2, hw', hl', by
    simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl', hn], rfl⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
