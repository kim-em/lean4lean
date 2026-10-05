import Lean4Lean.Theory.Typing.AnchoredOriginalParameterReserve

/-! A finite reserve for retaining, and subsequently reusing, original
parameter-alignment routes. The major pays its selected seed header and
universe equality roots; the requested declaration roots are separate. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

def routedParameterDependencyReserve (count header equalities field major : Nat) : Nat :=
  2 * (header + equalities + major) *
    ((2 * (header + equalities + major) + 2) ^ count * (1 + field + major))

theorem routedParameterDependencyReserve_mono
    (headerBound : header ≤ header') (equalityBound : equalities ≤ equalities')
    (fieldBound : field ≤ field') (majorBound : major ≤ major') :
    routedParameterDependencyReserve count header equalities field major ≤
      routedParameterDependencyReserve count header' equalities' field' major' := by
  have roots := Nat.add_le_add (Nat.add_le_add headerBound equalityBound) majorBound
  apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 roots)
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 roots) 2) count
  · omega

theorem routedParameterDependencyReserve_count_mono (bound : count ≤ count') :
    routedParameterDependencyReserve count header equalities field major ≤
      routedParameterDependencyReserve count' header equalities field major := by
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) bound)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
