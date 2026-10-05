import Lean4Lean.Theory.Typing.AnchoredOriginalParameterEqualities

/-! A joint reserve for the independent parameter-conversion proof roots
and the original constructor header. Mixing these roots under captures
requires their sum inside the capture product, not just an additive proof
cost outside it. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

/-- Both sides of an earlier-domain comparison may use independent original
roots. Each captured slot can use either a header domain or an equality
cell, hence the combined coefficient in every factor. -/
def parameterDependencyReserve (count header equalities field major : Nat) : Nat :=
  2 * (header + equalities) * ((header + equalities + 2) ^ count * (1 + field + major))

theorem parameterDependencyReserve_mono
    (headerBound : header ≤ header') (equalityBound : equalities ≤ equalities')
    (fieldBound : field ≤ field') (majorBound : major ≤ major') :
    parameterDependencyReserve count header equalities field major ≤
      parameterDependencyReserve count header' equalities' field' major' := by
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 2 (Nat.add_le_add headerBound equalityBound)
  · apply Nat.mul_le_mul
    · exact Nat.pow_le_pow_left (by omega) count
    · omega

/-- A computed declaration prefix shorter than the retained metadata bound
has no larger reserve; skipped/unqueried slots remain admissible. -/
theorem parameterDependencyReserve_count_mono (bound : count ≤ count') :
    parameterDependencyReserve count header equalities field major ≤
      parameterDependencyReserve count' header equalities field major := by
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) bound)

/-- The actual two-root closure edge fits whenever the finite capture ledger
has the combined-root bound. The later producer establishes that ledger
bound from its original cells; no term-query semantic assumption appears. -/
theorem parameter_pair_bound
    (left right : Origin) (captured initial : List Closure)
    (leftBound : left.weight ≤ header + equalities)
    (rightBound : right.weight ≤ header + equalities)
    (captureBound : 1 + environmentCost captured ≤
      ((header + equalities + 2) ^ count * (1 + field + major)) *
        (1 + environmentCost initial)) :
    (Closure.close left captured).cost + (Closure.close right captured).cost ≤
      parameterDependencyReserve count header equalities field major *
        (1 + environmentCost initial) := by
  have first := Nat.mul_le_mul leftBound captureBound
  have second := Nat.mul_le_mul rightBound captureBound
  have sum := Nat.add_le_add first second
  simpa only [Closure.cost, parameterDependencyReserve, Nat.mul_assoc, Nat.two_mul, Nat.add_mul] using sum

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
