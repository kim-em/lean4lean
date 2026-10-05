import Lean4Lean.Theory.Typing.Strong

/-! Exact original Pi bounds. The Pi constructor leaves one step for changing
an extracted component's universe to an equivalent literal universe. -/

namespace Lean4Lean.VEnv
open VExpr

theorem HasTypeStratified.piComponentBounds
    (typed : HasTypeStratified env U Γ (.forallE A B) V true n) :
    ∃ m u v, m + 1 = n ∧ u.WF U ∧ v.WF U ∧
      HasTypeStratified env U Γ A (.sort u) true m ∧
      HasTypeStratified env U (A :: Γ) B (.sort v) true m := by
  obtain ⟨_, core⟩ := typed.to_core
  cases core with
  | forallE hu hv domain body => exact ⟨_, _, _, rfl, hu, hv, domain, body⟩

theorem HasTypeStratified.equivalentSortSucc
    (typed : HasTypeStratified env U Γ expression (.sort u) true n)
    (hu : u.WF U) (hv : v.WF U) (equivalent : u ≈ v) :
    HasTypeStratified env U Γ expression (.sort v) true (n + 1) := by
  exact .defeq (u := .succ u) hu (.sortDF hu hv equivalent)
    (.base (.sort' hu hu rfl)) (.base (.sort' hv hu equivalent.symm)) typed

/-- Assemble precisely the bounds demanded by Pi injectivity from the original
Pi children. The semantic obligation is a homogeneous component comparison
and equivalence of the two original body levels; no new stratification of a
semantic answer is used. -/
theorem stratifiedPiInversionOfOriginalComponents
    (domain : HasTypeStratified env U Γ A (.sort u) true m)
    (body : HasTypeStratified env U (A :: Γ) B (.sort v) true m)
    (otherBody : HasTypeStratified env U (A' :: Γ) B' (.sort v') true m')
    (leftBound : m + 1 = n) (rightBound : m' + 1 = n')
    (hv : v.WF U) (hv' : v'.WF U) (levels : v ≈ v')
    (domains : IsDefEq env U Γ A A' (.sort u))
    (bodies : IsDefEq env U (A :: Γ) B B' (.sort v)) :
    (∃ u, IsDefEq env U Γ A A' (.sort u) ∧
      HasTypeStratified env U Γ A (.sort u) true n) ∧
    ∃ v, IsDefEq env U (A :: Γ) B B' (.sort v) ∧
      HasTypeStratified env U (A :: Γ) B (.sort v) true n ∧
      HasTypeStratified env U (A' :: Γ) B' (.sort v) true n' := by
  refine ⟨⟨u, domains, domain.mono (by omega)⟩, v, bodies,
    body.mono (by omega), ?_⟩
  subst n'
  exact otherBody.equivalentSortSucc hv' hv levels.symm

end Lean4Lean.VEnv
