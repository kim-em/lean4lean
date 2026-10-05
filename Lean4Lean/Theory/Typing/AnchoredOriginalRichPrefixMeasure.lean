import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReplay

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv
open OriginalClosureMeasure

theorem PrefixRoute.dependency_weight_le (ordered : sourceEnv.Ordered)
    (route : PrefixRoute sourceEnv U source expression first last) :
    (last.dependencyOrigin ordered).weight ≤ (first.dependencyOrigin ordered).weight := by
  induction route with
  | done => exact Nat.le_refl _
  | expose reference rest ih => exact Nat.le_trans ih (reference.expose_dependency_weight_le ordered)
  | convert plan term rest ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (Origin.rule_child (by simp)))

theorem PrefixRoute.dependency_cost_le (ordered : sourceEnv.Ordered)
    (route : PrefixRoute sourceEnv U source expression first last) (captured : List Closure) :
    (Closure.close (last.dependencyOrigin ordered) captured).cost ≤
    (Closure.close (first.dependencyOrigin ordered) captured).cost :=
  Nat.mul_le_mul_right _ (route.dependency_weight_le ordered)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
