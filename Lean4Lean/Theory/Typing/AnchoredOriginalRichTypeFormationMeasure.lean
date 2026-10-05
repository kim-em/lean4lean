import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRichComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule

/-! The computed formation occurrence stays below its original endpoint in
the dependency-aware measure, including recursively selected earlier headers.
An application's function type can therefore be compared with the explicit
Pi formation made from that application's actual domain/body children. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- The Pi destination is made from the application's actual retained children;
its cost plus the function's assigned formation fits strictly below the app. -/
theorem EndpointState.application_function_type_reindex_schedule
    (formed : env.Ordered) (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState env U source A (.sort u))
    (body : EndpointState env U (A :: source) B (.sort v))
    (function : EndpointState env U source f (.forallE A B))
    (argument : EndpointState env U source a A)
    (result : EndpointState env U source (B.inst a) (.sort v)) (captured : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close (function.typeFormation.node.dependencyOrigin formed) captured).cost +
       (Closure.close ((EndpointState.pi hu hv domain body).dependencyOrigin formed) captured).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.app hu hv domain body function argument result).dependencyOrigin formed) captured).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (function.typeFormation_dependency_cost_le formed captured) _)
  apply Nat.lt_of_lt_of_le _ (application_cost_le_captured
    (domain.dependencyOrigin formed) (body.dependencyOrigin formed) (function.dependencyOrigin formed)
    (argument.dependencyOrigin formed) (result.dependencyOrigin formed) captured)
  change ((function.dependencyOrigin formed).weight * (1 + environmentCost captured)) +
    ((Origin.binder (domain.dependencyOrigin formed) [body.dependencyOrigin formed] []).weight *
      (1 + environmentCost captured)) < _
  rw [← Nat.add_mul]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have positive := (result.dependencyOrigin formed).weight_pos
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
