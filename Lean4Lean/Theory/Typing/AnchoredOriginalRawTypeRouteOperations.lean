import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail

/-- A literal expression equality only changes the display index. Both
original occurrences and the destination baseline remain explicit. -/
noncomputable def RawGeneratedTypeRoute.sameExpression
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial
      (frame.realization.frame.dependencyEnvironment rightOrdered) := by
  cases same
  exact .same left right leftOrdered rightOrdered initial frame

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
