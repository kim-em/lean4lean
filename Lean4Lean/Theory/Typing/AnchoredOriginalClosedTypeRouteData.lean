import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration

/-! Exact empty-context route data, independent of any header normalization interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def closedCaptureGraph (context : ContextDerivation sourceEnv U []) (common : List VExpr) :
    OriginalCaptureMap (common := common) context .id := by
  cases context
  exact .empty common

def closedTypeRouteFrame (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (left right : Subst) :
    OriginalTypeRouteFrame env registry target (closedCaptureGraph context common) left right := by
  cases context
  exact {
    locals := [], available := fun _ => []
    realization := { frame := .nil, substitutions := .nil }
    closed := by intro i need member; cases member }

theorem closedTypeRouteFrame_capped
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (left right : Subst) :
    CappedCaptureGenerated base caps left right (closedCaptureGraph context common)
      (closedTypeRouteFrame context common env registry target left right).realization.frame.raw := by
  cases context
  exact .empty common left right

theorem closedTypeRouteFrame_environment
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    (ordered : sourceEnv.Ordered) :
    (closedTypeRouteFrame context common env registry target left right).realization.frame.dependencyEnvironment
      ordered = [] := by
  cases context
  rfl

theorem RawGeneratedTypeRoute.sameExpression_generated
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight right.graph frame.realization.frame.raw) :
    (sameExpression left right same leftOrdered rightOrdered initial frame).Generated base commonCaps := by
  cases same
  refine ⟨?_, ?_⟩
  · rw [sameExpression, WellFormed.eq_def]; trivial
  · intro boxed member
    simp only [sameExpression, frames.eq_def, List.mem_singleton] at member
    subst boxed
    exact capped

theorem RawGeneratedTypeRoute.sameExpression_reserve
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
    (sameExpression left right same leftOrdered rightOrdered initial frame).reserve =
      [.bundle (.close (left.node.dependencyOrigin leftOrdered) initial)
        (.close (right.node.dependencyOrigin rightOrdered)
          (frame.realization.frame.dependencyEnvironment rightOrdered))] := by
  cases same
  rw [sameExpression, reserve.eq_def]


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
