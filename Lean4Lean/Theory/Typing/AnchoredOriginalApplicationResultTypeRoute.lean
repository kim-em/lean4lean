import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationResultTypeRouteData
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteLedger

/-! Connect two original typings of a displayed application to the retained
result formation. Equality of the displayed terms is not confused with
equality of their assigned types. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false

namespace OriginalApplicationTypeRouteSide
section
variable
    (side : OriginalApplicationTypeRouteSide U common)
    (start : OriginalNestedDisplay U common ((VExpr.app side.f side.a).subst side.raw) startAssigned)
    (startOrdered : start.sourceEnv.Ordered) (sideOrdered : side.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight)

/-- Both charges retain actual endpoint occurrences and actual frame ledgers;
there is no numerical replacement for either original comparison. -/
noncomputable def resultFromAssignedRoute_charged
    (termCharge : ParameterRouteCharge sources ownerInitial count
      (.bundle (.close (start.node.dependencyOrigin startOrdered) initial)
        (.close (side.node.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered))))
    (formationCharge : ParameterRouteCharge sources ownerInitial count
      (.bundle (.close (side.termDisplay.formationDisplay.node.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered))
        (.close (side.result.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered)))) :
    (side.resultFromAssignedRoute start startOrdered sideOrdered initial frame).Charged sources ownerInitial count := by
  simp only [resultFromAssignedRoute, RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨termCharge, formationCharge⟩

end
end OriginalApplicationTypeRouteSide
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
