import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistoryGeneration

/-! Connect two original typings of a displayed application to the retained
result formation. Equality of the displayed terms is not confused with
equality of their assigned types. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

namespace OriginalApplicationTypeRouteSide
section
variable
    (side : OriginalApplicationTypeRouteSide U common)
    (start : OriginalNestedDisplay U common ((VExpr.app side.f side.a).subst side.raw) startAssigned)
    (startOrdered : start.sourceEnv.Ordered) (sideOrdered : side.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight)

/-- Compare the assigned types at the two actual application occurrences,
then retain the application's independently stored result formation. -/
noncomputable def resultFromAssignedRoute :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      start.formationDisplay side.resultDisplay initial
      (frame.realization.frame.dependencyEnvironment sideOrdered) :=
  .trans
    (.assigned start side.termDisplay startOrdered sideOrdered initial frame)
    (.same side.termDisplay.formationDisplay side.resultDisplay sideOrdered sideOrdered
      (frame.realization.frame.dependencyEnvironment sideOrdered) frame)

theorem resultFromAssignedRoute_frames :
    (side.resultFromAssignedRoute start startOrdered sideOrdered initial frame).frames =
      [frame.box, frame.box] := by
  simp only [resultFromAssignedRoute, RawGeneratedTypeRoute.frames.eq_def, List.singleton_append]

theorem resultFromAssignedRoute_reserve :
    (side.resultFromAssignedRoute start startOrdered sideOrdered initial frame).reserve =
      [Closure.bundle (.close (start.node.dependencyOrigin startOrdered) initial)
        (.close (side.node.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered)),
       Closure.bundle (.close (side.termDisplay.formationDisplay.node.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered))
        (.close (side.result.dependencyOrigin sideOrdered)
          (frame.realization.frame.dependencyEnvironment sideOrdered))] := by
  simp only [resultFromAssignedRoute, RawGeneratedTypeRoute.reserve.eq_def, List.singleton_append]
  rfl

theorem resultFromAssignedRoute_generated
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight side.graph
      frame.realization.frame.raw) :
    (side.resultFromAssignedRoute start startOrdered sideOrdered initial frame).Generated base commonCaps := by
  refine ⟨?_, ?_⟩
  · simp only [resultFromAssignedRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨True.intro, True.intro⟩
  · intro boxed member
    rw [side.resultFromAssignedRoute_frames start startOrdered sideOrdered initial frame] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    cases member
    exact generated


end
end OriginalApplicationTypeRouteSide
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
