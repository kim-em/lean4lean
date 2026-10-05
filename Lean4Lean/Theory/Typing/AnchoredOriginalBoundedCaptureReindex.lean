import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Captured-head source reconstruction preserves the destination capacity.
The exact stored query chooses its owner and generated common binder scope;
returning through that scope preserves the same bounded output frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichGroupedCapture.reindexBoundedHead
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.raw)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (seedExtension : OriginalFrameExtension ownerFrame.raw seed.frame.raw)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw entry.frame.raw))
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (need : Need) (member : need ∈ entries.needs)
    (destination : OriginalNestedDisplay U common (rawCapture.subst ownerRaw) destinationType)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight destination.graph destinationFrame.frame.raw)
    (reindex : ∀ entry ∈ entries,
      ∀ scope : CappedGeneratedOwnerScope base commonCaps ownerGraph commonLeft commonRight entry,
      ∀ next : OriginalCaptureRealization (destination.weaken scope.insertion).graph env registry target
        destinationLocals scope.left scope.right destinationAvailable,
      CappedCaptureGenerated base scope.caps scope.left scope.right (destination.weaken scope.insertion).graph next.frame.raw →
      next.frame.dependencyEnvironment destinationOrdered = destinationFrame.frame.dependencyEnvironment destinationOrdered →
      richSchedule .expressionReindex
        ((Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost +
          (Closure.close (destination.node.dependencyOrigin destinationOrdered) (next.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin headerOrdered)
          ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost +
          (Closure.close (destination.node.dependencyOrigin destinationOrdered)
            (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) →
      Nonempty (BoundedGeneratedQueryReply base scope.caps (destination.weaken scope.insertion) scope.left scope.right entry.input
        (environmentCost (next.frame.dependencyEnvironment destinationOrdered)))) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance)
      ((tail.group domain ordered ownerInitial entries).raw) ∧
      Nonempty (BoundedGeneratedQueryReply base commonCaps destination commonLeft commonRight need.profile
        (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered))) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  obtain ⟨extension⟩ := owners entry present
  have values := entry.extensionRealizations extension
  have inputGenerated := CappedCaptureGenerated.groupOfValues generated domain ownerGenerated nominalGraph
    nominal provenance displayed ordered ownerInitial seed seedExtension entries owners values.2.2.2.1 values.2.2.2.2
  obtain ⟨scope⟩ := entry.generateCappedOwnerScope ownerFrame ownerGenerated extension
  obtain ⟨next, nextGenerated, sameEnvironment⟩ := destinationFrame.weakenCapped destinationGenerated
    scope.insertion scope.leftTail scope.rightTail scope.capsTail
  have bound : richSchedule .expressionReindex
      ((Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost +
        (Closure.close (destination.node.dependencyOrigin destinationOrdered) (next.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
      ((Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost +
        (Closure.close (destination.node.dependencyOrigin destinationOrdered)
          (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) := by
    rw [sameEnvironment destinationOrdered]
    exact richSchedule_strict (Nat.add_lt_add_right
      (entries.ownerQuery_bound ordered headerOrdered tail present (variableNode.dependencyOrigin headerOrdered)) _) _ _
  obtain ⟨reply⟩ := reindex entry present scope next nextGenerated (sameEnvironment destinationOrdered) bound
  rw [sameEnvironment destinationOrdered] at reply
  have requestedQuery := reply.localDemand need (captureNeeds_covered entry.input need requested).1
    (captureNeeds_covered entry.input need requested).2
  exact ⟨inputGenerated, requestedQuery.unweaken scope.insertion scope.leftTail scope.rightTail scope.capsTail⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
