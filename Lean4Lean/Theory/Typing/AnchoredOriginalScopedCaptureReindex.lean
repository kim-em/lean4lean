import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex

/-! A captured source variable selects an actual owner scope. Its frame may
contain merges selected by earlier reconstruction; no binder-constructor
extension is required. Singleton closure preserves its exact original cost. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private lifted_substitution from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedCaptureReindex
set_option backward.isDefEq.respectTransparency false

/-- Dispatch the selected whole owner query to strictly smaller R, including
its actual closure and scope. The returned destination frame is unweakened
unchanged, so the original destination budget is preserved. -/
theorem RichGroupedCapture.reindexScopedBoundedHead
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (baseClosed : base.available.AtomClosed)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext))
    (owners : ∀ entry member, CappedCaptureGenerated base (scopes entry member).caps (scopes entry member).left
      (scopes entry member).right (scopes entry member).graph entry.frame.raw)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (need : Need) (member : need ∈ entries.needs)
    (destination : OriginalNestedDisplay U common (rawCapture.subst ownerRaw) destinationType)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      destination.graph destinationFrame.frame.raw)
    (destinationClosed : destinationAvailable.AtomClosed)
    (reindex : ∀ entry member, GeneratedObservationCall base (scopes entry member).caps
      (entry.scopeDisplay (scopes entry member)) (destination.weaken (scopes entry member).insertion)
      (scopes entry member).left (scopes entry member).right ordered destinationOrdered
      (richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin headerOrdered)
          ((tail.group domain ordered initial entries).dependencyEnvironment headerOrdered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost))) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps destination commonLeft commonRight need.profile
      (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered))) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  let scope := scopes entry present
  have ownerGenerated := owners entry present
  obtain ⟨owner, ownerCapped, ownerEnvironment⟩ := ownerGenerated.realize entry.frame entry.substitutions
  obtain ⟨ownerAvailable, closedOwner, closedCapped, included, closed, closedEnvironment⟩ :=
    owner.closeResources ownerCapped baseClosed
  obtain ⟨next, nextGenerated, sameEnvironment⟩ := destinationFrame.weakenCapped destinationGenerated
    scope.insertion scope.leftTail scope.rightTail scope.capsTail
  have bound : richSchedule .expressionReindex
      ((Closure.close (entry.owner.node.dependencyOrigin ordered) (closedOwner.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (destination.node.dependencyOrigin destinationOrdered) (next.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
      ((Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.group domain ordered initial entries).dependencyEnvironment headerOrdered)).cost +
       (Closure.close (destination.node.dependencyOrigin destinationOrdered)
         (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) := by
    rw [closedEnvironment, ownerEnvironment, sameEnvironment]
    exact richSchedule_strict (Nat.add_lt_add_right
      (entries.ownerQuery_bound ordered headerOrdered tail present (variableNode.dependencyOrigin headerOrdered)) _) _ _
  have query : RichObs sourceEnv env U registry target entry.owner.node entry.ownerLocals
      (scope.raw.comp scope.left) entry.queryInput entry.footprint := by
    rw [← ownerGenerated.generated.realizations.1]
    exact entry.query
  obtain ⟨reply⟩ := reindex entry present closedOwner closedCapped closed next nextGenerated destinationClosed bound query
    (fun i need member => included i need (entry.queryAvailable i need member))
  rw [sameEnvironment destinationOrdered] at reply
  let adapted := reply.mapQuery (reply.answer.reply.query.adaptRequest henv hscoped formed
    entry.queryBound entry.queryAdapter)
  exact (adapted.localDemand need (captureNeeds_covered entry.input need requested).1
    (captureNeeds_covered entry.input need requested).2).unweaken
    scope.insertion scope.leftTail scope.rightTail scope.capsTail

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
