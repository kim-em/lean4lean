import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalParameterSuccessor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyArgumentCapture
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportWorld transportWorld_call transportWorld_worlds from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
open private sponsored_covered from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistorySponsorship
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
section
variable {common : List VExpr} {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {frontier : List (World strata.rules.length)}
  {outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType}
  (head : OriginalFactorCut.ProjectionHead outer)
  {field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel)}
  (fieldEq : head.field = .ref field)
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (majorLocation : Located (.right head.major) (.ref major))
  (controls : OriginalWorldControls strata sourceEnv)
  (captured : WorldEnvironmentProvenance strata U ownerInitial)
  (origin : ProjectionParameterOrigin sourceEnv name info)
  {signature : ConstantTelescope (origin.family.type.instL levels)}
  {domains : signature.domains = [C,D]}
  (destination : FormalFamilyDestination (U := U) origin signature domains)
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)


variable
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) (destination.nativeSide common))
  (sourceEnvironment : history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered = ownerInitial)
  (priorWorld : WorldEnvironmentProvenance strata U history.final)
  (priorReady : Sponsored [(originalCallWorld controls .assignedComparison outer captured)] priorWorld.worlds)
  (whole : history.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier)
  (wholeReady : Sponsored [(originalCallWorld controls .assignedComparison outer captured)] (history.whole.worldReserve whole.inputs).worlds)
  (boundary : history.whole.WorldBoundary whole.inputs controls (controls.atHeader origin.constructorOrigin)
    (transportWorld sourceEnvironment.symm captured) priorWorld)
  (coherent : boundary.FrameOccurrenceCoherent whole.controls whole.frames)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
    environmentCost (location.dependencyEnvironment ordered ownerInitial))
  (headerBelow : origin.types ≤ env)
  (sourceData : WorldBoundaryFrame.ExecutionData P base caps frontier
    ⟨history.sourceFrame.box, controls, transportWorld sourceEnvironment.symm captured⟩)
  (priorData : WorldBoundaryFrame.ExecutionData P base caps frontier
    ⟨history.headerFrame.box, (controls.atHeader origin.constructorOrigin), priorWorld⟩)

include initial domain body function argument result hu hv location graph origin destination
  fieldEq majorLocation priorReady wholeReady boundary coherent noBinders sourceBound headerBelow sourceEnvironment
  sourceData priorData in
/-- Execute the second empty capture from the SAME first selected capture.
The dependent domain route and all lower calls are computed from its history. -/
theorem FormalFamilyDestination.captureSecondArgumentWorld
    (selectedFrame : OriginalTypeRouteFrame env registry target (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)).graph commonLeft commonRight)
    (selected : WorldEnvironmentProvenance strata U
      (selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered))
    (selectedReady : Sponsored [(originalCallWorld controls .assignedComparison outer captured)] selected.worlds)
    (selectedData : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨selectedFrame.box, (controls.atHeader origin.constructorOrigin), selected⟩)
    (nextDomain : EndpointRef sourceEnv U source nextA (.sort nextU))
    (nextBody : EndpointState sourceEnv U (nextA :: source) nextB (.sort nextV))
    (nextFunction : EndpointState sourceEnv U source nextF (.forallE nextA nextB))
    (nextArgument : EndpointState sourceEnv U source nextArg nextA)
    (nextResult : EndpointState sourceEnv U source (nextB.inst nextArg) (.sort nextV))
    (nextHu : nextU.WF U) (nextHv : nextV.WF U)
    (nextLocation : Located major (.app nextHu nextHv (.ref nextDomain) nextBody nextFunction nextArgument nextResult))
    (nextGraph : OriginalCaptureMap (common := common) (nextLocation.contextDerivation initial) nextRaw)
    (nextFrame : OriginalTypeRouteFrame env registry target nextGraph commonLeft commonRight)
    (nextEnvironment : nextFrame.realization.frame.dependencyEnvironment controls.ordered = ownerInitial)
    (nextData : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨nextFrame.box, controls, transportWorld nextEnvironment.symm captured⟩)
    (adjacent : (VExpr.app f a).subst raw = nextF.subst nextRaw)
    (outerWorld : WorldEnvironmentProvenance strata U outerEnvironment)
    (sourceCapacity : environmentCost ownerInitial ≤ environmentCost outerEnvironment)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds outerWorld.worlds)
    (outerPaid : Sponsored frontier [originalCallWorld controls .assignedComparison outer outerWorld])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison outer outerWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison outer outerWorld])) :
    ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
      Sponsored [originalCallWorld controls .assignedComparison outer captured] reserve.worlds ∧
      Sponsored [originalCallWorld controls .assignedComparison outer outerWorld] reserve.worlds ∧
      Nonempty (WorldVariableDemandReply P base caps
        (.capture (destination.secondSide
          (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)).graph
          destination.secondDomain nextGraph nextArgument (.ofLocation (.appArgument nextLocation) initial))
        commonLeft commonRight (controls.atHeader origin.constructorOrigin) reserve frontier
        0 (Profile.empty : Profile 0)) := by
  obtain ⟨nextHistory, sourceEq, headerEq, domainEq, finalWorld, sameFinal, finalPaid,
      data, routePaid, nextSourceEnvironment, nextBoundary, nextCoherent⟩ :=
    destination.nextArgumentHistoryWorld head fieldEq majorLocation controls captured origin
      initial domain body function argument result hu hv location graph history sourceEnvironment
      priorWorld priorReady whole wholeReady boundary coherent noBinders sourceBound headerBelow sourceData priorData
      selectedFrame selected selectedReady selectedData nextDomain nextBody nextFunction nextArgument nextResult
      nextHu nextHv nextLocation nextGraph nextFrame nextEnvironment nextData adjacent
  rcases nextHistory with ⟨nextLeftOrdered, nextRightOrdered, nextBelow, nextRightDomain, nextRightDomainEq,
    nextSourceFrame, nextHeaderFrame, nextRoute⟩
  dsimp only at sourceEq headerEq domainEq sameFinal nextSourceEnvironment
  subst nextSourceFrame
  subst nextHeaderFrame
  subst nextRightDomain
  have finalEq : finalWorld = selected := eq_of_heq sameFinal
  subst finalWorld
  let next := originalApplicationTypeRouteSide initial nextDomain nextBody nextFunction nextArgument nextResult
    nextHu nextHv nextLocation nextGraph
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next
      (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)) :=
    ⟨nextLeftOrdered, nextRightOrdered, nextBelow, destination.secondDomain, rfl, nextFrame, selectedFrame, nextRoute⟩
  have nextNoBinders : nextLocation.binderPrefix = [] := Located.sameSource_prefix_nil nextLocation
  have nextEnvironmentAll : ∀ ordered, nextFrame.realization.frame.dependencyEnvironment ordered = ownerInitial :=
    fun _ => nextEnvironment
  have nextBound : ∀ ordered, environmentCost (nextFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (nextLocation.dependencyEnvironment ordered ownerInitial) := by
    intro ordered
    rw [nextEnvironmentAll, Located.dependencyEnvironment_of_prefix_nil ordered nextLocation nextNoBinders]
    exact Nat.le_refl _
  let sourceWorld := transportWorld nextEnvironment.symm captured
  have sourceWorlds : sourceWorld.worlds = captured.worlds := transportWorld_worlds _ _
  have sourceCall : originalCallWorld controls .assignedComparison outer sourceWorld =
      originalCallWorld controls .assignedComparison outer captured := by
    exact transportWorld_call _ _ _ _ _
  have paidOuter {worlds : List (World strata.rules.length)}
      (paid : Sponsored [originalCallWorld controls .assignedComparison outer captured] worlds) :
      Sponsored [originalCallWorld controls .assignedComparison outer outerWorld] worlds := by
    intro child member
    obtain ⟨parent, present, lower⟩ := paid child member
    cases List.mem_singleton.mp present
    exact ⟨_, List.mem_singleton_self _, originalCallWorld_retargetBelow controls outer .assignedComparison
      captured outerWorld sourceCapacity sourceCovered lower⟩
  have headerCompatible : selectedData.generation.UsesControlPrefix controls.cutoff controls.fuel :=
    selectedData.compatible
  obtain ⟨reserveEnvironment, reserve, paidLocal, paid, result⟩ := nextHistory.captureEmptyArgumentWorld
    initial nextDomain nextBody nextFunction nextArgument nextResult nextHu nextHv nextLocation nextGraph
    controls (controls.atHeader origin.constructorOrigin) frontier nextNoBinders nextBound
    nextData.generation selectedData.generation sourceWorld selected nextData.covered selectedData.covered
    nextData.replayable selectedData.replayable nextData.controlled selectedData.controlled
    nextData.hereditary selectedData.hereditary nextData.compatible headerCompatible
    data nextBoundary nextCoherent outer head field fieldEq majorLocation captured
    nextEnvironmentAll sourceWorlds outerWorld
    (by rw [nextEnvironment]; exact sourceCapacity)
    (by rw [sourceWorlds]; exact sourceCovered) (origin.types_count_lt controls.ordered)
    (paidOuter selectedReady) (paidOuter routePaid)
    (by simpa only [sourceCall] using selectedReady) (by simpa only [sourceCall] using routePaid)
    outerPaid henv hscoped formed bank unary
  exact ⟨reserveEnvironment, reserve, by simpa only [sourceCall] using paidLocal, paid, result⟩
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
