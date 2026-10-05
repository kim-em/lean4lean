import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySelectedPiExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyDestination

/-! A concrete second header at the genuine installed family declaration.
The selected first capture is retained verbatim; a same-expression original
route exposes the second Pi without changing its domain proof or capture map. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportWorld transportWorld_call transportWorld_worlds descendant_below same_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private trans_worldInputs trans_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
open private composeExecution from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySelectedPiExecution
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option quotPrecheck false

noncomputable def FormalFamilyDestination.secondSide
    {origin : ProjectionParameterOrigin sourceEnv name info}
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (left : OriginalApplicationTypeRouteSide U common) : OriginalPiTypeRouteSide U common where
  sourceEnv := origin.types
  source := [C]
  A := D
  B := signature.result
  u := destination.secondLevel
  v := destination.resultLevel
  hu := destination.secondLevelWF
  hv := destination.resultLevelWF
  domain := .ref destination.secondDomain
  body := .ref destination.resultFormation
  rootSource := [C]
  rootExpression := .forallE D signature.result
  rootType := .sort (.imax destination.secondLevel destination.resultLevel)
  root := .left destination.bodyOriginal
  initial := .cons .nil destination.firstDomain
  location := .expose .here
  raw := Subst.id.cons (left.a.subst left.raw)
  graph := .capture (destination.nativeSide common).graph destination.firstDomain left.graph left.argument
    (.ofLocation (.appArgument left.location) left.initial)

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
/-- The first selected capture supplies the actual next header frame. The
successor targets the formal second domain original directly. -/
theorem FormalFamilyDestination.nextArgumentHistoryWorld
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
    (adjacent : (VExpr.app f a).subst raw = nextF.subst nextRaw) :
    let next := originalApplicationTypeRouteSide initial nextDomain nextBody nextFunction nextArgument nextResult
      nextHu nextHv nextLocation nextGraph
    ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)),
      nextHistory.sourceFrame = nextFrame ∧ nextHistory.headerFrame = selectedFrame ∧
      nextHistory.rightDomain = destination.secondDomain ∧
      ∃ finalWorld : WorldEnvironmentProvenance strata U nextHistory.final,
        HEq finalWorld selected ∧ Sponsored [(originalCallWorld controls .assignedComparison outer captured)] finalWorld.worlds ∧
        ∃ data : nextHistory.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
          Sponsored [(originalCallWorld controls .assignedComparison outer captured)] (nextHistory.whole.worldReserve data.inputs).worlds ∧
          ∃ nextSourceEnvironment : nextHistory.sourceFrame.realization.frame.dependencyEnvironment nextHistory.leftOrdered = ownerInitial,
          ∃ nextBoundary : nextHistory.whole.WorldBoundary data.inputs controls (controls.atHeader origin.constructorOrigin)
            (transportWorld nextSourceEnvironment.symm captured) finalWorld,
            nextBoundary.FrameOccurrenceCoherent data.controls data.frames := by
  have initialDomain : history.rightDomain = destination.firstDomain := (EndpointState.ref.inj history.rightDomainEq).symm
  rcases history with ⟨leftOrdered, rightOrdered, leftBelow, rightDomain, rightDomainEq, sourceFrame, headerFrame, historyRoute⟩
  have domainEq : rightDomain = destination.firstDomain := initialDomain
  subst rightDomain
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) (destination.nativeSide common) :=
    ⟨leftOrdered, rightOrdered, leftBelow, destination.firstDomain, rfl, sourceFrame, headerFrame, historyRoute⟩
  let wholeFrames := RawGeneratedTypeRoute.WorldBoundary.executionFramesOfData whole boundary coherent
  obtain ⟨completed, completedGenerated, _completedReserve, completedInputs, completedReady,
      completedBoundary, ⟨completedFrames⟩⟩ :=
    history.generatedSelectedSuccessorWorldExecution (sourceData := sourceData) (priorData := priorData) (wholeFrames := wholeFrames)
      head fieldEq majorLocation controls captured origin.constructorOrigin initial domain body function argument result
      hu hv location graph .nil destination.firstDomain destination.nativeBody destination.firstLevelWF
      ⟨destination.secondLevelWF, destination.resultLevelWF⟩
      (show Located (.left destination.headerOriginal) destination.nativeHeader from .expose .here)
      (closedCaptureGraph .nil common)
      sourceEnvironment priorWorld priorReady whole.inputs wholeReady boundary noBinders sourceBound headerBelow
      whole.generated selectedFrame selected selectedReady selectedData
  let next := originalApplicationTypeRouteSide initial nextDomain nextBody nextFunction nextArgument nextResult
    nextHu nextHv nextLocation nextGraph
  let nextWorldSource := transportWorld nextEnvironment.symm captured
  let sourceWorld := transportWorld sourceEnvironment.symm captured
  let predecessor := next.predecessorRoute (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) adjacent controls.ordered history.leftOrdered nextFrame history.sourceFrame
  let predecessorInputs := next.predecessorWorldInputs (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) adjacent controls.ordered history.leftOrdered nextFrame
    history.sourceFrame controls controls nextWorldSource sourceWorld
  have predecessorGenerated := next.predecessorRoute_ambientGenerated (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) adjacent controls.ordered history.leftOrdered
    nextFrame history.sourceFrame nextData.generation.erase.ambientGenerated sourceData.generation.erase.ambientGenerated
  have predecessorSource : predecessor.SourceGenerated P base caps := by
    refine ⟨predecessorGenerated.wellFormed, predecessorGenerated.ambient, ?_, ?_⟩
    · simp only [predecessor, OriginalApplicationTypeRouteSide.predecessorRoute,
        OriginalApplicationTypeRouteSide.resultFromAssignedRoute, RawGeneratedTypeRoute.AllSources.eq_def]
      have sourceP := sourceData.generation.erase.sources.1.source
      exact ⟨sourceP, sourceP, ⟨sourceP, sourceP, trivial⟩,
        ⟨sourceP, sourceP, ⟨sourceP, sourceP, trivial⟩, ⟨sourceP, sourceP, trivial⟩⟩⟩
    · intro boxed member
      simp only [predecessor, OriginalApplicationTypeRouteSide.predecessorRoute,
        OriginalApplicationTypeRouteSide.resultFromAssignedRoute, RawGeneratedTypeRoute.frames.eq_def,
        List.mem_append, List.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · exact nextData.generation.erase
      · exact sourceData.generation.erase
      · exact sourceData.generation.erase
  have predecessorReady : Sponsored [(originalCallWorld controls .assignedComparison outer captured)] (predecessor.worldReserve predecessorInputs).worlds := by
    rw [next.predecessorWorldInputs_worlds]
    intro child member
    simp only [nextWorldSource, sourceWorld, transportWorld_call, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appPiFormation nextLocation) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.assignedFormation (.appFunction nextLocation)) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appFunction nextLocation) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation location controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.assignedFormation location) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appResult location) controls captured _ _⟩
  let exposeHeader := RawGeneratedTypeRoute.same history.destination (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)).display
    rightOrdered rightOrdered (selectedFrame.realization.frame.dependencyEnvironment rightOrdered) selectedFrame
  let exposeInputs : exposeHeader.WorldInputs strata := ((controls.atHeader origin.constructorOrigin), (controls.atHeader origin.constructorOrigin), selected, selected)
  let exposeBoundary : exposeHeader.WorldBoundary exposeInputs (controls.atHeader origin.constructorOrigin) (controls.atHeader origin.constructorOrigin) selected selected :=
    .same _ _ _ _ _ _ _ _ _ ⟨rfl,rfl⟩
  have exposeGenerated : exposeHeader.SourceGenerated P base caps :=
    RetainedHeaderUniverse.sourceGenerated_same _ _ rfl _ _ _ _ headerBelow headerBelow
      selectedData.generation.erase.sources.1.source selectedData.generation.erase.sources.1.source
      selectedData.generation.erase
  have exposeFrames : exposeBoundary.ExecutionFrames P base caps frontier := by
    intro occurrence member
    change occurrence ∈ [⟨selectedFrame.box, (controls.atHeader origin.constructorOrigin), selected⟩] at member
    cases List.mem_singleton.mp member
    exact selectedData
  have exposeReady : Sponsored [(originalCallWorld controls .assignedComparison outer captured)] (exposeHeader.worldReserve exposeInputs).worlds := by
    rw [same_worldReserve]
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin.constructorOrigin
        history.destination.node selected outer captured _ _ selectedReady⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin.constructorOrigin
        (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)).display.node selected outer captured _ _ selectedReady⟩
  let fullRoute := (predecessor.trans completed).trans exposeHeader
  have fullGenerated := RetainedHeaderUniverse.sourceGenerated_trans
    (RetainedHeaderUniverse.sourceGenerated_trans predecessorSource completedGenerated) exposeGenerated
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next (destination.secondSide (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)) :=
    ⟨controls.ordered, rightOrdered, leftBelow, destination.secondDomain, rfl, nextFrame, selectedFrame, fullRoute⟩
  let predecessorBoundary := next.predecessorWorldInputs_boundary (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) adjacent controls.ordered history.leftOrdered
    nextFrame history.sourceFrame controls controls nextWorldSource sourceWorld ⟨rfl,rfl⟩
  let predecessorFrames := next.predecessorSelectedWorldExecution (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) adjacent controls.ordered history.leftOrdered
    nextFrame history.sourceFrame controls controls nextWorldSource sourceWorld ⟨rfl,rfl⟩ nextData sourceData
  let nextBoundary := (predecessorBoundary.trans completedBoundary).trans exposeBoundary
  let execution := composeExecution (predecessorBoundary.trans completedBoundary) exposeBoundary
    (composeExecution predecessorBoundary completedBoundary predecessorFrames completedFrames) exposeFrames
  let data := nextBoundary.controlledDataOfExecution fullGenerated execution
  refine ⟨nextHistory, rfl, rfl, rfl, selected, HEq.rfl, selectedReady, data, ?_,
    nextEnvironment, nextBoundary, nextBoundary.controlledDataOfExecution_coherent fullGenerated execution⟩
  change Sponsored [(originalCallWorld controls .assignedComparison outer captured)]
    (((predecessor.trans completed).trans exposeHeader).worldReserve
      (trans_worldInputs (trans_worldInputs predecessorInputs completedInputs) exposeInputs)).worlds
  rw [trans_worldReserve, trans_worldReserve]
  exact (predecessorReady.merge completedReady).merge exposeReady
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
