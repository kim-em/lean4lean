import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep

/-! Actual empty argument seeds transported through retained declaration-cell routes.
Every controlled occurrence, baseline, and hereditary frame is preserved. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly
open private nestedDisplay_heq RetainedHeaderUniverse.source_same trans_worldInputs trans_worldReserve
  environment_worlds_mpr from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
open private FramePacket sameData sameData_coherent transData transData_coherent table_cast_controls
  table_cast_worlds same_worlds finalTransport rightTransport environmentCast_worlds callWorld_cast
  environmentCast_heq boundary_world_coherent from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def PendingRichCapture.atDeclaration
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {headerAvailable : Valuation}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (nextDomain : EndpointRef nextEnv U nextSource nextA (.sort nextLevel))
    (nextLocals : List Nat) (nextLeft : Subst) (nextAvailable : Valuation) :
    PendingRichCapture (field := field) (major := major) nextDomain env registry target
      nextLocals nextLeft nextAvailable ownerInitial rawCapture leftValue rightValue where
  owner := pending.owner
  ownerLocals := pending.ownerLocals
  ownerLeft := pending.ownerLeft
  ownerRight := pending.ownerRight
  ownerAvailable := pending.ownerAvailable
  ownerClosed := pending.ownerClosed
  initialContext := pending.initialContext
  frame := pending.frame
  substitutions := pending.substitutions
  frame_environment_le := pending.frame_environment_le
  depth := pending.depth
  sourcePrefix := pending.sourcePrefix
  source_eq := pending.source_eq
  depth_eq := pending.depth_eq
  expression_eq := pending.expression_eq
  left_eq := pending.left_eq
  right_eq := pending.right_eq
  rank := pending.rank
  input := pending.input
  footprint := pending.footprint
  query := pending.query
  queryAvailable := pending.queryAvailable

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) right)

variable
  {nextContext : ContextDerivation nextEnv U nextSource}
  (nextGraph : OriginalCaptureMap (common := common) nextContext nextRaw)
  (nextDomain : EndpointRef nextEnv U nextSource nextA (.sort nextLevel))
  (nextProvenance : EndpointProvenance nextContext (.ref nextDomain))
  (nextOrdered : nextEnv.Ordered)
  {base : OriginalCaptureBase env U registry target}
  (nextFrame : OriginalTypeRouteFrame env registry target nextGraph commonLeft commonRight)

variable
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))

noncomputable def OriginalApplyPiHistory.emptyCellSeed :
    PendingRichCapture (field := field) (major := major) nextDomain env registry target
      nextFrame.locals (nextRaw.comp commonLeft) nextFrame.available ownerInitial
      a (a.subst (raw.comp commonLeft)) (a.subst (raw.comp commonRight)) :=
  (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound (.legacy (.legacy .empty) : RichObs sourceEnv env U registry target argument
      history.sourceFrame.locals (raw.comp commonLeft) (Profile.empty : Profile 0) [])
    (fun _ _ member => nomatch member)).atDeclaration nextDomain nextFrame.locals (nextRaw.comp commonLeft) nextFrame.available

noncomputable def OriginalApplyPiHistory.emptyCellScope :
    CappedOwnerScope common raw commonLeft commonRight commonCaps
      (history.emptyCellSeed (field := field) initial domain body function argument result hu hv location graph
        nextGraph nextDomain nextFrame noBinders sourceBound).depth
      ((history.emptyCellSeed (field := field) initial domain body function argument result hu hv location graph
        nextGraph nextDomain nextFrame noBinders sourceBound).owner.context initial) := {
  toOriginalOwnerScope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv
    location graph noBinders sourceBound (.legacy (.legacy .empty) : RichObs sourceEnv env U registry target argument
      history.sourceFrame.locals (raw.comp commonLeft) (Profile.empty : Profile 0) [])
    (fun _ _ member => nomatch member)
  caps := commonCaps
  capsTail := rfl }

theorem OriginalApplyPiHistory.argumentCellHistoryWorld
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (frontier : List (World strata.rules.length))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (sourceWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph
      history.sourceFrame.realization.frame.raw sourceControls)
    (sourceBaseline : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (headerBaseline : WorldEnvironmentProvenance strata U history.final)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) sourceWorld.worlds sourceBaseline.worlds)
    (sourceReplayable : sourceWorld.Replayable)
    (sourceReady : sourceWorld.Controlled frontier)
    (sourceHereditary : sourceWorld.Hereditary frontier)
    (sourceCompatible : sourceWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (whole : history.whole.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier)
    (wholeBoundary : history.whole.WorldBoundary whole.inputs sourceControls headerControls
      sourceBaseline headerBaseline)
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent whole.controls whole.frames) 
    (nextControls : OriginalWorldControls strata nextEnv)
    (nextWorld : WorldGenerated strata P base commonCaps commonLeft commonRight nextGraph
      nextFrame.realization.frame.raw nextControls)
    (nextBaseline : WorldEnvironmentProvenance strata U
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (nextCovered : Covered (@EquationControlMeasure.Less strata.rules.length) nextWorld.worlds nextBaseline.worlds)
    (nextReplayable : nextWorld.Replayable)
    (nextReady : nextWorld.Controlled frontier)
    (nextHereditary : nextWorld.Hereditary frontier)
    (nextCompatible : nextWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (cells : RawGeneratedTypeRoute env registry target commonLeft commonRight right.domainDisplay
      (nextGraph.parameterCellDisplay nextDomain nextProvenance) history.final
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (cellsData : cells.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier)
    (cellsBoundary : cells.WorldBoundary cellsData.inputs headerControls nextControls headerBaseline nextBaseline)
    (cellsCoherent : cellsBoundary.FrameOccurrenceCoherent cellsData.controls cellsData.frames) :
    ∃ next : OriginalSeedTypeHistory
        (history.emptyCellSeed (field := field) initial domain body function argument result hu hv location graph
          nextGraph nextDomain nextFrame noBinders sourceBound)
        (history.emptyCellScope (field := field) (commonCaps := commonCaps) initial domain body function argument result hu hv location graph
          nextGraph nextDomain nextFrame noBinders sourceBound).toOriginalOwnerScope
        nextGraph nextProvenance nextFrame.realization history.leftOrdered nextOrdered,
      ∃ data : next.route.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier,
        next.route.reserve = (history.argumentDomainRoute.reserve ++ cells.reserve) ++
          [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
              (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
            (.close (nextDomain.dependencyOrigin nextOrdered)
              (nextFrame.realization.frame.dependencyEnvironment nextOrdered))] ∧
        (next.route.worldReserve data.inputs).worlds =
          [originalCallWorld sourceControls .expressionReindex argument.typeFormation.node sourceBaseline,
           originalCallWorld sourceControls .expressionReindex (.ref domain) sourceBaseline] ++
          (history.whole.worldReserve whole.inputs).worlds ++
          (cells.worldReserve cellsData.inputs).worlds ++
          [originalCallWorld nextControls .expressionReindex (.ref nextDomain) nextBaseline,
           originalCallWorld nextControls .expressionReindex (.ref nextDomain) nextBaseline] ∧
        ∃ boundary : next.route.WorldBoundary data.inputs sourceControls nextControls
            sourceBaseline nextBaseline,
          boundary.FrameOccurrenceCoherent data.controls data.frames := by
  let seed := history.emptyCellSeed (field := field) initial domain body function argument result hu hv location graph
    nextGraph nextDomain nextFrame noBinders sourceBound
  let scope := history.emptyCellScope (field := field) (commonCaps := commonCaps) initial domain body function argument result hu hv location graph
    nextGraph nextDomain nextFrame noBinders sourceBound
  let weakening : WorldGenerated strata P base commonCaps commonLeft commonRight (.weaken nextGraph (.refl (Γ := common)))
      nextFrame.realization.frame.raw nextControls := .weaken nextWorld .refl rfl rfl rfl
  have weakReady : weakening.Controlled frontier :=
    ⟨nextReady.annotation, nextReady.within, nextReady.sponsored⟩
  have weakCompatible : weakening.UsesControlPrefix sourceControls.cutoff sourceControls.fuel := nextCompatible
  have headerPrefix := nextCompatible.controls_match
  have weakOwnCompatible : weakening.UsesControlPrefix nextControls.cutoff nextControls.fuel := by
    rw [headerPrefix.1, headerPrefix.2]
    exact weakCompatible
  obtain ⟨header, headerActual, nextWorlds, ⟨headerActualReady⟩, _nextCompatible, environmentEq, _replayableEq, headerAnnotationEq, ⟨headerActualHereditary⟩⟩ :=
    realizeWorld nextFrame.realization.frame weakening weakReady weakOwnCompatible
      (nextHereditary.weaken .refl rfl rfl rfl)
      nextFrame.realization.substitutions
  let destination : OriginalNestedDisplay U common (nextA.subst nextRaw) (.sort nextLevel) := {
    sourceEnv := nextEnv, source := nextSource, sourceExpression := nextA, sourceType := .sort nextLevel
    context := nextContext, node := .ref nextDomain
    provenance := nextProvenance, raw := nextRaw.lift_r .refl
    graph := .weaken nextGraph .refl
    expression_eq := by rw [← lift'_subst, lift'_refl]
    type_eq := rfl }
  let destinationFrame : OriginalTypeRouteFrame env registry target destination.graph commonLeft commonRight :=
    ⟨nextFrame.locals, nextFrame.available, header, nextFrame.closed⟩
  let destinationBaseline : WorldEnvironmentProvenance strata U
      (destinationFrame.realization.frame.dependencyEnvironment nextOrdered) :=
    (environmentEq nextOrdered).symm ▸ nextBaseline
  have destinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      headerActual.worlds destinationBaseline.worlds := by
    rw [show destinationBaseline.worlds = nextBaseline.worlds from
      environmentCast_worlds (environmentEq nextOrdered).symm nextBaseline, nextWorlds]
    exact nextCovered
  let left := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
  let first := RawGeneratedTypeRoute.same left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) history.sourceFrame
  have firstGenerated : first.SourceGenerated P base commonCaps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _
      sourceWorld.erase.ambientGenerated.ambient.2.below sourceWorld.erase.ambientGenerated.ambient.2.below
      sourceWorld.erase.sources.1.source sourceWorld.erase.sources.1.source sourceWorld.erase
  let firstData := sameData left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered _ history.sourceFrame
    sourceControls sourceControls sourceBaseline sourceBaseline sourceWorld sourceReady sourceCompatible sourceReplayable sourceHereditary sourceCovered firstGenerated
  let firstBoundary := RawGeneratedTypeRoute.WorldBoundary.same left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered history.sourceFrame sourceControls sourceControls
    sourceBaseline sourceBaseline ⟨rfl, rfl⟩
  have firstCoherent : firstBoundary.FrameOccurrenceCoherent firstData.controls firstData.frames :=
    sameData_coherent left.argumentDisplay.formationDisplay left.pi.domainDisplay
      history.leftOrdered history.leftOrdered _ history.sourceFrame sourceControls sourceControls
      sourceBaseline sourceBaseline sourceWorld sourceReady sourceCompatible sourceReplayable sourceHereditary sourceCovered firstGenerated ⟨rfl, rfl⟩
  let middle := RawGeneratedTypeRoute.piDomain left.pi right history.leftBelow history.whole
  have middleGenerated : middle.SourceGenerated P base commonCaps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; exact whole.generated.wellFormed
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact whole.generated.ambient
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨whole.generated.sources.left, whole.generated.sources.right, whole.generated.sources⟩
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.frames.eq_def]; exact whole.generated.frames
  have middleFrames : middle.frames = history.whole.frames := by
    dsimp only [middle]; rw [RawGeneratedTypeRoute.frames.eq_def]
  let Packet := FramePacket (common := common) (commonLeft := commonLeft) (commonRight := commonRight)
    P base commonCaps sourceControls.cutoff sourceControls.fuel frontier
  let oldEntries : ∀ i : Fin history.whole.frames.length, Packet (history.whole.frames[i]) :=
    fun i => ⟨whole.controls i, whole.frames i, whole.ready i, ⟨whole.compatible i⟩, ⟨whole.replayable i⟩, whole.hereditary i⟩
  let entries : ∀ i : Fin middle.frames.length, Packet (middle.frames[i]) :=
    (congrArg (fun frames => ∀ i : Fin frames.length, Packet (frames[i])) middleFrames).mpr oldEntries
  let middleData : middle.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier :=
    ⟨middleGenerated, whole.inputs,
      fun i => (entries i).1,
      fun i => (entries i).2.1,
      fun i => (entries i).2.2.1,
      fun i => (entries i).2.2.2.1.down,
      fun i => (entries i).2.2.2.2.1.down,
      fun i => (entries i).2.2.2.2.2⟩

  let middleBoundary := RawGeneratedTypeRoute.WorldBoundary.piDomain left.pi right history.leftBelow wholeBoundary
  have middleCoherent : middleBoundary.FrameOccurrenceCoherent middleData.controls middleData.frames := by
    intro index
    let oldIndex := Fin.cast (congrArg List.length middleFrames) index
    have sameOccurrence : middleBoundary.frameAt index = wholeBoundary.frameAt oldIndex := by
      unfold RawGeneratedTypeRoute.WorldBoundary.frameAt
      rfl
    have controlsEq : HEq (middleData.controls index) (whole.controls oldIndex) :=
      table_cast_controls middleFrames oldEntries index
    have worldsEq : (middleData.frames index).worlds = (whole.frames oldIndex).worlds :=
      table_cast_worlds middleFrames oldEntries index
    let predicate := fun occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata =>
      HEq (middleData.controls index) occurrence.controls ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) (middleData.frames index).worlds occurrence.world.worlds
    apply (congrArg predicate sameOccurrence).mpr
    refine ⟨controlsEq.trans (wholeCoherent oldIndex).1, ?_⟩
    rw [worldsEq]
    exact (wholeCoherent oldIndex).2

  let last := RawGeneratedTypeRoute.same (nextGraph.parameterCellDisplay nextDomain nextProvenance) destination nextOrdered nextOrdered
    (nextFrame.realization.frame.dependencyEnvironment nextOrdered) destinationFrame
  have lastGenerated : last.SourceGenerated P base commonCaps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _
      nextWorld.erase.ambientGenerated.ambient.2.below headerActual.erase.ambientGenerated.ambient.2.below
      nextWorld.erase.sources.1.source headerActual.erase.sources.1.source headerActual.erase
  have headerActualCompatible : headerActual.UsesControlPrefix sourceControls.cutoff sourceControls.fuel := by
    have same := nextCompatible.controls_match
    simpa only [same.1, same.2] using _nextCompatible
  let lastData := sameData (nextGraph.parameterCellDisplay nextDomain nextProvenance) destination
    nextOrdered nextOrdered _ destinationFrame
    nextControls nextControls nextBaseline destinationBaseline headerActual headerActualReady headerActualCompatible
      (_replayableEq.mpr nextReplayable) headerActualHereditary destinationCovered lastGenerated
  let combined := ((first.trans middle).trans cells).trans last
  let data := transData (transData (transData firstData middleData) cellsData) lastData
  let lastBoundary := RawGeneratedTypeRoute.WorldBoundary.same (nextGraph.parameterCellDisplay nextDomain nextProvenance) destination
    nextOrdered nextOrdered destinationFrame nextControls nextControls
    nextBaseline destinationBaseline ⟨rfl, rfl⟩
  have lastCoherent : lastBoundary.FrameOccurrenceCoherent lastData.controls lastData.frames :=
    sameData_coherent (nextGraph.parameterCellDisplay nextDomain nextProvenance) destination nextOrdered nextOrdered _ destinationFrame
      nextControls nextControls nextBaseline destinationBaseline headerActual headerActualReady headerActualCompatible
      (_replayableEq.mpr nextReplayable) headerActualHereditary destinationCovered lastGenerated ⟨rfl, rfl⟩
  let combinedBoundary := ((firstBoundary.trans middleBoundary).trans cellsBoundary).trans lastBoundary
  have combinedCoherent : combinedBoundary.FrameOccurrenceCoherent data.controls data.frames :=
    transData_coherent (transData (transData firstData middleData) cellsData) lastData _ _
      (transData_coherent (transData firstData middleData) cellsData _ _
        (transData_coherent firstData middleData _ _ firstCoherent middleCoherent) cellsCoherent) lastCoherent
  have reserveEq : combined.reserve = (history.argumentDomainRoute.reserve ++ cells.reserve) ++
      [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
          (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
        (.close (nextDomain.dependencyOrigin nextOrdered)
          (nextFrame.realization.frame.dependencyEnvironment nextOrdered))] := by
    change ((history.argumentDomainRoute.trans cells).trans last).reserve = _
    rw [RawGeneratedTypeRoute.reserve.eq_def ((history.argumentDomainRoute.trans cells).trans last)]
    change (history.argumentDomainRoute.trans cells).reserve ++ last.reserve = _
    rw [RawGeneratedTypeRoute.reserve.eq_def (history.argumentDomainRoute.trans cells)]
    change (history.argumentDomainRoute.reserve ++ cells.reserve) ++ last.reserve = _
    congr 1
    rw [RawGeneratedTypeRoute.reserve.eq_def last]
    simp only [last, destinationFrame, destination, OriginalCaptureMap.parameterCellDisplay,
      EndpointState.dependencyOrigin]
    rw [environmentEq nextOrdered]
  have worldsEq : (combined.worldReserve data.inputs).worlds =
      [originalCallWorld sourceControls .expressionReindex argument.typeFormation.node sourceBaseline,
       originalCallWorld sourceControls .expressionReindex (.ref domain) sourceBaseline] ++
      (history.whole.worldReserve whole.inputs).worlds ++
      (cells.worldReserve cellsData.inputs).worlds ++
      [originalCallWorld nextControls .expressionReindex (.ref nextDomain) nextBaseline,
       originalCallWorld nextControls .expressionReindex (.ref nextDomain) nextBaseline] := by
    change (((first.trans middle).trans cells).trans last |>.worldReserve (trans_worldInputs
      (trans_worldInputs (trans_worldInputs firstData.inputs middleData.inputs) cellsData.inputs) lastData.inputs)).worlds = _
    rw [trans_worldReserve, trans_worldReserve, trans_worldReserve]
    rw [show (middle.worldReserve middleData.inputs).worlds = (history.whole.worldReserve whole.inputs).worlds by
      simp only [middle, middleData, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
      rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def middle)]
      rfl]
    change (first.worldReserve (sourceControls, sourceControls, sourceBaseline, sourceBaseline)).worlds ++
      (history.whole.worldReserve whole.inputs).worlds ++
      (cells.worldReserve cellsData.inputs).worlds ++
      (last.worldReserve (nextControls, nextControls, nextBaseline, destinationBaseline)).worlds = _
    rw [same_worlds, same_worlds]
    have lastWorldEq : originalCallWorld nextControls .expressionReindex (.ref nextDomain)
        destinationBaseline = originalCallWorld nextControls .expressionReindex
          (.ref nextDomain) nextBaseline :=
      callWorld_cast nextControls .expressionReindex (.ref nextDomain)
        (environmentEq nextOrdered).symm nextBaseline
    change _ ++ _ ++ [_, originalCallWorld nextControls .expressionReindex _ destinationBaseline] = _
    rw [lastWorldEq]
    rfl
  have finalEq : header.frame.dependencyEnvironment nextOrdered = (nextFrame.realization.frame.dependencyEnvironment nextOrdered) := environmentEq nextOrdered
  obtain ⟨route, routeData, exactReserve, sameWorlds, routeBoundary, routeCoherent⟩ :=
    finalTransport combined data combinedBoundary combinedCoherent finalEq
  have finalWorldEq : (finalEq ▸ destinationBaseline : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment nextOrdered)) = nextBaseline :=
    eq_of_heq ((environmentCast_heq finalEq destinationBaseline).trans
      (environmentCast_heq finalEq.symm nextBaseline))
  let routeBoundary' : route.WorldBoundary routeData.inputs sourceControls nextControls
      sourceBaseline nextBaseline := finalWorldEq ▸ routeBoundary
  have routeCoherent' : routeBoundary'.FrameOccurrenceCoherent routeData.controls routeData.frames :=
    boundary_world_coherent routeData routeBoundary routeCoherent finalWorldEq
  have endpointEq : HEq destination (scope.toOriginalOwnerScope.declaredTypeDisplay nextGraph nextProvenance) := by
    dsimp only [destination, scope, OriginalApplyPiHistory.emptyCellScope, OriginalApplyPiHistory.argumentSeedScope,
      OriginalOwnerScope.declaredTypeDisplay, seed, OriginalApplyPiHistory.emptyCellSeed,
      PendingRichCapture.atDeclaration, OriginalApplyPiHistory.argumentSeed, Lift.skipN]
    exact nestedDisplay_heq _ _ _ _ _ _ _
  obtain ⟨nextRoute, nextData, nextReserve, nextWorlds, nextBoundary, nextCoherent⟩ :=
    rightTransport route routeData routeBoundary' routeCoherent' lift'_refl.symm endpointEq rfl
  exact ⟨⟨nextRoute⟩, nextData, nextReserve.trans (exactReserve.trans reserveEq),
    nextWorlds.trans (sameWorlds.trans worldsEq), nextBoundary, nextCoherent⟩
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
