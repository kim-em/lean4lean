import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChainLedger

/-! The counted successor preserves actual hereditary ambient generation
on all retained source, header, and historical frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
open private chainChargedTrans from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChainLedger
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

theorem OriginalNestedDisplay.nativePiCursorAmbient_counted
    (display : OriginalNestedDisplay U common expression assigned)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.realization.frame.raw)
    (below : display.sourceEnv ≤ env)
    (occurrence : ParameterRouteOccurrence sources ordered display.node)
    (ledger : ParameterRouteLedger sources ownerInitial count (frame.realization.frame.dependencyEnvironment ordered)) :
    ∃ side : OriginalPiTypeRouteSide U common,
      ∃ sideOrdered : side.sourceEnv.Ordered,
      ∃ nextFrame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight display side.display
          (frame.realization.frame.dependencyEnvironment ordered)
          (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
        route.AmbientGenerated base commonCaps ∧
        side.sourceEnv = display.sourceEnv ∧
        side.A = A ∧ side.B = B ∧ side.raw = display.raw ∧
        AmbientCaptureGenerated base commonCaps commonLeft commonRight side.graph nextFrame.realization.frame.raw ∧
        nextFrame.realization.frame.dependencyEnvironment sideOrdered = frame.realization.frame.dependencyEnvironment ordered ∧
        Nonempty (route.Charged sources ownerInitial count) ∧
        Nonempty (ParameterRouteOccurrence sources sideOrdered side.display.node) ∧
        Nonempty (ParameterRouteLedger sources ownerInitial count (nextFrame.realization.frame.dependencyEnvironment sideOrdered)) ∧
        ∃ domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u), side.domain = .ref domain := by
  rcases display with ⟨sourceEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at shape ordered frame generated below occurrence ledger ⊢
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  let side := nativeHeaderSide initial start graph
  let nextFrame := nativeHeaderFrame initial start graph frame
  have nextOccurrence : ParameterRouteOccurrence sources ordered side.display.node :=
    occurrence.route (piPrefix start).route
  have frameEq := nativeHeaderFrame_environment initial start graph frame ordered
  have nextLedger : ParameterRouteLedger sources ownerInitial count
      (nextFrame.realization.frame.dependencyEnvironment ordered) := by
    rw [frameEq]
    exact ledger
  have charged : (nativeHeaderRoute initial start graph frame ordered).Charged sources ownerInitial count := by
    rw [nativeHeaderRoute, RawGeneratedTypeRoute.Charged.eq_def]
    exact .reindex occurrence nextOccurrence ledger nextLedger
  refine ⟨side, ordered, nextFrame, nativeHeaderRoute initial start graph frame ordered,
    nativeHeaderRoute_ambientGenerated initial start graph frame ordered generated,
    rfl, rfl, rfl, rfl, nativeHeaderFrame_ambientGenerated initial start graph frame generated,
    frameEq, ⟨charged⟩, ⟨nextOccurrence⟩, ⟨nextLedger⟩, ?_⟩
  exact (piPrefix start).view.location.originalDomains.1

section
variable {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {commonLeft commonRight : Subst}
variable
  (sources : ParameterRouteSources sourceEnv U)
  (initial : ContextDerivation sourceEnv U sources.source)
  (domain : EndpointRef sourceEnv U sources.source A (.sort u))
  (body : EndpointState sourceEnv U (A :: sources.source) B (.sort v))
  (function : EndpointState sourceEnv U sources.source f (.forallE A B))
  (argument : EndpointState sourceEnv U sources.source a A)
  (result : EndpointState sourceEnv U sources.source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located sources.major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

/-- The next query-selected header frame and all five connecting R/C edges
are paid at the successor prefix. Every source charge comes from the two
actual application occurrences; every header charge comes from its retained
installation occurrence and the produced capture ledger. -/
theorem OriginalApplyPiHistory.nextParameterAmbient_counted
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = []) (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.AmbientGenerated base commonCaps)
    (replayed : AmbientApplyPiReplayResult history sources.field sources.major ownerInitial base commonCaps profile)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (headerOccurrence : ParameterRouteOccurrence sources history.rightOrdered (headerSide).display.node)
    (prefixLedger : ParameterRouteLedger sources ownerInitial count history.final)
    (nextDomainRef : EndpointRef sourceEnv U sources.source nextA (.sort nextU))
    (nextBodyNode : EndpointState sourceEnv U (nextA :: sources.source) nextB (.sort nextV))
    (nextFunction : EndpointState sourceEnv U sources.source nextF (.forallE nextA nextB))
    (nextArgument : EndpointState sourceEnv U sources.source nextArg nextA)
    (nextResult : EndpointState sourceEnv U sources.source (nextB.inst nextArg) (.sort nextV))
    (nextHu : nextU.WF U) (nextHv : nextV.WF U)
    (nextLocation : Located sources.major
      (.app nextHu nextHv (.ref nextDomainRef) nextBodyNode nextFunction nextArgument nextResult))
    (nextGraph : OriginalCaptureMap (common := common) (nextLocation.contextDerivation initial) nextRaw)
    (nextFrame : OriginalTypeRouteFrame env registry target nextGraph commonLeft commonRight)
    (nextGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight nextGraph nextFrame.realization.frame.raw)
    (nextBound : environmentCost (nextFrame.realization.frame.dependencyEnvironment sources.ordered) ≤
      environmentCost (nextLocation.dependencyEnvironment sources.ordered ownerInitial))
    (adjacent : (VExpr.app f a).subst sourceRaw = nextF.subst nextRaw)
    (headerShape : D = .forallE nextHeaderDomain nextHeaderBody) :
    let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
      nextResult nextHu nextHv nextLocation nextGraph
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.AmbientGenerated base commonCaps ∧
        nextHistory.sourceFrame = nextFrame ∧
        nextHeader.sourceEnv = headerEnv ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.A = nextHeaderDomain ∧ nextHeader.B = nextHeaderBody ∧
        nextHeader.raw = headerRaw.cons (a.subst sourceRaw) ∧
        Nonempty (nextHistory.whole.Charged sources ownerInitial (count + 1)) ∧
        Nonempty (ParameterRouteOccurrence sources nextHistory.rightOrdered nextHeader.display.node) ∧
        Nonempty (ParameterRouteLedger sources ownerInitial (count + 1) nextHistory.final) := by
  let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
    nextResult nextHu nextHv nextLocation nextGraph
  have domainEq : history.rightDomain = headerDomain := (EndpointState.ref.inj history.rightDomainEq).symm
  have domainOccurrence : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain) := by
    rw [domainEq]
    exact headerOccurrence.piDomain
  have successor := history.applyRoute_successorLedger sources initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound
    headerBelow wholeCharged headerOccurrence domainOccurrence prefixLedger
  have outputLedger : ParameterRouteLedger sources ownerInitial (count + 1)
      (history.outputEnvironment sources.field sources.major ownerInitial) := by
    simpa only [OriginalApplyPiHistory.outputEnvironment, domainEq] using successor.2
  have capturedLedger : ParameterRouteLedger sources ownerInitial (count + 1)
      (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered) :=
    .bounded outputLedger _ (replayed.toOriginalApplyPiReplayResult.environment_bound history.rightOrdered)
  have bodyOccurrence : ParameterRouteOccurrence sources history.rightOrdered history.destination.node :=
    headerOccurrence.piBody
  obtain ⟨completed, completedGenerated, completedReserve⟩ := history.generatedSuccessorAmbient
    (field := sources.field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound
    headerBelow generated replayed
  have completedCharged : completed.Charged sources ownerInitial (count + 1) := by
    apply completed.chargedOfReserve
    rw [completedReserve]
    have applied := (RawGeneratedTypeRoute.chargedReserve _ successor.1)
    rw [history.applyRoute_reserve (field := sources.field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow] at applied
    exact applied.append (.cons (.reindex bodyOccurrence bodyOccurrence outputLedger capturedLedger) .nil)
  obtain ⟨nextHeader, nextHeaderOrdered, nextHeaderFrame, exposeHeader, exposeGenerated,
      headerSource, headerDomainShape, headerBodyShape, headerRawShape, headerGenerated, headerFrameEq,
      ⟨exposeCharged⟩, ⟨nextHeaderOccurrence⟩, ⟨nextLedger⟩, nextDomainOriginal, nextDomainEq⟩ :=
    history.destination.nativePiCursorAmbient_counted headerShape history.rightOrdered replayed.captureFrame
      replayed.generation headerBelow bodyOccurrence capturedLedger
  let predecessor := next.predecessorRoute sourceSide adjacent sources.ordered history.leftOrdered nextFrame history.sourceFrame
  have predecessorGenerated := next.predecessorRoute_ambientGenerated sourceSide adjacent sources.ordered history.leftOrdered
    nextFrame history.sourceFrame nextGenerated generated.source
  have predecessorCharged : predecessor.Charged sources ownerInitial (count + 1) := by
    change (next.predecessorRoute sourceSide adjacent sources.ordered history.leftOrdered nextFrame history.sourceFrame).Charged _ _ _
    rw [OriginalApplicationTypeRouteSide.predecessorRoute, RawGeneratedTypeRoute.Charged.eq_def]
    refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.Charged.eq_def]
      exact .ownerPair (.major (.appPiFormation nextLocation))
        (.major (.assignedFormation (.appFunction nextLocation))) _ _ nextBound nextBound
    · apply OriginalApplicationTypeRouteSide.resultFromAssignedRoute_charged
      · exact .ownerPair (.major (.appFunction nextLocation)) (.major location) _ _
          nextBound (sourceBound sources.ordered)
      · exact .ownerPair (.major (.assignedFormation location)) (.major (.appResult location)) _ _
          (sourceBound sources.ordered) (sourceBound sources.ordered)
  let whole := (predecessor.trans completed).trans exposeHeader
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader :=
    ⟨sources.ordered, nextHeaderOrdered, history.leftBelow, nextDomainOriginal, nextDomainEq,
      nextFrame, nextHeaderFrame, whole⟩
  have wholeGenerated : whole.AmbientGenerated base commonCaps :=
    (predecessorGenerated.trans completedGenerated).trans exposeGenerated
  have wholePaid : whole.Charged sources ownerInitial (count + 1) :=
    chainChargedTrans (chainChargedTrans predecessorCharged completedCharged) exposeCharged
  refine ⟨nextHeader, nextHistory, ⟨nextGenerated, headerGenerated, wholeGenerated⟩, rfl,
    headerSource, ?_, headerDomainShape, headerBodyShape, headerRawShape,
    ⟨wholePaid⟩, ⟨nextHeaderOccurrence⟩, ⟨nextLedger⟩⟩
  · rw [headerSource]
    exact headerBelow

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
