import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiRouteLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteCharges

/-! Each dependent family parameter retains the same original source and
header occurrences while advancing the concrete capture ledger once. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def ParameterRouteOccurrence.route
    {first : EndpointState sourceEnv U source expression firstType}
    {last : EndpointState sourceEnv U source expression lastType}
    (occurrence : ParameterRouteOccurrence sources ordered first)
    (route : PrefixRoute sourceEnv U source expression first last) :
    ParameterRouteOccurrence sources ordered last := by
  cases occurrence with
  | seed occurrence =>
    apply ParameterRouteOccurrence.seed
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (route.locate location)
    | equalityLeft root member location => exact .equalityLeft root member (route.locate location)
    | equalityRight root member location => exact .equalityRight root member (route.locate location)
  | requested occurrence =>
    apply ParameterRouteOccurrence.requested
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (route.locate location)
    | equalityLeft root member location => exact .equalityLeft root member (route.locate location)
    | equalityRight root member location => exact .equalityRight root member (route.locate location)

noncomputable def ParameterRouteOccurrence.piDomain
    (occurrence : ParameterRouteOccurrence sources ordered (.pi hu hv domain body)) :
    ParameterRouteOccurrence sources ordered domain := by
  cases occurrence with
  | seed occurrence =>
    apply ParameterRouteOccurrence.seed
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (.piDomain location)
    | equalityLeft root member location => exact .equalityLeft root member (.piDomain location)
    | equalityRight root member location => exact .equalityRight root member (.piDomain location)
  | requested occurrence =>
    apply ParameterRouteOccurrence.requested
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (.piDomain location)
    | equalityLeft root member location => exact .equalityLeft root member (.piDomain location)
    | equalityRight root member location => exact .equalityRight root member (.piDomain location)

noncomputable def ParameterRouteOccurrence.piBody
    (occurrence : ParameterRouteOccurrence sources ordered (.pi hu hv domain body)) :
    ParameterRouteOccurrence sources ordered body := by
  cases occurrence with
  | seed occurrence =>
    apply ParameterRouteOccurrence.seed
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (.piBody location)
    | equalityLeft root member location => exact .equalityLeft root member (.piBody location)
    | equalityRight root member location => exact .equalityRight root member (.piBody location)
  | requested occurrence =>
    apply ParameterRouteOccurrence.requested
    cases occurrence with
    | headerOrigin location => exact .headerOrigin (.piBody location)
    | equalityLeft root member location => exact .equalityLeft root member (.piBody location)
    | equalityRight root member location => exact .equalityRight root member (.piBody location)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem chainGeneratedTrans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstGenerated : first.Generated base commonCaps) (secondGenerated : second.Generated base commonCaps) :
    (first.trans second).Generated base commonCaps := by
  refine ⟨?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨firstGenerated.wellFormed, secondGenerated.wellFormed⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def] at member
    exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (secondGenerated.frames boxed)

private noncomputable def chainChargedTrans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstCharged : first.Charged sources ownerInitial count) (secondCharged : second.Charged sources ownerInitial count) :
    (first.trans second).Charged sources ownerInitial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨firstCharged, secondCharged⟩

private theorem chainAmbientTrans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstAmbient : first.Ambient) (secondAmbient : second.Ambient) :
    (first.trans second).Ambient := by
  rw [RawGeneratedTypeRoute.Ambient.eq_def]
  exact ⟨firstAmbient, secondAmbient⟩

private theorem predecessorAmbient
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextBelow : next.sourceEnv ≤ env) (previousBelow : previous.sourceEnv ≤ env) :
    (next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).Ambient := by
  simp only [OriginalApplicationTypeRouteSide.predecessorRoute,
    OriginalApplicationTypeRouteSide.resultFromAssignedRoute, RawGeneratedTypeRoute.Ambient.eq_def]
  exact ⟨⟨nextBelow, nextBelow⟩, ⟨⟨nextBelow, previousBelow⟩, ⟨previousBelow, previousBelow⟩⟩⟩

/-- Expose the next header Pi without erasing its position in the retained
installation roots. The actual selected frame keeps the incoming ledger. -/
theorem OriginalNestedDisplay.nativePiCursor_counted
    (display : OriginalNestedDisplay U common expression assigned)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.realization.frame.raw)
    (below : display.sourceEnv ≤ env)
    (occurrence : ParameterRouteOccurrence sources ordered display.node)
    (ledger : ParameterRouteLedger sources ownerInitial count (frame.realization.frame.dependencyEnvironment ordered)) :
    ∃ side : OriginalPiTypeRouteSide U common,
      ∃ sideOrdered : side.sourceEnv.Ordered,
      ∃ nextFrame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight display side.display
          (frame.realization.frame.dependencyEnvironment ordered)
          (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
        route.Generated base commonCaps ∧ route.Ambient ∧
        side.sourceEnv = display.sourceEnv ∧
        side.A = A ∧ side.B = B ∧ side.raw = display.raw ∧
        CappedCaptureGenerated base commonCaps commonLeft commonRight side.graph nextFrame.realization.frame.raw ∧
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
    nativeHeaderRoute_generated initial start graph frame ordered generated,
    ?_, rfl, rfl, rfl, rfl, nativeHeaderFrame_generated initial start graph frame generated,
    frameEq, ⟨charged⟩, ⟨nextOccurrence⟩, ⟨nextLedger⟩, ?_⟩
  · rw [nativeHeaderRoute, RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨below, below⟩
  · exact (piPrefix start).view.location.originalDomains.1

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
theorem OriginalApplyPiHistory.nextParameter_counted
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = []) (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.Generated base commonCaps)
    (replayed : OriginalApplyPiReplayResult history sources.field sources.major ownerInitial base commonCaps profile)
    (wholeAmbient : history.whole.Ambient)
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
    (nextGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight nextGraph nextFrame.realization.frame.raw)
    (nextBound : environmentCost (nextFrame.realization.frame.dependencyEnvironment sources.ordered) ≤
      environmentCost (nextLocation.dependencyEnvironment sources.ordered ownerInitial))
    (adjacent : (VExpr.app f a).subst sourceRaw = nextF.subst nextRaw)
    (headerShape : D = .forallE nextHeaderDomain nextHeaderBody) :
    let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
      nextResult nextHu nextHv nextLocation nextGraph
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.Generated base commonCaps ∧
        nextHistory.sourceFrame = nextFrame ∧
        nextHeader.sourceEnv = headerEnv ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.A = nextHeaderDomain ∧ nextHeader.B = nextHeaderBody ∧
        nextHeader.raw = headerRaw.cons (a.subst sourceRaw) ∧
        nextHistory.whole.Ambient ∧
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
    .bounded outputLedger _ (replayed.environment_bound history.rightOrdered)
  have bodyOccurrence : ParameterRouteOccurrence sources history.rightOrdered history.destination.node :=
    headerOccurrence.piBody
  obtain ⟨completed, completedGenerated, completedAmbient, completedReserve⟩ := history.generatedSuccessor
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
  obtain ⟨nextHeader, nextHeaderOrdered, nextHeaderFrame, exposeHeader, exposeGenerated, exposeAmbient,
      headerSource, headerDomainShape, headerBodyShape, headerRawShape, headerGenerated, headerFrameEq,
      ⟨exposeCharged⟩, ⟨nextHeaderOccurrence⟩, ⟨nextLedger⟩, nextDomainOriginal, nextDomainEq⟩ :=
    history.destination.nativePiCursor_counted headerShape history.rightOrdered replayed.captureFrame
      replayed.reply.capped headerBelow bodyOccurrence capturedLedger
  let predecessor := next.predecessorRoute sourceSide adjacent sources.ordered history.leftOrdered nextFrame history.sourceFrame
  have predecessorGenerated := next.predecessorRoute_generated sourceSide adjacent sources.ordered history.leftOrdered
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
  have wholeGenerated : whole.Generated base commonCaps :=
    chainGeneratedTrans (chainGeneratedTrans predecessorGenerated completedGenerated) exposeGenerated
  have wholePaid : whole.Charged sources ownerInitial (count + 1) :=
    chainChargedTrans (chainChargedTrans predecessorCharged completedCharged) exposeCharged
  refine ⟨nextHeader, nextHistory, ⟨nextGenerated, headerGenerated, wholeGenerated⟩, rfl,
    headerSource, ?_, headerDomainShape, headerBodyShape, headerRawShape,
    ?_, ⟨wholePaid⟩, ⟨nextHeaderOccurrence⟩, ⟨nextLedger⟩⟩
  · rw [headerSource]
    exact headerBelow
  · exact chainAmbientTrans
      (chainAmbientTrans
        (predecessorAmbient next sourceSide adjacent sources.ordered history.leftOrdered nextFrame history.sourceFrame
          history.leftBelow history.leftBelow)
        (completedAmbient wholeAmbient)) exposeAmbient

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
