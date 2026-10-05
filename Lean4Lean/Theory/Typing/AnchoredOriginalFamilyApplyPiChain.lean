import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayBound
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationLineage
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationResultTypeRouteData
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteAmbient

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem route_reserve_trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
    (first.trans second).reserve = first.reserve ++ second.reserve := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem route_reserve_same
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
    (RawGeneratedTypeRoute.same left right leftOrdered rightOrdered initial frame).reserve =
      [Closure.bundle (.close (left.node.dependencyOrigin leftOrdered) initial)
        (.close (right.node.dependencyOrigin rightOrdered)
          (frame.realization.frame.dependencyEnvironment rightOrdered))] := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem route_generated_trans
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

/-- Retain the actual function occurrence while changing only its displayed
source expression by a proved syntactic equality. Its assigned Pi is kept. -/
noncomputable def OriginalApplicationTypeRouteSide.functionDisplayAs
    (side : OriginalApplicationTypeRouteSide U common)
    (same : expression = side.f.subst side.raw) :
    OriginalNestedDisplay U common expression ((VExpr.forallE side.A side.B).subst side.raw) where
  sourceEnv := side.sourceEnv
  source := side.source
  sourceExpression := side.f
  sourceType := .forallE side.A side.B
  context := side.location.contextDerivation side.initial
  node := side.function
  provenance := .ofLocation (.appFunction side.location) side.initial
  raw := side.raw
  graph := side.graph
  expression_eq := same
  type_eq := rfl

noncomputable def OriginalApplicationTypeRouteSide.predecessorRoute
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight next.pi.display previous.resultDisplay
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered)
      (previousFrame.realization.frame.dependencyEnvironment previousOrdered) :=
  .trans
    (.same next.pi.display (next.functionDisplayAs same).formationDisplay nextOrdered nextOrdered
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered) nextFrame)
    (previous.resultFromAssignedRoute (next.functionDisplayAs same) nextOrdered previousOrdered
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered) previousFrame)

theorem OriginalApplicationTypeRouteSide.predecessorRoute_generated
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight next.graph nextFrame.realization.frame.raw)
    (previousGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight previous.graph previousFrame.realization.frame.raw) :
    (next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).Generated base commonCaps := by
  apply route_generated_trans
  · refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      trivial
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact nextGenerated
  · exact previous.resultFromAssignedRoute_generated (next.functionDisplayAs same) nextOrdered previousOrdered
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered) previousFrame previousGenerated

/-- Adjacent source arguments identify the preceding term syntactically,
while leaving the two independently assigned types untouched. -/
theorem familySpine_adjacent
    (arguments : List VExpr)
    {node : EndpointState sourceEnv U source (mkApps (.const name levels) arguments) assigned}
    (start : Located root node) (index : Nat)
    (selected : arguments[index]? = some argument)
    (nextSelected : arguments[index + 1]? = some nextArgument) :
    (spineApplication arguments start (index + 1) nextSelected).functionExpression =
      .app (spineApplication arguments start index selected).functionExpression argument := by
  rw [spineApplication_functionExpression, spineApplication_functionExpression,
    List.take_add_one, selected]
  simp only [Option.toList_some, mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]

private def routeFrame_recontext
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    OriginalTypeRouteFrame env registry target (equal ▸ graph) commonLeft commonRight := by
  cases equal
  exact frame

private theorem routeFrame_recontext_environment
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) :
    (routeFrame_recontext equal frame).realization.frame.dependencyEnvironment ordered =
      frame.realization.frame.dependencyEnvironment ordered := by
  cases equal
  rfl

private theorem routeFrame_recontext_generated
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight (equal ▸ graph)
      (routeFrame_recontext equal frame).realization.frame.raw := by
  cases equal
  exact generated

private theorem piPrefix_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {start : Located root node} (packet : PiPrefix start)
    (initial : ContextDerivation sourceEnv U rootSource) :
    packet.view.location.contextDerivation initial = start.contextDerivation initial := by
  rw [← packet.location_eq, PrefixRoute.locate_contextDerivation]

/-- A later declared Pi is exposed inside the same original header tree.
Only equality of the retained original contexts transports its actual frame. -/
noncomputable def nativeHeaderSide
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw) :
    OriginalPiTypeRouteSide U common :=
  let packet := piPrefix start
  { sourceEnv := sourceEnv
    source := source
    A := A
    B := B
    u := packet.view.domainLevel
    v := packet.view.bodyLevel
    hu := packet.view.domainWF
    hv := packet.view.bodyWF
    domain := packet.view.domain
    body := packet.view.body
    rootSource := rootSource
    rootExpression := rootExpression
    rootType := rootType
    root := root
    initial := initial
    location := packet.view.location
    raw := raw
    graph := (piPrefix_context packet initial).symm ▸ graph }

noncomputable def nativeHeaderFrame
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    OriginalTypeRouteFrame env registry target (nativeHeaderSide initial start graph).graph commonLeft commonRight :=
  routeFrame_recontext (piPrefix_context (piPrefix start) initial).symm frame

theorem nativeHeaderFrame_environment
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) :
    (nativeHeaderFrame initial start graph frame).realization.frame.dependencyEnvironment ordered =
      frame.realization.frame.dependencyEnvironment ordered :=
  routeFrame_recontext_environment _ frame ordered

theorem nativeHeaderFrame_generated
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight (nativeHeaderSide initial start graph).graph
      (nativeHeaderFrame initial start graph frame).realization.frame.raw :=
  routeFrame_recontext_generated _ frame generated

noncomputable def nativeHeaderRoute
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      (OriginalNestedDisplay.ofOccurrence initial start graph) (nativeHeaderSide initial start graph).display
      (frame.realization.frame.dependencyEnvironment ordered)
      ((nativeHeaderFrame initial start graph frame).realization.frame.dependencyEnvironment ordered) :=
  .same (.ofOccurrence initial start graph) (nativeHeaderSide initial start graph).display ordered ordered
    (frame.realization.frame.dependencyEnvironment ordered) (nativeHeaderFrame initial start graph frame)

theorem nativeHeaderRoute_generated
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    (nativeHeaderRoute initial start graph frame ordered).Generated base commonCaps := by
  refine ⟨?_, ?_⟩
  · rw [nativeHeaderRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    trivial
  · intro boxed member
    rw [nativeHeaderRoute, RawGeneratedTypeRoute.frames.eq_def] at member
    cases List.mem_singleton.mp member
    exact nativeHeaderFrame_generated initial start graph frame generated

/-- Consume a literal next Pi in an actual retained header display. The
returned route, domain reference and frame all retain the selected original
Pi occurrence; no source proof is reconstructed after capture. -/
theorem OriginalNestedDisplay.nativePiCursor
    (display : OriginalNestedDisplay U common expression assigned)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.realization.frame.raw) :
    ∃ side : OriginalPiTypeRouteSide U common,
      ∃ sideOrdered : side.sourceEnv.Ordered,
      ∃ nextFrame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight display side.display
          (frame.realization.frame.dependencyEnvironment ordered)
          (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
        route.Generated base commonCaps ∧
        side.sourceEnv = display.sourceEnv ∧
        side.A = A ∧ side.B = B ∧ side.raw = display.raw ∧
        CappedCaptureGenerated base commonCaps commonLeft commonRight side.graph nextFrame.realization.frame.raw ∧
        nextFrame.realization.frame.dependencyEnvironment sideOrdered =
          frame.realization.frame.dependencyEnvironment ordered ∧
        ∃ domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u), side.domain = .ref domain := by
  rcases display with ⟨sourceEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at shape ordered frame generated ⊢
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  let side := nativeHeaderSide initial start graph
  let nextFrame := nativeHeaderFrame initial start graph frame
  refine ⟨side, ordered, nextFrame, nativeHeaderRoute initial start graph frame ordered,
    nativeHeaderRoute_generated initial start graph frame ordered generated, rfl, rfl, rfl, rfl,
    nativeHeaderFrame_generated initial start graph frame generated,
    nativeHeaderFrame_environment initial start graph frame ordered, ?_⟩
  exact (piPrefix start).view.location.originalDomains.1

noncomputable def OriginalApplyPiReplayResult.captureFrame
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
    {field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType}
    {major : EndpointRef left.sourceEnv U left.source majorExpression majorType}
    (replayed : OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
    OriginalTypeRouteFrame env registry target history.destination.graph commonLeft commonRight :=
  ⟨replayed.reply.reply.locals, replayed.reply.reply.available,
    replayed.reply.reply.realization, replayed.reply.reply.closed⟩

section
variable {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {commonLeft commonRight : Subst}
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

/-- A produced captured frame becomes the concrete baseline for the next
parameter. The final literal reindex is a real charged edge: equal capacity
alone never identifies its finite environment with the previous envelope. -/
theorem OriginalApplyPiHistory.generatedSuccessor
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.Generated base commonCaps)
    (replayed : OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
    ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (sourceSide).resultDisplay history.destination
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)
        (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered),
      route.Generated base commonCaps ∧
      (history.whole.Ambient → route.Ambient) ∧
      route.reserve = history.reserve ++
        [Closure.bundle
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (history.outputEnvironment field major ownerInitial))
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered))] := by
  cases history with
  | mk leftOrdered rightOrdered leftBelow rightDomain rightDomainEq sourceFrame headerFrame whole =>
    have domainEq : rightDomain = headerDomain := (EndpointState.ref.inj rightDomainEq).symm
    subst rightDomain
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide :=
      ⟨leftOrdered, rightOrdered, leftBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
    let application := history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
    let reframe := RawGeneratedTypeRoute.same history.destination history.destination rightOrdered rightOrdered
      (history.outputEnvironment field major ownerInitial) replayed.captureFrame
    dsimp only [originalApplicationTypeRouteSide, originalNativePiRouteSide] at *
    refine ⟨.trans application reframe, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
        exact ⟨history.applyRoute_wellFormed (field := field) initial domain body function argument result hu hv location sourceGraph
          headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
          generated.whole.wellFormed, by dsimp only [reframe]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial⟩
      · intro boxed member
        rw [RawGeneratedTypeRoute.frames.eq_def] at member
        rcases List.mem_append.mp member with member | member
        · exact (history.applyRoute_generated (field := field) initial domain body function argument result hu hv location sourceGraph
            headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
            generated).frames boxed member
        · have only : boxed = replayed.captureFrame.box := by
            dsimp only [reframe] at member
            rw [RawGeneratedTypeRoute.frames.eq_def] at member
            exact List.mem_singleton.mp member
          subst boxed
          exact replayed.reply.capped
    · intro wholeAmbient
      rw [RawGeneratedTypeRoute.Ambient.eq_def]
      refine ⟨?_, ?_⟩
      · change application.Ambient
        dsimp only [application, OriginalApplyPiHistory.applyRoute]
        rw [RawGeneratedTypeRoute.Ambient.eq_def]
        exact wholeAmbient
      · change reframe.Ambient
        rw [RawGeneratedTypeRoute.Ambient.eq_def]
        exact ⟨headerBelow, headerBelow⟩
    · rw [route_reserve_trans]
      rw [history.applyRoute_reserve (field := field) initial domain body function argument result hu hv location sourceGraph
        headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow]
      dsimp only [reframe]
      exact congrArg (fun reserve => history.reserve ++ reserve)
        (route_reserve_same history.destination history.destination rightOrdered rightOrdered
          (history.outputEnvironment field major ownerInitial) replayed.captureFrame)

/-- The dependent successor uses the preceding concrete replayed capture,
the next actual source application, and the next Pi in the retained header.
All three route segments are built from those original occurrences. -/
theorem OriginalApplyPiHistory.nextParameter
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.Generated base commonCaps)
    (replayed : OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile)
    (next : OriginalApplicationTypeRouteSide U common)
    (nextOrdered : next.sourceEnv.Ordered) (nextBelow : next.sourceEnv ≤ env)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (nextGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight next.graph nextFrame.realization.frame.raw)
    (adjacent : (VExpr.app f a).subst sourceRaw = next.f.subst next.raw)
    (headerShape : D = .forallE nextDomain nextBody) :
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.Generated base commonCaps ∧
        nextHistory.sourceFrame = nextFrame ∧
        nextHeader.sourceEnv = headerEnv ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.A = nextDomain ∧ nextHeader.B = nextBody ∧
        nextHeader.raw = headerRaw.cons (a.subst sourceRaw) := by
  obtain ⟨completed, completedGenerated, _, _⟩ := history.generatedSuccessor
    (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound
    headerBelow generated replayed
  obtain ⟨nextHeader, nextHeaderOrdered, nextHeaderFrame, exposeHeader, exposeGenerated,
      headerSource, headerDomainShape, headerBodyShape, headerRawShape, headerGenerated, _, nextDomainOriginal, nextDomainEq⟩ :=
    history.destination.nativePiCursor headerShape history.rightOrdered replayed.captureFrame replayed.reply.capped
  let predecessor := next.predecessorRoute sourceSide adjacent nextOrdered history.leftOrdered
    nextFrame history.sourceFrame
  have predecessorGenerated := next.predecessorRoute_generated sourceSide adjacent nextOrdered history.leftOrdered
    nextFrame history.sourceFrame nextGenerated generated.source
  let whole := (predecessor.trans completed).trans exposeHeader
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader :=
    ⟨nextOrdered, nextHeaderOrdered, nextBelow, nextDomainOriginal, nextDomainEq,
      nextFrame, nextHeaderFrame, whole⟩
  refine ⟨nextHeader, nextHistory, ⟨nextGenerated, headerGenerated, ?_⟩, rfl, headerSource, ?_, headerDomainShape, headerBodyShape, headerRawShape⟩
  · exact route_generated_trans (route_generated_trans predecessorGenerated completedGenerated) exposeGenerated
  · rw [headerSource]
    exact headerBelow

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
