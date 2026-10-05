import Lean4Lean.Theory.Typing.AnchoredOriginalNativeHeaderWorldExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteExecutionData
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderSourceGeneration

/-! A dependent successor from the actual selected capture frame. Construction
needs no completed application replay or semantic result: the existing finite
whole history and positive selected generation are retained as executable data. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportWorld transportWorld_call transportWorld_worlds descendant_below same_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private trans_worldInputs trans_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
open private route_reserve_trans route_reserve_same routeFrame_recontext piPrefix_context from
  Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
set_option quotPrecheck false

private noncomputable def composeExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {left : OriginalNestedDisplay U common le lt}
    {middle : OriginalNestedDisplay U common me middleAssigned}
    {right : OriginalNestedDisplay U common re rt}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
    {lc : OriginalWorldControls strata left.sourceEnv} {mc : OriginalWorldControls strata middle.sourceEnv}
    {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {mw : WorldEnvironmentProvenance strata U intermediate}
    {rw : WorldEnvironmentProvenance strata U final}
    (before : first.WorldBoundary firstInputs lc mc lw mw)
    (after : second.WorldBoundary secondInputs mc rc mw rw)
    (leftData : before.ExecutionFrames P base caps frontier)
    (rightData : after.ExecutionFrames P base caps frontier) :
    (before.trans after).ExecutionFrames P base caps frontier := by
  classical
  intro occurrence member
  by_cases previous : occurrence ∈ before.frames
  · exact leftData occurrence previous
  · exact rightData occurrence ((List.mem_append.mp member).resolve_left previous)

noncomputable def OriginalApplicationTypeRouteSide.predecessorSelectedWorldExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextControls : OriginalWorldControls strata next.sourceEnv)
    (previousControls : OriginalWorldControls strata previous.sourceEnv)
    (nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (previousWorld : WorldEnvironmentProvenance strata U (previousFrame.realization.frame.dependencyEnvironment previousOrdered))
    (compatible : nextControls.cutoff = previousControls.cutoff ∧ nextControls.fuel = previousControls.fuel)
    (nextData : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨nextFrame.box, nextControls, nextWorld⟩)
    (previousData : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨previousFrame.box, previousControls, previousWorld⟩) :
    (next.predecessorWorldInputs_boundary previous same nextOrdered previousOrdered nextFrame previousFrame
      nextControls previousControls nextWorld previousWorld compatible).ExecutionFrames P base caps frontier := by
  classical
  intro occurrence member
  change occurrence ∈ [⟨nextFrame.box, nextControls, nextWorld⟩] ++
    ([⟨previousFrame.box, previousControls, previousWorld⟩] ++ [⟨previousFrame.box, previousControls, previousWorld⟩]) at member
  by_cases current : occurrence = ⟨nextFrame.box, nextControls, nextWorld⟩
  · cases current
    exact nextData
  · simp only [List.mem_append, List.mem_singleton, current, false_or, or_self] at member
    cases member
    exact previousData

private theorem graph_recontext_heq
    {first second : ContextDerivation sourceEnv U source}
    {raw : Subst} (equal : first = second)
    (graph : OriginalCaptureMap (common := common) first raw) : HEq (equal ▸ graph) graph := by
  cases equal
  rfl

private theorem frame_recontext_heq
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    HEq (routeFrame_recontext equal frame) frame := by
  cases equal
  rfl

/-- The exact Pi side selected from this display's retained original proof. -/
noncomputable def OriginalNestedDisplay.nativePiSide
    (display : OriginalNestedDisplay U common expression assigned)
    (shape : display.sourceExpression = .forallE A B) :
    OriginalPiTypeRouteSide U common := by
  rcases display with ⟨headerEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at shape
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  exact nativeHeaderSide initial start graph

/-- The operative cursor exposes the actual next original Pi and carries its
selected positive generation through the exact context transport. -/
theorem OriginalNestedDisplay.nativePiCursorSelectedWorldExecution
    {sourceEnv : VEnv} {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv familyName familyInfo)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerType)
    (callerCaptured : WorldEnvironmentProvenance strata U callerEnvironment)
    (display : OriginalNestedDisplay U common expression assigned)
    (sourceEqual : display.sourceEnv = origin.source)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨frame.box, (show OriginalWorldControls strata display.sourceEnv from
        sourceEqual.symm ▸ controls.atHeader origin), world⟩)
    (inherited : Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] world.worlds) :
    ∃ side : OriginalPiTypeRouteSide U common,
      ∃ sideOrdered : side.sourceEnv.Ordered,
      ∃ nextFrame : OriginalTypeRouteFrame env registry target side.graph commonLeft commonRight,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight display side.display
          (frame.realization.frame.dependencyEnvironment ordered)
          (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
        route.SourceGenerated P base caps ∧
        side.sourceEnv = display.sourceEnv ∧
        side.A = A ∧ side.B = B ∧ side.raw = display.raw ∧
        nextFrame.realization.frame.dependencyEnvironment sideOrdered = frame.realization.frame.dependencyEnvironment ordered ∧
        (∃ domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u), side.domain = .ref domain) ∧
        ∃ nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
          nextWorld.worlds = world.worlds ∧
          ∃ inputs : route.WorldInputs strata,
            Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] (route.worldReserve inputs).worlds ∧
            ∃ nextControls : OriginalWorldControls strata side.sourceEnv,
            ∃ boundary : route.WorldBoundary inputs (sourceEqual.symm ▸ controls.atHeader origin)
                nextControls world nextWorld,
              Nonempty (boundary.ExecutionFrames P base caps frontier) ∧
              ∃ nextData : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨nextFrame.box, nextControls, nextWorld⟩,
                HEq nextData.generation.environment data.generation.environment ∧
                HEq side.domain (piPrefix (display.provenance.location.castExpression shape)).view.domain ∧
                HEq side.body (piPrefix (display.provenance.location.castExpression shape)).view.body ∧
                HEq side.location (piPrefix (display.provenance.location.castExpression shape)).view.location ∧
                side.source = display.source ∧
                HEq (side.location.contextDerivation side.initial) display.context ∧
                HEq side.graph display.graph ∧ HEq nextFrame frame ∧
                side = display.nativePiSide shape := by
  rcases display with ⟨headerEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at sourceEqual shape ordered frame world data inherited ⊢
  subst headerEnv
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  let side := nativeHeaderSide initial start graph
  let nextFrame := nativeHeaderFrame initial start graph frame
  let nextWorld := transportWorld (nativeHeaderFrame_environment initial start graph frame ordered).symm world
  have ambient := nativeHeaderRoute_ambientGenerated initial start graph frame ordered
    data.generation.erase.ambientGenerated
  have routeGenerated : (nativeHeaderRoute initial start graph frame ordered).SourceGenerated P base caps := by
    refine ⟨ambient.wellFormed, ambient.ambient, ?_, ?_⟩
    · rw [nativeHeaderRoute, RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨data.generation.erase.sources.1.source, data.generation.erase.sources.1.source, trivial⟩
    · intro boxed member
      rw [nativeHeaderRoute, RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact (nativeHeaderFrameExecution initial start graph frame (controls.atHeader origin) world data).generation.erase
  refine ⟨side, ordered, nextFrame, nativeHeaderRoute initial start graph frame ordered,
    routeGenerated,
    rfl, rfl, rfl, rfl, nativeHeaderFrame_environment initial start graph frame ordered,
    (piPrefix start).view.location.originalDomains.1, nextWorld, transportWorld_worlds _ world,
    nativeHeaderWorldInputs initial start graph frame (controls.atHeader origin) world, ?_,
    controls.atHeader origin, nativeHeaderWorldInputs_boundary initial start graph frame (controls.atHeader origin) world,
    ⟨nativeHeaderWorldExecution initial start graph frame (controls.atHeader origin) world data⟩,
    nativeHeaderFrameExecution initial start graph frame (controls.atHeader origin) world data,
    nativeHeaderFrameExecution_environment initial start graph frame (controls.atHeader origin) world data,
    HEq.rfl, HEq.rfl, HEq.rfl, rfl, heq_of_eq (piPrefix_context (piPrefix start) initial),
    graph_recontext_heq (piPrefix_context (piPrefix start) initial).symm graph,
    frame_recontext_heq (piPrefix_context (piPrefix start) initial).symm frame, rfl⟩
  rw [nativeHeaderWorldInputs_worlds]
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin node world
      caller callerCaptured _ _ inherited⟩
  · cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin side.display.node world
      caller callerCaptured _ _ inherited⟩

section Successor
variable {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {frontier : List (World strata.rules.length)}
  {outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType}
  (head : OriginalFactorCut.ProjectionHead outer)
  {field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel)}
  (fieldEq : head.field = .ref field)
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (majorLocation : Located (.right head.major) (.ref major))
  (controls : OriginalWorldControls strata sourceEnv)
  (captured : WorldEnvironmentProvenance strata U ownerInitial)
  (origin : ConstantHeaderOrigin sourceEnv familyName familyInfo)
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef origin.source U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation origin.source U headerRootSource)
  (headerDomain : EndpointRef origin.source U headerSource C (.sort cu))
  (headerBody : EndpointState origin.source U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
local notation "callerWorld" => originalCallWorld controls .assignedComparison outer captured

variable
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight
      (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph)
      (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph))
    (sourceEnvironment : history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered = ownerInitial)
    (priorWorld : WorldEnvironmentProvenance strata U history.final)
    (priorReady : Sponsored [originalCallWorld controls .assignedComparison outer captured] priorWorld.worlds)
    (wholeInputs : history.whole.WorldInputs strata)
    (wholeReady : Sponsored [originalCallWorld controls .assignedComparison outer captured]
      (history.whole.worldReserve wholeInputs).worlds)

local notation "sourceWorld" => transportWorld sourceEnvironment.symm captured
local notation "headerControls" => controls.atHeader origin

variable (wholeBoundary : history.whole.WorldBoundary wholeInputs controls (controls.atHeader origin)
  (transportWorld sourceEnvironment.symm captured) priorWorld)


variable
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : origin.source ≤ env)
    (sourceData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
      ⟨history.sourceFrame.box, controls, transportWorld sourceEnvironment.symm captured⟩)
    (priorData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
      ⟨history.headerFrame.box, controls.atHeader origin, priorWorld⟩)
    (wholeFrames : wholeBoundary.ExecutionFrames P base commonCaps frontier)

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  fieldEq majorLocation priorReady wholeReady wholeBoundary noBinders sourceBound headerBelow sourceEnvironment
  sourceData priorData wholeFrames in
theorem OriginalApplyPiHistory.generatedSelectedSuccessorWorldExecution
    (wholeGenerated : history.whole.SourceGenerated P base commonCaps)
    (selectedFrame : OriginalTypeRouteFrame env registry target history.destination.graph commonLeft commonRight)
    (selected : WorldEnvironmentProvenance strata U
      (selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered))
    (selectedReady : Sponsored [callerWorld] selected.worlds)
    (selectedData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
      ⟨selectedFrame.box, controls.atHeader origin, selected⟩) :
    ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (sourceSide).resultDisplay history.destination
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)
        (selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered),
      route.SourceGenerated P base commonCaps ∧
      route.reserve = history.reserve ++
        [Closure.bundle
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (history.outputEnvironment field major ownerInitial))
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered))] ∧
      ∃ inputs : route.WorldInputs strata, Sponsored [callerWorld] (route.worldReserve inputs).worlds ∧
        ∃ boundary : route.WorldBoundary inputs controls headerControls sourceWorld selected,
          Nonempty (boundary.ExecutionFrames P base commonCaps frontier) := by
  have generated : history.AmbientGenerated base commonCaps :=
    ⟨sourceData.generation.erase.ambientGenerated, priorData.generation.erase.ambientGenerated,
      wholeGenerated.ambientGenerated⟩
  rcases history with ⟨leftOrdered, rightOrdered, leftBelow, rightDomain, rightDomainEq, sourceFrame, headerFrame, whole⟩
  have domainEq : rightDomain = headerDomain := (EndpointState.ref.inj rightDomainEq).symm
  subst rightDomain
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide :=
    ⟨leftOrdered, rightOrdered, leftBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
  let application := history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
  let reframe := RawGeneratedTypeRoute.same history.destination history.destination rightOrdered rightOrdered
    (history.outputEnvironment field major ownerInitial) selectedFrame
  let applicationInputs := history.applyWorldInputs (field := field) head controls captured origin initial domain body function argument result hu hv location
    sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    sourceEnvironment priorWorld wholeInputs noBinders sourceBound headerBelow
  let envelope := history.outputWorld field major controls headerControls captured (transportWorld sourceEnvironment.symm captured) priorWorld wholeInputs
  let reframeInputs : reframe.WorldInputs strata := (headerControls, headerControls, envelope, selected)
  have applicationGenerated := history.applyRoute_ambientGenerated (field := field) initial domain body function argument result
    hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    noBinders ownerInitial sourceBound headerBelow generated
  have applicationSource : application.SourceGenerated P base commonCaps := by
    refine ⟨applicationGenerated.wellFormed, applicationGenerated.ambient, ?_, ?_⟩
    · dsimp only [application]
      rw [OriginalApplyPiHistory.applyRoute, RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨wholeGenerated.sources.left, wholeGenerated.sources.right, wholeGenerated.sources⟩
    · intro boxed member
      rw [history.applyRoute_frames (field := field) initial domain body function argument result hu hv location sourceGraph
        headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow] at member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact sourceData.generation.erase
      · exact priorData.generation.erase
      · exact wholeGenerated.frames boxed member
  have reframeGenerated : reframe.SourceGenerated P base commonCaps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [reframe]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · dsimp only [reframe]; rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨headerBelow, headerBelow⟩
    · dsimp only [reframe]; rw [RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨wholeGenerated.sources.right, wholeGenerated.sources.right, trivial⟩
    · intro boxed member
      dsimp only [reframe] at member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact selectedData.generation.erase
  let applicationBoundary : application.WorldBoundary applicationInputs controls headerControls
      (transportWorld sourceEnvironment.symm captured) envelope :=
    .applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph leftOrdered rightOrdered
      leftBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound whole _
      controls headerControls (transportWorld sourceEnvironment.symm captured) priorWorld captured
      (by rw [transportWorld_worlds]; exact Covered.refl _) wholeInputs
      wholeBoundary (by
        simp only [OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
          RawGeneratedTypeRoute.reserve, history, originalNativePiRouteSide,
          EndpointState.dependencyOrigin, OriginalApplyPiHistory.final]
        rfl)
  let reframeBoundary : reframe.WorldBoundary reframeInputs headerControls headerControls envelope selected :=
    .same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩
  let applicationFrames : applicationBoundary.ExecutionFrames P base commonCaps frontier := by
    classical
    intro occurrence member
    change occurrence ∈ ⟨sourceFrame.box, controls, transportWorld sourceEnvironment.symm captured⟩ ::
      ⟨headerFrame.box, headerControls, priorWorld⟩ :: wholeBoundary.frames at member
    by_cases atSource : occurrence = ⟨sourceFrame.box, controls, transportWorld sourceEnvironment.symm captured⟩
    · cases atSource
      exact sourceData
    · by_cases atPrior : occurrence = ⟨headerFrame.box, headerControls, priorWorld⟩
      · cases atPrior
        exact priorData
      · exact wholeFrames occurrence (by simpa only [List.mem_cons, atSource, atPrior, false_or] using member)
  let reframeFrames : reframeBoundary.ExecutionFrames P base commonCaps frontier := by
    intro occurrence member
    change occurrence ∈ [⟨selectedFrame.box, controls.atHeader origin, selected⟩] at member
    cases List.mem_singleton.mp member
    exact selectedData
  dsimp only [originalApplicationTypeRouteSide, originalNativePiRouteSide] at *
  refine ⟨application.trans reframe, RetainedHeaderUniverse.sourceGenerated_trans applicationSource reframeGenerated, ?_,
    trans_worldInputs applicationInputs reframeInputs, ?_, applicationBoundary.trans reframeBoundary,
    ⟨composeExecution applicationBoundary reframeBoundary applicationFrames reframeFrames⟩⟩
  · rw [route_reserve_trans]
    rw [history.applyRoute_reserve (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow]
    exact congrArg (fun reserve => history.reserve ++ reserve)
      (route_reserve_same history.destination history.destination rightOrdered rightOrdered
        (history.outputEnvironment field major ownerInitial) selectedFrame)
  · rw [trans_worldReserve]
    apply Sponsored.merge
    · exact history.applyWorldInputs_sponsored head majorLocation controls captured origin initial domain body function argument result
        hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
        sourceEnvironment priorWorld priorReady wholeInputs wholeReady noBinders sourceBound headerBelow
    · dsimp only [reframe, reframeInputs]
      rw [same_worldReserve history.destination history.destination rightOrdered rightOrdered
        (history.outputEnvironment field major ownerInitial) selectedFrame
        headerControls headerControls envelope selected]
      have envelopeReady := history.outputWorld_sponsored head fieldEq majorLocation controls captured origin initial domain body function argument result
        hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
        sourceEnvironment priorWorld priorReady wholeInputs wholeReady
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
          history.destination.node envelope outer captured _ _ envelopeReady⟩
      · cases List.mem_singleton.mp member
        exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
          history.destination.node selected outer captured _ _ selectedReady⟩

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  fieldEq majorLocation priorReady wholeReady wholeBoundary noBinders sourceBound headerBelow sourceEnvironment
  sourceData priorData wholeFrames in
/-- The dependent next history is built from the actual next application and
literal next header Pi. All new reserves have original sponsors; the selected
capture's annotated ledger is retained verbatim at the reframe/exposure join. -/
theorem OriginalApplyPiHistory.nextSelectedParameterWorldExecution
    (wholeGenerated : history.whole.SourceGenerated P base commonCaps)
    (selectedFrame : OriginalTypeRouteFrame env registry target history.destination.graph commonLeft commonRight)
    (selected : WorldEnvironmentProvenance strata U
      (selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered))
    (selectedReady : Sponsored [callerWorld] selected.worlds)
    (selectedData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
      ⟨selectedFrame.box, controls.atHeader origin, selected⟩)
    (nextDomainRef : EndpointRef sourceEnv U source nextA (.sort nextU))
    (nextBodyNode : EndpointState sourceEnv U (nextA :: source) nextB (.sort nextV))
    (nextFunction : EndpointState sourceEnv U source nextF (.forallE nextA nextB))
    (nextArgument : EndpointState sourceEnv U source nextArg nextA)
    (nextResult : EndpointState sourceEnv U source (nextB.inst nextArg) (.sort nextV))
    (nextHu : nextU.WF U) (nextHv : nextV.WF U)
    (nextLocation : Located major
      (.app nextHu nextHv (.ref nextDomainRef) nextBodyNode nextFunction nextArgument nextResult))
    (nextGraph : OriginalCaptureMap (common := common) (nextLocation.contextDerivation initial) nextRaw)
    (nextFrame : OriginalTypeRouteFrame env registry target nextGraph commonLeft commonRight)
    (nextEnvironment : nextFrame.realization.frame.dependencyEnvironment controls.ordered = ownerInitial)
    (nextData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
      ⟨nextFrame.box, controls, transportWorld nextEnvironment.symm captured⟩)
    (adjacent : (VExpr.app f a).subst sourceRaw = nextF.subst nextRaw)
    (headerShape : D = .forallE nextHeaderDomain nextHeaderBody) :
    let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
      nextResult nextHu nextHv nextLocation nextGraph
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.AmbientGenerated base commonCaps ∧
        nextHistory.sourceFrame = nextFrame ∧
        nextHeader.sourceEnv = origin.source ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.A = nextHeaderDomain ∧ nextHeader.B = nextHeaderBody ∧
        nextHeader.raw = headerRaw.cons (a.subst sourceRaw) ∧
        nextHistory.final = selectedFrame.realization.frame.dependencyEnvironment history.rightOrdered ∧
        ∃ nextWorld : WorldEnvironmentProvenance strata U nextHistory.final,
          nextWorld.worlds = selected.worlds ∧ Sponsored [callerWorld] nextWorld.worlds ∧
          ∃ inputs : nextHistory.whole.WorldInputs strata,
            Sponsored [callerWorld] (nextHistory.whole.worldReserve inputs).worlds ∧
            ∃ nextSourceEnvironment : nextHistory.sourceFrame.realization.frame.dependencyEnvironment
                nextHistory.leftOrdered = ownerInitial,
            ∃ nextControls : OriginalWorldControls strata nextHeader.sourceEnv,
            ∃ boundary : nextHistory.whole.WorldBoundary inputs controls nextControls
                (transportWorld nextSourceEnvironment.symm captured) nextWorld,
              Nonempty (boundary.ExecutionFrames P base commonCaps frontier) ∧
              ∃ headerData : WorldBoundaryFrame.ExecutionData P base commonCaps frontier
                  ⟨nextHistory.headerFrame.box, nextControls, nextWorld⟩,
                HEq headerData.generation.environment selectedData.generation.environment ∧
                HEq (EndpointState.ref nextHistory.rightDomain)
                  (piPrefix (history.destination.provenance.location.castExpression headerShape)).view.domain ∧
                HEq nextHeader.body
                  (piPrefix (history.destination.provenance.location.castExpression headerShape)).view.body ∧
                HEq nextHeader.location
                  (piPrefix (history.destination.provenance.location.castExpression headerShape)).view.location ∧
                nextHeader.source = C :: headerSource ∧
                HEq (nextHeader.location.contextDerivation nextHeader.initial) history.destination.context ∧
                HEq nextHeader.graph history.destination.graph ∧ HEq nextHistory.headerFrame selectedFrame ∧
                nextHeader = history.destination.nativePiSide headerShape ∧
                ∃ data : nextHistory.whole.ControlledWorldData P base commonCaps controls.cutoff controls.fuel frontier,
                  data.inputs = inputs ∧ boundary.FrameOccurrenceCoherent data.controls data.frames := by
  let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
    nextResult nextHu nextHv nextLocation nextGraph
  obtain ⟨completed, completedGenerated, _completedReserve, completedInputs, completedReady,
      completedBoundary, ⟨completedFrames⟩⟩ :=
    history.generatedSelectedSuccessorWorldExecution (sourceData := sourceData) (priorData := priorData) (wholeFrames := wholeFrames) head fieldEq majorLocation controls captured origin initial domain body function argument result
      hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceEnvironment priorWorld priorReady wholeInputs wholeReady wholeBoundary noBinders sourceBound headerBelow
      wholeGenerated selectedFrame selected selectedReady selectedData
  obtain ⟨nextHeader, nextHeaderOrdered, nextHeaderFrame, exposeHeader, exposeGenerated,
      headerSource, headerDomainShape, headerBodyShape, headerRawShape, headerFrameEq,
      ⟨nextDomainOriginal, nextDomainEq⟩, nextWorld, nextWorlds, exposeInputs, exposeReady, nextControls,
      exposeBoundary, ⟨exposeFrames⟩, nextHeaderData, headerEnvironment, domainOriginalEq, bodyOriginalEq, locationOriginalEq,
      headerContextSource, headerContextEq, headerGraphEq, headerActualFrameEq, headerSideEq⟩ :=
    history.destination.nativePiCursorSelectedWorldExecution controls origin outer captured rfl headerShape history.rightOrdered
      selectedFrame selected selectedData selectedReady
  have nextGenerated := nextData.generation.erase.ambientGenerated
  have headerGenerated := nextHeaderData.generation.erase.ambientGenerated
  let nextWorldSource := transportWorld nextEnvironment.symm captured
  let predecessor := next.predecessorRoute sourceSide adjacent controls.ordered history.leftOrdered nextFrame history.sourceFrame
  let predecessorInputs := next.predecessorWorldInputs sourceSide adjacent controls.ordered history.leftOrdered nextFrame
    history.sourceFrame controls controls nextWorldSource sourceWorld
  have predecessorGenerated := next.predecessorRoute_ambientGenerated sourceSide adjacent controls.ordered history.leftOrdered
    nextFrame history.sourceFrame nextGenerated sourceData.generation.erase.ambientGenerated
  have predecessorSource : predecessor.SourceGenerated P base commonCaps := by
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
  have predecessorReady : Sponsored [callerWorld] (predecessor.worldReserve predecessorInputs).worlds := by
    rw [next.predecessorWorldInputs_worlds]
    intro child member
    simp only [nextWorldSource, transportWorld_call, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appPiFormation nextLocation) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.assignedFormation (.appFunction nextLocation)) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appFunction nextLocation) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation location controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.assignedFormation location) controls captured _ _⟩
    · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation (.appResult location) controls captured _ _⟩
  let whole := (predecessor.trans completed).trans exposeHeader
  have wholeSource := RetainedHeaderUniverse.sourceGenerated_trans
    (RetainedHeaderUniverse.sourceGenerated_trans predecessorSource completedGenerated) exposeGenerated
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader :=
    ⟨controls.ordered, nextHeaderOrdered, history.leftBelow, nextDomainOriginal, nextDomainEq,
      nextFrame, nextHeaderFrame, whole⟩
  refine ⟨nextHeader, nextHistory, ⟨nextGenerated, headerGenerated,
    wholeSource.ambientGenerated⟩,
    rfl, headerSource, ?_, headerDomainShape, headerBodyShape, headerRawShape, headerFrameEq,
    nextWorld, nextWorlds, ?_, trans_worldInputs (trans_worldInputs predecessorInputs completedInputs) exposeInputs, ?_,
    nextEnvironment, nextControls, ?_⟩
  · rw [headerSource]
    exact headerBelow
  · rw [nextWorlds]
    exact selectedReady
  · rw [trans_worldReserve, trans_worldReserve]
    exact (predecessorReady.merge completedReady).merge exposeReady
  · let predecessorBoundary := next.predecessorWorldInputs_boundary sourceSide adjacent controls.ordered history.leftOrdered
      nextFrame history.sourceFrame controls controls nextWorldSource sourceWorld ⟨rfl, rfl⟩
    let predecessorFrames := next.predecessorSelectedWorldExecution sourceSide adjacent controls.ordered history.leftOrdered
      nextFrame history.sourceFrame controls controls nextWorldSource sourceWorld ⟨rfl, rfl⟩ nextData sourceData
    let boundary := (predecessorBoundary.trans completedBoundary).trans exposeBoundary
    let execution := composeExecution (predecessorBoundary.trans completedBoundary) exposeBoundary
      (composeExecution predecessorBoundary completedBoundary predecessorFrames completedFrames) exposeFrames
    let data := boundary.controlledDataOfExecution wholeSource execution
    exact ⟨boundary, ⟨execution⟩, nextHeaderData, headerEnvironment,
      (heq_of_eq nextDomainEq.symm).trans domainOriginalEq, bodyOriginalEq, locationOriginalEq,
      headerContextSource, headerContextEq, headerGraphEq, headerActualFrameEq, headerSideEq, data, rfl,
      boundary.controlledDataOfExecution_coherent wholeSource execution⟩


end Successor

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
