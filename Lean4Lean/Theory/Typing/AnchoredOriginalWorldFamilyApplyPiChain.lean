import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedWorld
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteBoundary
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistorySponsorship

/-! World provenance for a real dependent family successor. Every join reuses
its concrete annotated baseline; equal numerical capacities do not identify
world ledgers. The source links are actual predecessor R/C/R calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportWorld transportWorld_call transportWorld_worlds descendant_below same_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private trans_worldInputs trans_worldReserve environment_worlds_mpr from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
open private route_reserve_trans route_reserve_same from
  Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
set_option quotPrecheck false

private theorem transportWorld_worlds
    {strata : EquationStratification env} {first second : List Closure}
    (equal : first = second) (world : WorldEnvironmentProvenance strata U first) :
    (transportWorld equal world).worlds = world.worlds := by
  cases equal
  rfl

private theorem assigned_worldReserve
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    ((RawGeneratedTypeRoute.assigned left right lf rf initial frame).worldReserve
      (leftControls, rightControls, leftWorld, rightWorld)).worlds =
      [originalCallWorld leftControls .assignedComparison left.node leftWorld,
       originalCallWorld rightControls .assignedComparison right.node rightWorld] := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.assigned left right lf rf initial frame))]
  rfl

/-- Both occurrences keep the same source frame annotations at the shared
formation joins. The assigned comparison is an actual term pair. -/
noncomputable def OriginalApplicationTypeRouteSide.predecessorWorldInputs
    {strata : EquationStratification env}
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextControls : OriginalWorldControls strata next.sourceEnv)
    (previousControls : OriginalWorldControls strata previous.sourceEnv)
    (nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (previousWorld : WorldEnvironmentProvenance strata U (previousFrame.realization.frame.dependencyEnvironment previousOrdered)) :
    (next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).WorldInputs strata := by
  exact trans_worldInputs
    (first := .same next.pi.display (next.functionDisplayAs same).formationDisplay nextOrdered nextOrdered
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered) nextFrame)
    (nextControls, nextControls, nextWorld, nextWorld)
    (trans_worldInputs
      (first := .assigned (next.functionDisplayAs same) previous.termDisplay nextOrdered previousOrdered
        (nextFrame.realization.frame.dependencyEnvironment nextOrdered) previousFrame)
      (second := .same previous.termDisplay.formationDisplay previous.resultDisplay previousOrdered previousOrdered
        (previousFrame.realization.frame.dependencyEnvironment previousOrdered) previousFrame)
      (nextControls, previousControls, nextWorld, previousWorld)
      (previousControls, previousControls, previousWorld, previousWorld))

theorem OriginalApplicationTypeRouteSide.predecessorWorldInputs_worlds
    {strata : EquationStratification env}
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextControls : OriginalWorldControls strata next.sourceEnv)
    (previousControls : OriginalWorldControls strata previous.sourceEnv)
    (nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (previousWorld : WorldEnvironmentProvenance strata U (previousFrame.realization.frame.dependencyEnvironment previousOrdered)) :
    ((next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).worldReserve
      (next.predecessorWorldInputs previous same nextOrdered previousOrdered nextFrame previousFrame
        nextControls previousControls nextWorld previousWorld)).worlds =
      [originalCallWorld nextControls .expressionReindex next.pi.display.node nextWorld,
       originalCallWorld nextControls .expressionReindex next.function.typeFormation.node nextWorld,
       originalCallWorld nextControls .assignedComparison next.function nextWorld,
       originalCallWorld previousControls .assignedComparison previous.node previousWorld,
       originalCallWorld previousControls .expressionReindex previous.node.typeFormation.node previousWorld,
       originalCallWorld previousControls .expressionReindex previous.result previousWorld] := by
  simp only [OriginalApplicationTypeRouteSide.predecessorRoute,
    OriginalApplicationTypeRouteSide.resultFromAssignedRoute,
    OriginalApplicationTypeRouteSide.predecessorWorldInputs]
  rw [trans_worldReserve, trans_worldReserve, same_worldReserve, assigned_worldReserve, same_worldReserve]
  rfl

noncomputable def OriginalApplicationTypeRouteSide.predecessorWorldInputs_boundary
    {strata : EquationStratification env}
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextControls : OriginalWorldControls strata next.sourceEnv)
    (previousControls : OriginalWorldControls strata previous.sourceEnv)
    (nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (previousWorld : WorldEnvironmentProvenance strata U (previousFrame.realization.frame.dependencyEnvironment previousOrdered))
    (compatible : nextControls.cutoff = previousControls.cutoff ∧ nextControls.fuel = previousControls.fuel) :
    (next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).WorldBoundary
      (next.predecessorWorldInputs previous same nextOrdered previousOrdered nextFrame previousFrame
        nextControls previousControls nextWorld previousWorld)
      nextControls previousControls nextWorld previousWorld := by
  exact .trans
    (.same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩)
    (.trans (.assigned _ _ _ _ _ _ _ _ _ compatible) (.same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩))

/-- The next literal Pi keeps the SAME captured ledger. Only its original
context proof is transported, exactly as in the existing native cursor. -/
noncomputable def nativeHeaderWorldInputs
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered)) :
    (nativeHeaderRoute initial start graph frame controls.ordered).WorldInputs strata :=
  (controls, controls, captured,
    transportWorld (nativeHeaderFrame_environment initial start graph frame controls.ordered).symm captured)

theorem nativeHeaderWorldInputs_worlds
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered)) :
    ((nativeHeaderRoute initial start graph frame controls.ordered).worldReserve
      (nativeHeaderWorldInputs initial start graph frame controls captured)).worlds =
      [originalCallWorld controls .expressionReindex node captured,
       originalCallWorld controls .expressionReindex (nativeHeaderSide initial start graph).display.node captured] := by
  change ((RawGeneratedTypeRoute.same (.ofOccurrence initial start graph)
    (nativeHeaderSide initial start graph).display controls.ordered controls.ordered
    (frame.realization.frame.dependencyEnvironment controls.ordered)
    (nativeHeaderFrame initial start graph frame)).worldReserve
      (controls, controls, captured,
        transportWorld (nativeHeaderFrame_environment initial start graph frame controls.ordered).symm captured)).worlds = _
  rw [same_worldReserve, transportWorld_call]
  rfl


noncomputable def nativeHeaderWorldInputs_boundary
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered)) :
    (nativeHeaderRoute initial start graph frame controls.ordered).WorldBoundary
      (nativeHeaderWorldInputs initial start graph frame controls captured) controls controls captured
      (transportWorld (nativeHeaderFrame_environment initial start graph frame controls.ordered).symm captured) :=
  .same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩

/-- Expose the next actual Pi while transporting the SAME selected world
ledger. Its two calls use the original earlier source, including all previous
captures; they need no source proof reconstructed at a substituted type. -/
theorem OriginalNestedDisplay.nativePiCursorWorld
    {sourceEnv : VEnv}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv familyName familyInfo)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerType)
    (callerCaptured : WorldEnvironmentProvenance strata U callerEnvironment)
    (display : OriginalNestedDisplay U common expression assigned)
    (sourceEqual : display.sourceEnv = origin.source)
    (shape : display.sourceExpression = .forallE A B)
    (ordered : display.sourceEnv.Ordered)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight display.graph frame.realization.frame.raw)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment ordered))
    (inherited : Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] world.worlds) :
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
        (∃ domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u), side.domain = .ref domain) ∧
        ∃ nextWorld : WorldEnvironmentProvenance strata U (nextFrame.realization.frame.dependencyEnvironment sideOrdered),
          nextWorld.worlds = world.worlds ∧
          ∃ inputs : route.WorldInputs strata,
            Sponsored [originalCallWorld controls .assignedComparison caller callerCaptured] (route.worldReserve inputs).worlds ∧
            ∃ nextControls : OriginalWorldControls strata side.sourceEnv,
              Nonempty (route.WorldBoundary inputs (sourceEqual.symm ▸ controls.atHeader origin)
                nextControls world nextWorld) := by
  rcases display with ⟨headerEnv, source, sourceExpression, sourceType, context, node,
    provenance, raw, graph, expressionEq, typeEq⟩
  dsimp only at sourceEqual shape ordered frame generated world inherited ⊢
  subst headerEnv
  subst sourceExpression
  cases expressionEq
  cases typeEq
  rcases provenance with ⟨rootSource, rootExpression, rootType, root, initial, start, contextEq⟩
  cases contextEq
  let side := nativeHeaderSide initial start graph
  let nextFrame := nativeHeaderFrame initial start graph frame
  let nextWorld := transportWorld (nativeHeaderFrame_environment initial start graph frame ordered).symm world
  refine ⟨side, ordered, nextFrame, nativeHeaderRoute initial start graph frame ordered,
    nativeHeaderRoute_ambientGenerated initial start graph frame ordered generated,
    rfl, rfl, rfl, rfl, nativeHeaderFrame_ambientGenerated initial start graph frame generated,
    nativeHeaderFrame_environment initial start graph frame ordered,
    (piPrefix start).view.location.originalDomains.1, nextWorld, ?_,
    nativeHeaderWorldInputs initial start graph frame (controls.atHeader origin) world, ?_,
    controls.atHeader origin, ⟨nativeHeaderWorldInputs_boundary initial start graph frame
      (controls.atHeader origin) world⟩⟩
  · exact transportWorld_worlds _ world
  · rw [nativeHeaderWorldInputs_worlds]
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin node world
        caller callerCaptured _ _ inherited⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin side.display.node world
        caller callerCaptured _ _ inherited⟩

section Successor
variable {strata : EquationStratification env}
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

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  majorLocation priorReady wholeReady in
/-- Actual source occurrences pay the seed's new R pair. Header-domain
reframing uses earlier constants and the SAME inherited prefix worlds. -/
theorem OriginalApplyPiHistory.argumentSeedWorld_sponsored :
    Sponsored [callerWorld]
      (history.argumentSeedWorld controls headerControls sourceWorld priorWorld wholeInputs).worlds := by
  rw [history.argumentSeedWorld_worlds]
  apply Sponsored.merge
  · apply Sponsored.merge
    · intro child member
      simp only [transportWorld_call, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
          (.assignedFormation (.appArgument location)) controls captured _ _⟩
      · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
          (.appDomain location) controls captured _ _⟩
    · exact wholeReady
  · intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
        (headerSide).domain priorWorld outer captured _ _ priorReady⟩
    · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
        (.ref history.rightDomain) priorWorld outer captured _ _ priorReady⟩

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  fieldEq majorLocation priorReady wholeReady in
/-- The computed fixed output envelope is sponsored by the actual outer
projection. Its larger capture capacity does not introduce a new sponsor. -/
theorem OriginalApplyPiHistory.outputWorld_sponsored :
    Sponsored [callerWorld]
      (history.outputWorld field major controls headerControls captured sourceWorld priorWorld wholeInputs).worlds := by
  have fieldReady : Sponsored [callerWorld] [originalCallWorld controls .expressionReindex (.ref field) captured] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, ProjectionHead.parameterOwner_below head field fieldEq .here controls captured _ _⟩
  have majorReady : Sponsored [callerWorld] [originalCallWorld controls .expressionReindex (.ref major) captured] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, ProjectionHead.parameter_below head majorLocation controls captured _ _⟩
  have domainReady : Sponsored [callerWorld]
      [originalCallWorld headerControls .expressionReindex (.ref history.rightDomain) priorWorld] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
      (.ref history.rightDomain) priorWorld outer captured _ _ priorReady⟩
  exact WorldEnvironmentProvenance.groupHistory_sponsored controls headerControls captured priorWorld
    fieldReady majorReady domainReady priorReady _
      (history.argumentSeedWorld_sponsored head majorLocation controls captured origin initial domain body function argument result
        hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
        sourceEnvironment priorWorld priorReady wholeInputs wholeReady)

variable
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : origin.source ≤ env)

noncomputable def OriginalApplyPiHistory.applyWorldInputs :
    (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      noBinders ownerInitial sourceBound headerBelow).WorldInputs strata :=
  (controls, headerControls, sourceWorld, priorWorld, wholeInputs)

theorem OriginalApplyPiHistory.applyWorldInputs_worlds :
    ((history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      noBinders ownerInitial sourceBound headerBelow).worldReserve
        (history.applyWorldInputs (field := field) head controls captured origin initial domain body function argument result hu hv location
          sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
          sourceEnvironment priorWorld wholeInputs noBinders sourceBound headerBelow)).worlds =
      (history.whole.worldReserve wholeInputs).worlds ++
      [originalCallWorld controls .fundamental (sourceSide).node sourceWorld,
       originalCallWorld controls .fundamental (sourceSide).node sourceWorld,
       originalCallWorld headerControls .fundamental (headerSide).display.node priorWorld,
       originalCallWorld headerControls .fundamental (headerSide).display.node priorWorld] := by
  simp only [OriginalApplyPiHistory.applyRoute, OriginalApplyPiHistory.applyWorldInputs,
    RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def _)]
  rw [WorldEnvironmentProvenance.worlds_append]
  rfl

include majorLocation priorReady wholeReady in
theorem OriginalApplyPiHistory.applyWorldInputs_sponsored :
    Sponsored [callerWorld]
      ((history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
        headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
        noBinders ownerInitial sourceBound headerBelow).worldReserve
          (history.applyWorldInputs (field := field) head controls captured origin initial domain body function argument result hu hv location
            sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
            sourceEnvironment priorWorld wholeInputs noBinders sourceBound headerBelow)).worlds := by
  rw [history.applyWorldInputs_worlds (field := field) head controls captured origin initial domain body function argument result
    hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    sourceEnvironment priorWorld wholeInputs noBinders sourceBound headerBelow]
  apply wholeReady.merge
  intro child member
  simp only [transportWorld_call, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation location controls captured _ _⟩
  · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation location controls captured _ _⟩
  · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
      (headerSide).display.node priorWorld outer captured _ _ priorReady⟩
  · exact ⟨_, List.mem_singleton_self _, originalRetainedHeader_below controls origin
      (headerSide).display.node priorWorld outer captured _ _ priorReady⟩

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  fieldEq majorLocation priorReady wholeReady wholeBoundary noBinders sourceBound headerBelow sourceEnvironment in
/-- The actual application specialization and its independently selected
captured frame retain one coherent annotation at their shared endpoint.
No universe-history size bound or completed next-history callback is used. -/
theorem OriginalApplyPiHistory.generatedSuccessorWorld
    (generated : history.AmbientGenerated base commonCaps)
    (replayed : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile)
    (selected : WorldEnvironmentProvenance strata U
      (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered))
    (selectedReady : Sponsored [callerWorld] selected.worlds) :
    ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (sourceSide).resultDisplay history.destination
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)
        (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered),
      route.AmbientGenerated base commonCaps ∧
      route.reserve = history.reserve ++
        [Closure.bundle
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (history.outputEnvironment field major ownerInitial))
          (.close (history.destination.node.dependencyOrigin history.rightOrdered)
            (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered))] ∧
      ∃ inputs : route.WorldInputs strata, Sponsored [callerWorld] (route.worldReserve inputs).worlds ∧
        Nonempty (route.WorldBoundary inputs controls headerControls sourceWorld selected) := by
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
    let applicationInputs := history.applyWorldInputs (field := field) head controls captured origin initial domain body function argument result hu hv location
      sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceEnvironment priorWorld wholeInputs noBinders sourceBound headerBelow
    let envelope := history.outputWorld field major controls headerControls captured (transportWorld sourceEnvironment.symm captured) priorWorld wholeInputs
    let reframeInputs : reframe.WorldInputs strata := (headerControls, headerControls, envelope, selected)
    have applicationGenerated := history.applyRoute_ambientGenerated (field := field) initial domain body function argument result
      hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      noBinders ownerInitial sourceBound headerBelow generated
    have reframeGenerated : reframe.AmbientGenerated base commonCaps := by
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [reframe]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
      · dsimp only [reframe]; rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨headerBelow, headerBelow⟩
      · intro boxed member
        dsimp only [reframe] at member
        rw [RawGeneratedTypeRoute.frames.eq_def] at member
        cases List.mem_singleton.mp member
        exact replayed.generation
    dsimp only [originalApplicationTypeRouteSide, originalNativePiRouteSide] at *
    refine ⟨application.trans reframe, applicationGenerated.trans reframeGenerated, ?_,
      trans_worldInputs applicationInputs reframeInputs, ?_, ⟨?_⟩⟩
    · rw [route_reserve_trans]
      rw [history.applyRoute_reserve (field := field) initial domain body function argument result hu hv location sourceGraph
        headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow]
      exact congrArg (fun reserve => history.reserve ++ reserve)
        (route_reserve_same history.destination history.destination rightOrdered rightOrdered
          (history.outputEnvironment field major ownerInitial) replayed.captureFrame)
    · rw [trans_worldReserve]
      apply Sponsored.merge
      · exact history.applyWorldInputs_sponsored head majorLocation controls captured origin initial domain body function argument result
          hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
          sourceEnvironment priorWorld priorReady wholeInputs wholeReady noBinders sourceBound headerBelow
      · dsimp only [reframe, reframeInputs]
        rw [same_worldReserve history.destination history.destination rightOrdered rightOrdered
          (history.outputEnvironment field major ownerInitial) replayed.captureFrame
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
    · apply RawGeneratedTypeRoute.WorldBoundary.trans
      · exact .applyPi initial domain body function argument result hu hv location sourceGraph noBinders
          headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph leftOrdered rightOrdered
          leftBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound whole _
          controls headerControls (transportWorld sourceEnvironment.symm captured) priorWorld captured
          (by rw [transportWorld_worlds]; exact Covered.refl _) wholeInputs
          wholeBoundary (by
            simp only [OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
              RawGeneratedTypeRoute.reserve, history, originalNativePiRouteSide,
              EndpointState.dependencyOrigin, OriginalApplyPiHistory.final]
            rfl)
      · exact .same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩

include initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  fieldEq majorLocation priorReady wholeReady wholeBoundary noBinders sourceBound headerBelow sourceEnvironment in
/-- The dependent next history is built from the actual next application and
literal next header Pi. All new reserves have original sponsors; the selected
capture's annotated ledger is retained verbatim at the reframe/exposure join. -/
theorem OriginalApplyPiHistory.nextParameterWorld
    (generated : history.AmbientGenerated base commonCaps)
    (replayed : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile)
    (selected : WorldEnvironmentProvenance strata U
      (replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered))
    (selectedReady : Sponsored [callerWorld] selected.worlds)
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
    (nextGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight nextGraph nextFrame.realization.frame.raw)
    (nextEnvironment : nextFrame.realization.frame.dependencyEnvironment controls.ordered = ownerInitial)
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
        nextHistory.final = replayed.captureFrame.realization.frame.dependencyEnvironment history.rightOrdered ∧
        ∃ nextWorld : WorldEnvironmentProvenance strata U nextHistory.final,
          nextWorld.worlds = selected.worlds ∧ Sponsored [callerWorld] nextWorld.worlds ∧
          ∃ inputs : nextHistory.whole.WorldInputs strata,
            Sponsored [callerWorld] (nextHistory.whole.worldReserve inputs).worlds ∧
            ∃ nextSourceEnvironment : nextHistory.sourceFrame.realization.frame.dependencyEnvironment
                nextHistory.leftOrdered = ownerInitial,
            ∃ nextControls : OriginalWorldControls strata nextHeader.sourceEnv,
              Nonempty (nextHistory.whole.WorldBoundary inputs controls nextControls
                (transportWorld nextSourceEnvironment.symm captured) nextWorld) := by
  let next := originalApplicationTypeRouteSide initial nextDomainRef nextBodyNode nextFunction nextArgument
    nextResult nextHu nextHv nextLocation nextGraph
  obtain ⟨completed, completedGenerated, _completedReserve, completedInputs, completedReady, ⟨completedBoundary⟩⟩ :=
    history.generatedSuccessorWorld head fieldEq majorLocation controls captured origin initial domain body function argument result
      hu hv location sourceGraph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceEnvironment priorWorld priorReady wholeInputs wholeReady wholeBoundary noBinders sourceBound headerBelow
      generated replayed selected selectedReady
  obtain ⟨nextHeader, nextHeaderOrdered, nextHeaderFrame, exposeHeader, exposeGenerated,
      headerSource, headerDomainShape, headerBodyShape, headerRawShape, headerGenerated, headerFrameEq,
      ⟨nextDomainOriginal, nextDomainEq⟩, nextWorld, nextWorlds, exposeInputs, exposeReady, nextControls, ⟨exposeBoundary⟩⟩ :=
    history.destination.nativePiCursorWorld controls origin outer captured rfl headerShape history.rightOrdered
      replayed.captureFrame replayed.generation selected selectedReady
  let nextWorldSource := transportWorld nextEnvironment.symm captured
  let predecessor := next.predecessorRoute sourceSide adjacent controls.ordered history.leftOrdered nextFrame history.sourceFrame
  let predecessorInputs := next.predecessorWorldInputs sourceSide adjacent controls.ordered history.leftOrdered nextFrame
    history.sourceFrame controls controls nextWorldSource sourceWorld
  have predecessorGenerated := next.predecessorRoute_ambientGenerated sourceSide adjacent controls.ordered history.leftOrdered
    nextFrame history.sourceFrame nextGenerated generated.source
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
  let nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader :=
    ⟨controls.ordered, nextHeaderOrdered, history.leftBelow, nextDomainOriginal, nextDomainEq,
      nextFrame, nextHeaderFrame, whole⟩
  refine ⟨nextHeader, nextHistory, ⟨nextGenerated, headerGenerated,
    (predecessorGenerated.trans completedGenerated).trans exposeGenerated⟩,
    rfl, headerSource, ?_, headerDomainShape, headerBodyShape, headerRawShape, headerFrameEq,
    nextWorld, nextWorlds, ?_, trans_worldInputs (trans_worldInputs predecessorInputs completedInputs) exposeInputs, ?_,
    nextEnvironment, nextControls, ⟨?_⟩⟩
  · rw [headerSource]
    exact headerBelow
  · rw [nextWorlds]
    exact selectedReady
  · rw [trans_worldReserve, trans_worldReserve]
    exact (predecessorReady.merge completedReady).merge exposeReady
  · exact .trans
      (.trans (next.predecessorWorldInputs_boundary sourceSide adjacent controls.ordered history.leftOrdered
        nextFrame history.sourceFrame controls controls nextWorldSource sourceWorld ⟨rfl, rfl⟩) completedBoundary)
      exposeBoundary

end Successor

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
