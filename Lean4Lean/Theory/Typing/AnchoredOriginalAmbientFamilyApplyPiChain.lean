import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayData
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain

/-! Positive generation along the actual counted application successor.
The next header baseline is the concrete replayed frame, not its capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private routeFrame_recontext piPrefix_context route_reserve_trans route_reserve_same
  from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

private theorem routeFrame_recontext_ambientGenerated
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    AmbientCaptureGenerated base commonCaps commonLeft commonRight (equal ▸ graph)
      (routeFrame_recontext equal frame).realization.frame.raw := by
  cases equal
  exact generated

theorem nativeHeaderFrame_ambientGenerated
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    AmbientCaptureGenerated base commonCaps commonLeft commonRight (nativeHeaderSide initial start graph).graph
      (nativeHeaderFrame initial start graph frame).realization.frame.raw :=
  routeFrame_recontext_ambientGenerated _ frame generated

theorem nativeHeaderRoute_ambientGenerated
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (start : Located root node)
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    (nativeHeaderRoute initial start graph frame ordered).AmbientGenerated base commonCaps := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nativeHeaderRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    trivial
  · rw [nativeHeaderRoute, RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨generated.ambient.1.below, generated.ambient.1.below⟩
  · intro boxed member
    rw [nativeHeaderRoute, RawGeneratedTypeRoute.frames.eq_def] at member
    cases List.mem_singleton.mp member
    exact nativeHeaderFrame_ambientGenerated initial start graph frame generated

theorem OriginalApplicationTypeRouteSide.predecessorRoute_ambientGenerated
    (next previous : OriginalApplicationTypeRouteSide U common)
    (same : (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw)
    (nextOrdered : next.sourceEnv.Ordered) (previousOrdered : previous.sourceEnv.Ordered)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (previousFrame : OriginalTypeRouteFrame env registry target previous.graph commonLeft commonRight)
    (nextGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight next.graph nextFrame.realization.frame.raw)
    (previousGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight previous.graph previousFrame.realization.frame.raw) :
    (next.predecessorRoute previous same nextOrdered previousOrdered nextFrame previousFrame).AmbientGenerated base commonCaps := by
  refine ⟨(next.predecessorRoute_generated previous same nextOrdered previousOrdered nextFrame previousFrame
    nextGenerated.capped previousGenerated.capped).wellFormed, ?_, ?_⟩
  · simp only [OriginalApplicationTypeRouteSide.predecessorRoute,
      OriginalApplicationTypeRouteSide.resultFromAssignedRoute, RawGeneratedTypeRoute.Ambient.eq_def]
    have nextBelow := nextGenerated.ambient.1.below
    have previousBelow := previousGenerated.ambient.1.below
    exact ⟨⟨nextBelow, nextBelow⟩, ⟨⟨nextBelow, previousBelow⟩, ⟨previousBelow, previousBelow⟩⟩⟩
  · intro boxed member
    simp only [OriginalApplicationTypeRouteSide.predecessorRoute,
      OriginalApplicationTypeRouteSide.resultFromAssignedRoute, RawGeneratedTypeRoute.frames.eq_def,
      List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact nextGenerated
    · exact previousGenerated
    · exact previousGenerated

noncomputable abbrev AmbientApplyPiReplayResult.captureFrame
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
    {field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType}
    {major : EndpointRef left.sourceEnv U left.source majorExpression majorType}
    (replayed : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
    OriginalTypeRouteFrame env registry target history.destination.graph commonLeft commonRight :=
  replayed.toOriginalApplyPiReplayResult.captureFrame

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

theorem OriginalApplyPiHistory.applyRoute_ambientGenerated
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.AmbientGenerated base commonCaps) : (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).AmbientGenerated base commonCaps := by
  refine ⟨history.applyRoute_wellFormed (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
    generated.whole.wellFormed, ?_, ?_⟩
  · rw [OriginalApplyPiHistory.applyRoute, RawGeneratedTypeRoute.Ambient.eq_def]
    exact generated.whole.ambient
  · intro boxed member
    rw [history.applyRoute_frames (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow] at member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact generated.source
    · exact generated.header
    · exact generated.whole.frames boxed member

theorem OriginalApplyPiHistory.generatedSuccessorAmbient
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.AmbientGenerated base commonCaps)
    (replayed : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
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
    refine ⟨.trans application reframe, ?_, ?_⟩
    · apply RawGeneratedTypeRoute.AmbientGenerated.trans
      · exact history.applyRoute_ambientGenerated (field := field) initial domain body function argument result hu hv location sourceGraph
          headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow generated
      · refine ⟨?_, ?_, ?_⟩
        · dsimp only [reframe]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
        · dsimp only [reframe]; rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨headerBelow, headerBelow⟩
        · intro boxed member
          dsimp only [reframe] at member
          rw [RawGeneratedTypeRoute.frames.eq_def] at member
          cases List.mem_singleton.mp member
          exact replayed.generation
    · rw [route_reserve_trans]
      rw [history.applyRoute_reserve (field := field) initial domain body function argument result hu hv location sourceGraph
        headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow]
      dsimp only [reframe]
      exact congrArg (fun reserve => history.reserve ++ reserve)
        (route_reserve_same history.destination history.destination rightOrdered rightOrdered
          (history.outputEnvironment field major ownerInitial) replayed.captureFrame)


end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
