import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryGroupActivation

/-! Bootstrap a declaration capture from its actual empty original argument query.
The existing history interpreter computes owner F and declaration alignment; no
completed value, alignment, or incoming observer is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private replyOfFrame from Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryUnweaken
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem generatedEmptyHistoryCaptureWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    {ownerContext : ContextDerivation sourceEnv U source}
    (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (nominalProvenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (frontier parent : List (World strata.rules.length))
    (seedWorld : WorldGenerated strata P base scope.caps scope.left scope.right scope.graph seed.frame.raw sourceControls)
    (seedReplayable : seedWorld.Replayable)
    (seedArgument : seed.owner.Argument)
    (seedHereditary : seedWorld.Hereditary frontier)
    (seedReady : seedWorld.Controlled frontier)
    (seedCompatible : seedWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (seedQueryReady : ControlledStoredQuery sourceControls frontier (.observation seed.query))
    (domainProvenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (priorWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph prior.frame.raw headerControls)
    (priorReplayable : priorWorld.Replayable)
    (priorHereditary : priorWorld.Hereditary frontier)
    (priorReady : priorWorld.Controlled frontier)
    (priorCompatible : priorWorld.UsesControlPrefix headerControls.cutoff headerControls.fuel)
    (history : OriginalSeedTypeHistory seed scope.toOriginalOwnerScope graph domainProvenance prior
      sourceControls.ordered headerControls.ordered)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment sourceControls.ordered) ×
      WorldEnvironmentProvenance strata U (prior.frame.dependencyEnvironment headerControls.ordered))
    (baselineCoverage : Covered (@EquationControlMeasure.Less strata.rules.length) seedWorld.worlds baselines.1.worlds ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) priorWorld.worlds baselines.2.worlds)
    (seedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      baselines.1.worlds (seed.owner.worldEnvironment sourceControls initial).worlds)
    (routeData : history.route.ControlledWorldData P base scope.caps sourceControls.cutoff sourceControls.fuel frontier)
    (boundary : history.route.WorldBoundary routeData.inputs sourceControls headerControls baselines.1 baselines.2)
    (coherent : boundary.FrameOccurrenceCoherent routeData.controls routeData.frames)
    (ownerAmbient : ownerGraph.Ambient env) (ownerSources : ownerGraph.AllSources P)
    (nominalAmbient : nominalGraph.Ambient env) (nominalSources : nominalGraph.AllSources P)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (ownerSponsored : Sponsored frontier [originalCallWorld sourceControls .fundamental seed.owner.node
      (seed.owner.worldEnvironment sourceControls initial)])
    (ownerSmaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld sourceControls .fundamental seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)]) parent)
    (routeSponsored : Sponsored frontier (history.route.worldReserve routeData.inputs).worlds)
    (routeSmaller : CallBelow strata.rules.length
      (frontier ++ (history.route.worldReserve routeData.inputs).worlds) parent)
 :
    let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
      initial baselines.2 (history.route.worldReserve routeData.inputs)
    Nonempty (WorldVariableDemandReply P base commonCaps
      (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight
      headerControls reserve frontier 0 (Profile.empty : Profile 0)) := by
  let empty : RichGradedResult sourceEnv env U registry target seed.owner.node
      seed.ownerLocals seed.ownerLeft seed.ownerAvailable (Profile.empty : Profile 0) := {
    rank := 0, bound := Nat.le_refl _, raw := .empty, footprint := []
    observation := .legacy (.legacy .empty)
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ member => nomatch member
    live := Profile.Live.empty }
  have emptyReady : ControlledStoredQuery sourceControls frontier (.observation empty.observation) := {
    annotation := .empty
    within := by
      intro control active
      simp only [empty, StoredOriginalQuery.headDepth, RichObs.headDepth, SortableObs.headDepth]
      rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := by intro child member; cases member }
  obtain ⟨selected, selectedData, _, _, _, _, _, _⟩ := replyOfFrame
    (seed.seedDisplay scope.graph) sourceControls baselines.1 frontier seed.frame seedWorld
    seedReplayable seedReady seedCompatible seedHereditary seed.substitutions seed.ownerClosed
    empty emptyReady (fun _ => Nat.le_refl _) baselineCoverage.1
  exact generatedWorldHistoryGroupDemand ownerGraph nominalGraph nominal nominalProvenance displayed seed scope
    sourceControls headerControls frontier parent seedWorld seedReplayable seedArgument seedHereditary seedReady
    seedCompatible seedQueryReady domainProvenance prior priorWorld priorReplayable priorHereditary priorReady
    priorCompatible history initial baselines baselineCoverage seedCovered routeData boundary coherent
    ownerAmbient ownerSources nominalAmbient nominalSources henv hscoped formed bank unary ownerSponsored
    ownerSmaller routeSponsored routeSmaller selected selectedData

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
