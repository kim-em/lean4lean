import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryHereditary
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldSeedArgumentFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedVariableDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedSeedData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldScopedSeedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldScopedSeedAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRawTypeRouteReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGroupCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyEntryRestriction
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryWorlds

/-! A selected capture query is interpreted at its actual original owner and
then transported through its retained finite type history. The seed and header
baselines remain fixed when recursive calls select different resource tables. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6400000
variable {headerAvailable : Valuation}

private noncomputable def variableReady
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlEnv)
    (frontier : List (World strata.rules.length))
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} (profile : Profile n) :
    ControlledStoredQuery controls frontier (.observation
      (RichObs.legacy (env := env) (registry := registry) (target := target) (node := node) (.legacy (.var locals σ index profile)))) := {
  annotation := .var
  within := by
    intro control active
    simp only [StoredOriginalQuery.headDepth, RichObs.headDepth, SortableObs.headDepth]
    rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
    exact Nat.zero_le _
  sponsored := by intro child member; cases member }

private theorem realizeHistoryFrame
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.raw controls)
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ result : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available,
      ∃ next : WorldGenerated strata P base caps commonLeft commonRight graph result.frame.raw controls,
        ∃ nextH : next.Hereditary frontier,
        next.worlds = generated.worlds ∧ Nonempty (next.Controlled frontier) ∧
        next.UsesControlPrefix controls.cutoff controls.fuel ∧
        (∀ ordered : sourceEnv.Ordered, result.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered) ∧
        (next.Replayable ↔ generated.Replayable) := by
  obtain ⟨left, right⟩ := generated.erase.ambientGenerated.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, hereditary, rfl, ⟨ready⟩, compatible, (fun _ => rfl), Iff.rfl⟩

private theorem seedReindexBelowHistory
    {strata : EquationStratification env} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {owner : HeaderOwner field major}
    (argument : owner.Argument)
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (seed : WorldEnvironmentProvenance strata U seedEnvironment)
    (route : WorldEnvironmentProvenance strata U routeEnvironment)
    (tail : WorldEnvironmentProvenance strata U tailEnvironment)
    (node : EndpointState headerEnv U current expression assigned) (phase : RichPhase)
    (capacity : environmentCost seedEnvironment ≤ environmentCost (owner.dependencyEnvironment sourceControls.ordered ownerInitial))
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) seed.worlds
      (owner.worldEnvironment sourceControls initial).worlds) :
    WorldBelow strata.rules.length
      (originalCallWorld sourceControls .expressionReindex owner.node seed)
      (originalCallWorld headerControls phase node
        ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial prior route).append tail)) := by
  obtain ⟨root, member, lower⟩ := argument.reindex_below_root sourceControls initial seed capacity covered
  apply Below.under (child := root) _ lower
  change root ∈ ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial prior route).append tail).worlds
  rw [WorldEnvironmentProvenance.worlds_append, WorldEnvironmentProvenance.groupHistory,
    WorldEnvironmentProvenance.worlds_append]
  apply List.mem_append_left
  apply List.mem_append_right
  apply WorldEnvironmentProvenance.replayRoots_subset_groupBaseline
  exact List.mem_append_left _ (List.mem_cons_of_mem _ member)

private theorem prefixCall {count : Nat} {calls before : List (World count)}
    (smaller : CallBelow count calls before) (frontier : List (World count)) :
    CallBelow count (frontier ++ calls) (frontier ++ before) := by
  induction frontier with
  | nil => exact smaller
  | cons head tail ih => exact ih.cons head

/-- The selected owner answer is computed by unary F; its actual assigned
certificate is then the input to the structural history interpreter. Neither
an alignment nor a completed route answer is an input. -/
theorem PendingRichCapture.replaySelectedWorldHistory
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedCapped : CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (history : OriginalSeedTypeHistory seed scope.toOriginalOwnerScope graph domainProvenance prior
      sourceControls.ordered headerControls.ordered)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment sourceControls.ordered) ×
      WorldEnvironmentProvenance strata U (prior.frame.dependencyEnvironment headerControls.ordered))
    (seedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      baselines.1.worlds (seed.owner.worldEnvironment sourceControls initial).worlds)
    (inputs : history.route.WorldInputs strata)
    (boundary : history.route.WorldBoundary inputs sourceControls headerControls baselines.1 baselines.2)
    (generated : history.route.SourceGenerated P base scope.caps)
    (frontier parent : List (World strata.rules.length))
    (execution : boundary.ExecutionFrames P base scope.caps frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (ownerSponsored : Sponsored frontier [originalCallWorld sourceControls .fundamental seed.owner.node
      (seed.owner.worldEnvironment sourceControls initial)])
    (ownerSmaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld sourceControls .fundamental seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)]) parent)
    (routeSponsored : Sponsored frontier (history.route.worldReserve inputs).worlds)
    (routeSmaller : CallBelow strata.rules.length
      (frontier ++ (history.route.worldReserve inputs).worlds) parent)
    (selected : AmbientBoundedGeneratedQueryReply base scope.caps (seed.seedDisplay scope.graph)
      scope.left scope.right (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment sourceControls.ordered)))
    (selectedData : WorldGeneratedQueryReplyData (P := P) sourceControls baselines.1 frontier selected) :
    let pending := seed.requery scope.graph seedCapped sourceControls.ordered selected.toBoundedGeneratedQueryReply
    ∃ value : RichComputationalValue sourceEnv env U registry target pending.owner.node
        pending.ownerLocals pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input,
      Nonempty (ControlledStoredQuery sourceControls frontier (.certificate value.certificate)) ∧
      ∃ chosen : AmbientBoundedGeneratedQueryReply base commonCaps
        (graph.parameterCellDisplay domain domainProvenance) commonLeft commonRight value.support
        (environmentCost (prior.frame.dependencyEnvironment headerControls.ordered)),
      ∃ chosenData : WorldGeneratedQueryReplyData (P := P) headerControls baselines.2 frontier chosen,
      ∃ alignment : HeaderValueAlignment pending.owner domain env registry target
        pending.ownerLocals chosen.answer.reply.locals pending.ownerLeft pending.ownerRight
        (raw.comp commonLeft) pending.ownerAvailable chosen.answer.reply.available pending.input,
        alignment.value = value.toRichBinderValue ∧
        Nonempty (ControlledStoredQuery headerControls frontier (.certificate alignment.aligned.certificate)) := by
  dsimp only
  let pending := seed.requery scope.graph seedCapped sourceControls.ordered selected.toBoundedGeneratedQueryReply
  have ownerCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selectedData.generation.worlds (seed.owner.worldEnvironment sourceControls initial).worlds :=
    Covered.trans EquationControlMeasure.less_trans selectedData.covered seedCovered
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated pending.frame selectedData.generation selectedData.controlled
    selectedData.replayable selectedData.compatible selectedData.hereditary
  obtain ⟨value, ⟨valueReady⟩, _⟩ := (unary _ ownerSmaller).computational pending.owner.node
    (pending.owner.provenance pending.initialContext) sourceControls pending.frame selectedData.generation.environment
    (seed.owner.worldEnvironment sourceControls initial) frontier (pending.frame_environment_le sourceControls.ordered)
    ownerCovered rfl ownerSponsored frameData pending.ownerClosed formed pending.substitutions
    pending.query pending.queryAvailable selectedData.query
  obtain ⟨incoming, ⟨incomingData⟩⟩ := pending.worldAssignedInput scope sourceControls baselines.1 frontier
    selectedData.generation selectedData.replayable selectedData.controlled selectedData.compatible selectedData.hereditary
    selected.bounded selectedData.covered value.toRichSupportedValue valueReady
  obtain ⟨transported, ⟨transportedData⟩⟩ := boundary.replayWorld generated execution henv hscoped formed
    parent bank unary routeSponsored routeSmaller incoming incomingData value.certificate.formed
  obtain ⟨chosen, chosenData, alignment, sameValue, alignmentReady, _⟩ :=
    pending.worldAlignmentOfReply scope domainProvenance headerControls baselines.2 frontier henv
      value.toRichSupportedValue transported transportedData
  exact ⟨value, ⟨valueReady⟩, chosen, chosenData, alignment, sameValue, alignmentReady⟩


/-- Requerying a dormant history constructs a fresh singleton capture with an
ordinary variable observer. The fixed history reserve bounds both its numeric
capacity and its hereditary worlds. -/
theorem generatedWorldHistoryGroupDemand
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
    (selected : AmbientBoundedGeneratedQueryReply base scope.caps (seed.seedDisplay scope.graph)
      scope.left scope.right (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment sourceControls.ordered)))
    (selectedData : WorldGeneratedQueryReplyData (P := P) sourceControls baselines.1 frontier selected) :
    let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
      initial baselines.2 (history.route.worldReserve routeData.inputs)
    Nonempty (WorldVariableDemandReply P base commonCaps
      (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight
      headerControls reserve frontier 0 requested) := by
  dsimp only
  let pending := seed.requery scope.graph seedWorld.erase.ambientGenerated.capped sourceControls.ordered
    selected.toBoundedGeneratedQueryReply
  obtain ⟨value, ⟨valueReady⟩, chosen, chosenData, alignment, valueEq, ⟨alignedReady⟩⟩ :=
    seed.replaySelectedWorldHistory scope seedWorld.erase.ambientGenerated.capped domainProvenance prior
      sourceControls headerControls history initial baselines seedCovered routeData.inputs boundary routeData.generated
      frontier parent (boundary.executionFramesOfData routeData coherent) henv hscoped formed bank unary
      ownerSponsored ownerSmaller routeSponsored routeSmaller selected selectedData
  have ownerSame : sourceControls.HasPrefix headerControls.cutoff headerControls.fuel := boundary.controls_match
  have ownerCompatible : selectedData.generation.UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    simpa only [← ownerSame.1, ← ownerSame.2] using selectedData.compatible
  let current := pending.reheader chosen.answer.reply.locals (raw.comp commonLeft) chosen.answer.reply.available
  let entry := current.complete alignment
  let entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      chosen.answer.reply.locals (raw.comp commonLeft) chosen.answer.reply.available ownerInitial
      rawCapture leftValue rightValue := [entry]
  have actualValueReady : ControlledStoredQuery headerControls frontier (.certificate alignment.value.certificate) := by
    rw [valueEq]
    exact valueReady.recontrol headerControls ownerSame.1 ownerSame.2
  let packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight commonCaps
      headerControls sourceControls frontier entry :=
    ⟨scope, selectedData.generation, selectedData.replayable, selectedData.controlled, ownerCompatible,
      selectedData.query.recontrol headerControls ownerSame.1 ownerSame.2, actualValueReady, alignedReady, selectedData.hereditary⟩
  let scopes : ∀ e ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps e.depth
      (e.owner.context e.initialContext) := fun e member => by
    cases List.mem_singleton.mp member
    exact scope
  let owners : ∀ e member, WorldGenerated strata P base (scopes e member).caps (scopes e member).left
      (scopes e member).right (scopes e member).graph e.frame.raw sourceControls := fun e member => by
    have same : e = entry := List.mem_singleton.mp member
    subst e
    exact selectedData.generation
  let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
    baselines.2 (history.route.worldReserve routeData.inputs)
  let frame := (chosen.answer.reply.realization.frame.group domain sourceControls.ordered ownerInitial entries).reserve
    (groupCaptureHistoryReserve field major domain sourceControls.ordered headerControls.ordered ownerInitial
      (prior.frame.dependencyEnvironment headerControls.ordered) history.route.reserve)
  let generation : WorldGenerated strata P base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) frame.raw headerControls :=
    .historyGroup chosenData.generation domain ownerGraph nominalGraph nominal nominalProvenance displayed
      sourceControls.ordered headerControls.ordered ownerInitial seed scope sourceControls seedWorld domainProvenance
      prior history priorWorld initial baselines routeData.inputs routeData.generated.wellFormed routeData.controls routeData.frames
      (chosen.bounded headerControls.ordered) entries scopes sourceControls owners ownerAmbient nominalAmbient
      priorWorld.erase.ambientGenerated.ambient.2 routeData.generated.ambient ownerSources nominalSources
      priorWorld.erase.sources.2 routeData.generated.sources
  have entryReady : ∀ query ∈ (richGroupedEntriesRaw entries).storedQueries,
      Nonempty (ControlledStoredQuery headerControls frontier query) := by
    intro query member
    simp only [entries, richGroupedEntriesRaw, RawRichGroupEntries.storedQueries, List.append_nil] at member
    exact packet.storedReady ownerSame query member
  obtain ⟨generationReady⟩ := WorldGenerated.Controlled.historyGroup chosenData.generation domain ownerGraph
    nominalGraph nominal nominalProvenance displayed sourceControls.ordered headerControls.ordered ownerInitial seed scope
    sourceControls seedWorld domainProvenance prior history priorWorld initial baselines routeData.inputs
    routeData.generated.wellFormed routeData.controls routeData.frames (chosen.bounded headerControls.ordered)
    entries scopes sourceControls owners ownerAmbient nominalAmbient priorWorld.erase.ambientGenerated.ambient.2
    routeData.generated.ambient ownerSources nominalSources priorWorld.erase.sources.2 routeData.generated.sources
    chosenData.controlled entryReady (seedQueryReady.recontrol headerControls ownerSame.1 ownerSame.2)
    seedReady ownerSame priorReady routeData.ready
    (fun i => ⟨(routeData.compatible i).controls_match.1.trans ownerSame.1, (routeData.compatible i).controls_match.2.trans ownerSame.2⟩)
    (by intro e member; cases List.mem_singleton.mp member; exact selectedData.controlled) ownerSame
  let generationHereditary : generation.Hereditary frontier :=
    WorldGenerated.Hereditary.historyGroup chosenData.generation domain ownerGraph nominalGraph nominal nominalProvenance
      displayed sourceControls.ordered headerControls.ordered ownerInitial seed scope sourceControls seedWorld
      domainProvenance prior history priorWorld initial baselines routeData.inputs routeData.generated.wellFormed
      routeData.controls routeData.frames (chosen.bounded headerControls.ordered) entries scopes sourceControls owners
      ownerAmbient nominalAmbient priorWorld.erase.ambientGenerated.ambient.2 routeData.generated.ambient
      ownerSources nominalSources priorWorld.erase.sources.2 routeData.generated.sources
      chosenData.hereditary seedHereditary ownerSame priorHereditary routeData.hereditary
      (fun i => ⟨(routeData.compatible i).controls_match.1.trans ownerSame.1,
        (routeData.compatible i).controls_match.2.trans ownerSame.2⟩)
      (by intro e member; cases List.mem_singleton.mp member; exact selectedData.hereditary) ownerSame
  have ownerCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selectedData.generation.worlds (seed.owner.worldEnvironment sourceControls initial).worlds :=
    Covered.trans EquationControlMeasure.less_trans selectedData.covered seedCovered
  have replayable : generation.Replayable :=
    ⟨chosenData.replayable, seedReplayable, priorReplayable, routeData.replayable,
      (by intro e member; cases List.mem_singleton.mp member; exact selectedData.replayable),
      (by intro e member; cases List.mem_singleton.mp member; exact ownerCovered),
      ⟨seedArgument, seedCovered⟩, baselineCoverage.1, baselineCoverage.2, ⟨boundary, coherent⟩, chosenData.covered⟩
  have compatible : generation.UsesControlPrefix headerControls.cutoff headerControls.fuel :=
    ⟨chosenData.compatible, by
        change seedWorld.UsesControlPrefix headerControls.cutoff headerControls.fuel
        rw [← ownerSame.1, ← ownerSame.2]
        exact seedCompatible,
      priorCompatible, (by
        intro i
        change (routeData.frames i).UsesControlPrefix headerControls.cutoff headerControls.fuel
        rw [← ownerSame.1, ← ownerSame.2]
        exact routeData.compatible i),
      (by intro e member; cases List.mem_singleton.mp member; exact ownerCompatible), ownerSame⟩
  have rawPair := (pending.owner.node.sound.defeq.mono selectedData.generation.erase.ambientGenerated.ambient.2.below).substDF
    henv pending.substitutions.wf formed pending.substitutions
  rw [pending.left_eq, pending.right_eq] at rawPair
  have atDeclared := alignment.path.cast rawPair
  have substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons leftValue)
      ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    .cons chosen.answer.reply.realization.substitutions
      (domain.sound.defeq.mono chosenData.generation.erase.ambientGenerated.ambient.2.below) atDeclared
  obtain ⟨realized, actual, actualHereditary, actualWorlds, ⟨actualReady⟩, actualCompatible, actualEnvironment, actualReplayable⟩ :=
    realizeHistoryFrame frame generation generationReady compatible generationHereditary substitutions
  let demand : WorldVariableDemand env U registry target
      (chosen.answer.reply.available.push entries.needs) 0 requested := {
    rank := selected.answer.reply.query.rank
    bound := selected.answer.reply.query.bound
    raw := selected.answer.reply.query.raw
    adapter := selected.answer.reply.query.adapter
    member := List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
    live := value.related.live henv hscoped formed }
  have capacity (ordered : headerEnv.Ordered) :
      environmentCost (realized.frame.dependencyEnvironment ordered) ≤ environmentCost reserve.closures := by
    rw [actualEnvironment ordered]
    exact Nat.le_of_eq (chosen.answer.reply.realization.frame.historyGroup_environmentCost
      sourceControls.ordered ordered entries (prior.frame.dependencyEnvironment headerControls.ordered)
      history.route.reserve (chosen.bounded ordered))
  have worlds : actual.worlds = (reserve.append (WorldEnvironmentProvenance.group sourceControls headerControls
      initial chosenData.generation.environment entries)).worlds := by
    rw [actualWorlds]
    exact WorldGenerated.historyGroup_worlds chosenData.generation domain ownerGraph nominalGraph nominal nominalProvenance displayed
      sourceControls.ordered headerControls.ordered ownerInitial seed scope sourceControls seedWorld domainProvenance
      prior history priorWorld initial baselines routeData.inputs routeData.generated.wellFormed routeData.controls routeData.frames
      (chosen.bounded headerControls.ordered) entries scopes sourceControls owners ownerAmbient nominalAmbient
      priorWorld.erase.ambientGenerated.ambient.2 routeData.generated.ambient ownerSources nominalSources
      priorWorld.erase.sources.2 routeData.generated.sources
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds reserve.worlds := by
    rw [worlds, WorldEnvironmentProvenance.worlds_append]
    exact (Covered.refl _).merge (WorldEnvironmentProvenance.group_covered_history sourceControls headerControls
      initial chosenData.generation.environment baselines.2 entries (history.route.worldReserve routeData.inputs)
      (chosen.bounded headerControls.ordered) chosenData.covered)
  exact ⟨{
    locals := Locals.push chosen.answer.reply.locals
    available := chosen.answer.reply.available.push entries.needs
    realization := realized
    generation := actual
    replayable := actualReplayable.mpr replayable
    controlled := actualReady
    compatible := actualCompatible
    hereditary := actualHereditary
    capacity := capacity
    covered := covered
    demand := demand }⟩

theorem generatedWorldHistoryGroupActivation
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
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode)
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
    (selected : AmbientBoundedGeneratedQueryReply base scope.caps (seed.seedDisplay scope.graph)
      scope.left scope.right (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment sourceControls.ordered)))
    (selectedData : WorldGeneratedQueryReplyData (P := P) sourceControls baselines.1 frontier selected) :
    let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
      initial baselines.2 (history.route.worldReserve routeData.inputs)
    ∃ reply : AmbientBoundedGeneratedQueryReply base commonCaps
      (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance variableNode variableProvenance)
      commonLeft commonRight requested (environmentCost _),
      Nonempty (WorldGeneratedQueryReplyData (P := P) headerControls reserve frontier reply) ∧
      reply.answer.reply.query.footprint = [(0, Need.mk reply.answer.reply.query.rank reply.answer.reply.query.raw)] := by
  dsimp only
  obtain ⟨answer⟩ := generatedWorldHistoryGroupDemand ownerGraph nominalGraph nominal nominalProvenance displayed seed scope sourceControls headerControls frontier parent seedWorld seedReplayable seedArgument seedHereditary seedReady seedCompatible seedQueryReady domainProvenance prior priorWorld priorReplayable priorHereditary priorReady priorCompatible history initial baselines baselineCoverage seedCovered routeData boundary coherent ownerAmbient ownerSources nominalAmbient nominalSources henv hscoped formed bank unary ownerSponsored ownerSmaller routeSponsored routeSmaller selected selectedData
  let reply := answer.atNode variableNode variableProvenance
  let data := answer.atNode_data variableNode variableProvenance
  exact ⟨reply, ⟨data.toWorldGeneratedQueryReplyData⟩, data.footprint⟩


/-- Activate a history branch inside a selected or merged destination frame.
Only its proper seed, owner, and route calls are retargeted to the fixed outer
budget; the selected parent itself need not be strictly smaller. -/
theorem reindexWorldHistoryGroupDemandAt
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
    (variableNode : EndpointState headerEnv U callerSource callerExpression callerAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (currentTail : WorldEnvironmentProvenance strata U currentEnvironment)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (currentCapacity : environmentCost
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).closures ≤
      environmentCost destinationEnvironment)
    (currentCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).worlds
      destinationBaseline.worlds)
    {ρ : Lift} (insertion : Ctx.Lift' ρ scope.scope nextScope)
    (leftTail : Subst.lift_l ρ nextLeft = scope.left)
    (rightTail : Subst.lift_l ρ nextRight = scope.right)
    (capsTail : (fun i => nextCaps (ρ.liftVar i)) = scope.caps)
    (left : OriginalNestedDisplay U nextScope ((seed.owner.expression.subst scope.raw).lift' ρ) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (sameCutoff : leftControls.cutoff = sourceControls.cutoff)
    (sameFuel : leftControls.fuel = sourceControls.fuel)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals nextLeft nextRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      leftControls leftBaseline frontier leftFrame)
    (parentEq : parent = frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (sponsored : Sponsored frontier [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp nextLeft)
      (requested : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query)) :
    Nonempty (WorldVariableDemandReply P base commonCaps
      (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight
      headerControls
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail)
      frontier 0 requested) := by
  let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
    initial baselines.2 (history.route.worldReserve routeData.inputs)
  let leftCall := originalCallWorld leftControls .expressionReindex left.node leftBaseline
  let selectedCurrent := originalCallWorld headerControls .expressionReindex variableNode (reserve.append currentTail)
  let current := originalCallWorld headerControls .expressionReindex variableNode destinationBaseline
  have currentBound : BoundedNode (@EquationControlMeasure.Less strata.rules.length) selectedCurrent current :=
    originalCallWorld_boundedNode headerControls .expressionReindex variableNode
      (reserve.append currentTail) destinationBaseline currentCapacity currentCovered
  have retainChild {child : World strata.rules.length}
      (lower : WorldBelow strata.rules.length child selectedCurrent) :
      WorldBelow strata.rules.length child current :=
    BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans currentBound lower
  have currentSponsored : Sponsored frontier [current] := by
    intro world member
    cases List.mem_singleton.mp member
    exact sponsored _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have lowerUse (uses : List (World strata.rules.length))
      (lower : ∀ child ∈ uses, WorldBelow strata.rules.length child current) :
      Sponsored frontier uses ∧ CallBelow strata.rules.length (frontier ++ uses) parent := by
    constructor
    · intro child member
      obtain ⟨sponsor, present, bound⟩ := currentSponsored current (List.mem_singleton_self _)
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans (lower child member) bound⟩
    · rw [parentEq]
      apply prefixCall
      exact callBelow_of_sublist (List.sublist_cons_self leftCall uses) ((split_call lower).cons leftCall)
  have seedLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1) current := by
    apply retainChild
    exact seedReindexBelowHistory (domain := domain) seedArgument sourceControls headerControls initial baselines.2
      baselines.1 (history.route.worldReserve routeData.inputs) currentTail variableNode .expressionReindex
      (seed.frame_environment_le sourceControls.ordered) seedCovered
  have ownerRLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .expressionReindex seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)) current := by
    apply retainChild
    exact seedReindexBelowHistory (domain := domain) seedArgument sourceControls headerControls initial baselines.2
      (seed.owner.worldEnvironment sourceControls initial) (history.route.worldReserve routeData.inputs)
      currentTail variableNode .expressionReindex (Nat.le_refl _) (Covered.refl _)
  have ownerFLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .fundamental seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)) current := by
    apply EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans _ ownerRLower
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  obtain ⟨ownerSponsored, ownerSmaller⟩ := lowerUse [_] (by
    intro child member; cases List.mem_singleton.mp member; exact ownerFLower)
  obtain ⟨routeSponsored, routeSmaller⟩ := lowerUse (history.route.worldReserve routeData.inputs).worlds (by
    intro child member
    apply retainChild
    apply Below.child
    change child ∈ (reserve.append currentTail).worlds
    dsimp only [reserve]
    rw [WorldEnvironmentProvenance.worlds_append, WorldEnvironmentProvenance.groupHistory,
      WorldEnvironmentProvenance.worlds_append]
    exact List.mem_append_left _ (List.mem_append_left _ member))
  have reindexSmaller : CallBelow strata.rules.length
      (frontier ++ [leftCall, originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1]) parent := by
    rw [parentEq]
    apply prefixCall
    exact (split_call (calls := [originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1])
      (by intro child member; cases List.mem_singleton.mp member; exact seedLower)).cons leftCall
  have reindexSponsored : Sponsored frontier
      [leftCall, originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1] := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact sponsored _ List.mem_cons_self
    · cases List.mem_singleton.mp member
      exact (lowerUse [_] (by intro child member; cases List.mem_singleton.mp member; exact seedLower)).1 _
        (List.mem_singleton_self _)
  let weakWorld := seedWorld.weaken insertion leftTail rightTail capsTail
  let weakReady : weakWorld.Controlled frontier := ⟨seedReady.annotation, seedReady.within, seedReady.sponsored⟩
  let weakHereditary : weakWorld.Hereditary frontier :=
    ⟨seedHereditary.tablesClosed, seedHereditary.bases, seedHereditary.ready⟩
  obtain ⟨seedFrame, actualSeed, actualH, actualWorlds, ⟨actualReady⟩, actualCompatible, actualEnvironment, actualReplayable⟩ :=
    realizeHistoryFrame seed.frame weakWorld weakReady seedCompatible weakHereditary seed.substitutions
  let seedData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := (seed.seedDisplay scope.graph).weaken insertion) sourceControls baselines.1 frontier seedFrame := {
    generation := actualSeed, replayable := actualReplayable.mpr seedReplayable,
    controlled := actualReady, compatible := actualCompatible, closed := seed.ownerClosed
    capacity := by
      simpa only [actualEnvironment sourceControls.ordered] using
        (Nat.le_refl (environmentCost (seed.frame.dependencyEnvironment sourceControls.ordered)))
    covered := by rw [actualWorlds]; exact baselineCoverage.1
    hereditary := actualH }
  obtain ⟨weakSelected, ⟨weakData⟩⟩ := bank.observation _ reindexSmaller base nextCaps left
    ((seed.seedDisplay scope.graph).weaken insertion) nextLeft nextRight leftControls sourceControls sameCutoff sameFuel
    leftBaseline baselines.1 frontier rfl reindexSponsored leftFrame leftData seedFrame seedData query resources queryReady
  obtain ⟨selected, selectedData, _sameQuery, _sameWorld, _sameRetained, _sameOwned, _sameBases, _sameTables⟩ :=
    WorldGeneratedQueryReplyData.unweaken insertion leftTail rightTail capsTail weakSelected weakData
  obtain ⟨answer⟩ := generatedWorldHistoryGroupDemand ownerGraph nominalGraph nominal
    nominalProvenance displayed seed scope sourceControls headerControls frontier parent seedWorld seedReplayable
    seedArgument seedHereditary seedReady seedCompatible seedQueryReady domainProvenance prior priorWorld priorReplayable
    priorHereditary priorReady priorCompatible history initial baselines baselineCoverage seedCovered routeData boundary coherent
    ownerAmbient ownerSources nominalAmbient nominalSources
    henv hscoped formed bank unary ownerSponsored ownerSmaller routeSponsored routeSmaller selected selectedData
  exact ⟨{ answer with
    capacity := fun ordered => Nat.le_trans (answer.capacity ordered) (by
      change environmentCost reserve.closures ≤ environmentCost (reserve.closures ++ currentEnvironment)
      rw [merge_environmentCost_append]
      exact Nat.le_max_left _ _)
    covered := Covered.trans EquationControlMeasure.less_trans answer.covered
      (fun world member => ⟨world, by rw [WorldEnvironmentProvenance.worlds_append]; exact List.mem_append_left _ member, .inl rfl⟩) }⟩

theorem reindexWorldHistoryGroupDemand
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
    (variableNode : EndpointState headerEnv U callerSource callerExpression callerAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (currentTail : WorldEnvironmentProvenance strata U currentEnvironment)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (currentCapacity : environmentCost
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).closures ≤
      environmentCost destinationEnvironment)
    (currentCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).worlds
      destinationBaseline.worlds)
    (left : OriginalNestedDisplay U scope.scope (seed.owner.expression.subst scope.raw) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (sameCutoff : leftControls.cutoff = sourceControls.cutoff)
    (sameFuel : leftControls.fuel = sourceControls.fuel)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals scope.left scope.right leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := scope.caps)
      leftControls leftBaseline frontier leftFrame)
    (parentEq : parent = frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (sponsored : Sponsored frontier [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp scope.left)
      (requested : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query)) :
    Nonempty (WorldVariableDemandReply P base commonCaps
      (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight
      headerControls
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail)
      frontier 0 requested) := by
  let reserve := WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
    initial baselines.2 (history.route.worldReserve routeData.inputs)
  let leftCall := originalCallWorld leftControls .expressionReindex left.node leftBaseline
  let selectedCurrent := originalCallWorld headerControls .expressionReindex variableNode (reserve.append currentTail)
  let current := originalCallWorld headerControls .expressionReindex variableNode destinationBaseline
  have currentBound : BoundedNode (@EquationControlMeasure.Less strata.rules.length) selectedCurrent current :=
    originalCallWorld_boundedNode headerControls .expressionReindex variableNode
      (reserve.append currentTail) destinationBaseline currentCapacity currentCovered
  have retainChild {child : World strata.rules.length}
      (lower : WorldBelow strata.rules.length child selectedCurrent) :
      WorldBelow strata.rules.length child current :=
    BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans currentBound lower
  have currentSponsored : Sponsored frontier [current] := by
    intro world member
    cases List.mem_singleton.mp member
    exact sponsored _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have lowerUse (uses : List (World strata.rules.length))
      (lower : ∀ child ∈ uses, WorldBelow strata.rules.length child current) :
      Sponsored frontier uses ∧ CallBelow strata.rules.length (frontier ++ uses) parent := by
    constructor
    · intro child member
      obtain ⟨sponsor, present, bound⟩ := currentSponsored current (List.mem_singleton_self _)
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans (lower child member) bound⟩
    · rw [parentEq]
      apply prefixCall
      exact callBelow_of_sublist (List.sublist_cons_self leftCall uses) ((split_call lower).cons leftCall)
  have seedLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1) current := by
    apply retainChild
    exact seedReindexBelowHistory (domain := domain) seedArgument sourceControls headerControls initial baselines.2
      baselines.1 (history.route.worldReserve routeData.inputs) currentTail variableNode .expressionReindex
      (seed.frame_environment_le sourceControls.ordered) seedCovered
  have ownerRLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .expressionReindex seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)) current := by
    apply retainChild
    exact seedReindexBelowHistory (domain := domain) seedArgument sourceControls headerControls initial baselines.2
      (seed.owner.worldEnvironment sourceControls initial) (history.route.worldReserve routeData.inputs)
      currentTail variableNode .expressionReindex (Nat.le_refl _) (Covered.refl _)
  have ownerFLower : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .fundamental seed.owner.node
        (seed.owner.worldEnvironment sourceControls initial)) current := by
    apply EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans _ ownerRLower
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  obtain ⟨ownerSponsored, ownerSmaller⟩ := lowerUse [_] (by
    intro child member; cases List.mem_singleton.mp member; exact ownerFLower)
  obtain ⟨routeSponsored, routeSmaller⟩ := lowerUse (history.route.worldReserve routeData.inputs).worlds (by
    intro child member
    apply retainChild
    apply Below.child
    change child ∈ (reserve.append currentTail).worlds
    dsimp only [reserve]
    rw [WorldEnvironmentProvenance.worlds_append, WorldEnvironmentProvenance.groupHistory,
      WorldEnvironmentProvenance.worlds_append]
    exact List.mem_append_left _ (List.mem_append_left _ member))
  have reindexSmaller : CallBelow strata.rules.length
      (frontier ++ [leftCall, originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1]) parent := by
    rw [parentEq]
    apply prefixCall
    exact (split_call (calls := [originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1])
      (by intro child member; cases List.mem_singleton.mp member; exact seedLower)).cons leftCall
  have reindexSponsored : Sponsored frontier
      [leftCall, originalCallWorld sourceControls .expressionReindex seed.owner.node baselines.1] := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact sponsored _ List.mem_cons_self
    · cases List.mem_singleton.mp member
      exact (lowerUse [_] (by intro child member; cases List.mem_singleton.mp member; exact seedLower)).1 _
        (List.mem_singleton_self _)
  obtain ⟨seedFrame, actualSeed, actualH, actualWorlds, ⟨actualReady⟩, actualCompatible, actualEnvironment, actualReplayable⟩ :=
    realizeHistoryFrame seed.frame seedWorld seedReady seedCompatible seedHereditary seed.substitutions
  let seedData : WorldCallFrameData (P := P) (base := base) (caps := scope.caps)
      (display := seed.seedDisplay scope.graph) sourceControls baselines.1 frontier seedFrame := {
    generation := actualSeed, replayable := actualReplayable.mpr seedReplayable,
    controlled := actualReady, compatible := actualCompatible, closed := seed.ownerClosed
    capacity := by
      simpa only [actualEnvironment sourceControls.ordered] using
        (Nat.le_refl (environmentCost (seed.frame.dependencyEnvironment sourceControls.ordered)))
    covered := by rw [actualWorlds]; exact baselineCoverage.1
    hereditary := actualH }
  obtain ⟨selected, ⟨selectedData⟩⟩ := bank.observation _ reindexSmaller base scope.caps left
    (seed.seedDisplay scope.graph) scope.left scope.right leftControls sourceControls sameCutoff sameFuel
    leftBaseline baselines.1 frontier rfl reindexSponsored leftFrame leftData seedFrame seedData query resources queryReady
  obtain ⟨answer⟩ := generatedWorldHistoryGroupDemand ownerGraph nominalGraph nominal
    nominalProvenance displayed seed scope sourceControls headerControls frontier parent seedWorld seedReplayable
    seedArgument seedHereditary seedReady seedCompatible seedQueryReady domainProvenance prior priorWorld priorReplayable
    priorHereditary priorReady priorCompatible history initial baselines baselineCoverage seedCovered routeData boundary coherent
    ownerAmbient ownerSources nominalAmbient nominalSources
    henv hscoped formed bank unary ownerSponsored ownerSmaller routeSponsored routeSmaller selected selectedData
  exact ⟨{ answer with
    capacity := fun ordered => Nat.le_trans (answer.capacity ordered) (by
      change environmentCost reserve.closures ≤ environmentCost (reserve.closures ++ currentEnvironment)
      rw [merge_environmentCost_append]
      exact Nat.le_max_left _ _)
    covered := Covered.trans EquationControlMeasure.less_trans answer.covered
      (fun world member => ⟨world, by rw [WorldEnvironmentProvenance.worlds_append]; exact List.mem_append_left _ member, .inl rfl⟩) }⟩

theorem reindexWorldHistoryGroupHead
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
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (currentTail : WorldEnvironmentProvenance strata U currentEnvironment)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (currentCapacity : environmentCost
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).closures ≤
      environmentCost destinationEnvironment)
    (currentCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
        baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail).worlds
      destinationBaseline.worlds)
    (left : OriginalNestedDisplay U scope.scope (seed.owner.expression.subst scope.raw) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (sameCutoff : leftControls.cutoff = sourceControls.cutoff)
    (sameFuel : leftControls.fuel = sourceControls.fuel)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals scope.left scope.right leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := scope.caps)
      leftControls leftBaseline frontier leftFrame)
    (parentEq : parent = frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (sponsored : Sponsored frontier [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld headerControls .expressionReindex variableNode destinationBaseline])
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp scope.left)
      (requested : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query)) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base commonCaps
      (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance variableNode variableProvenance)
      commonLeft commonRight requested (environmentCost destinationEnvironment),
      Nonempty (WorldCaptureHeadReplyData (P := P) headerControls
        ((WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls initial
          baselines.2 (history.route.worldReserve routeData.inputs)).append currentTail)
        destinationBaseline frontier reply) := by
  obtain ⟨answer⟩ := reindexWorldHistoryGroupDemand ownerGraph nominalGraph nominal nominalProvenance displayed seed scope sourceControls headerControls frontier parent seedWorld seedReplayable seedArgument seedHereditary seedReady seedCompatible seedQueryReady domainProvenance prior priorWorld priorReplayable priorHereditary priorReady priorCompatible history initial baselines baselineCoverage seedCovered routeData boundary coherent ownerAmbient ownerSources nominalAmbient nominalSources variableNode henv hscoped formed bank unary currentTail destinationBaseline currentCapacity currentCovered left leftControls leftBaseline sameCutoff sameFuel leftFrame leftData parentEq sponsored query resources queryReady
  let localReply := answer.atNode variableNode variableProvenance
  let localData := answer.atNode_data variableNode variableProvenance
  let reply := { localReply with
    bounded := fun ordered => Nat.le_trans (answer.capacity ordered) currentCapacity }
  exact ⟨reply, ⟨{ localData with
    covered := Covered.trans EquationControlMeasure.less_trans answer.covered currentCovered }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
