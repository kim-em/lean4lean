import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerReplayFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection

/-! Selection of actual capture owners retains their queries and sponsors.
The family replay path shares a cutoff and fuel table across its caller and
earlier headers. This file uses that equality explicitly; it does not infer
bounds at independently chosen owner controls from an ancestor's bound. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private needAdapter from Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
open private rawOwners from Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem headEnvironment_worlds_mpr
    {strata : EquationStratification env} {first second : List Closure}
    (same : first = second) (world : WorldEnvironmentProvenance strata U second) :
    ((congrArg (WorldEnvironmentProvenance strata U) same).mpr world).worlds = world.worlds := by
  cases same
  rfl

theorem RichGroupedCaptureEntry.query_mem_storedQueries
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals declaredLeft available initial rawCapture leftValue rightValue) :
    .observation entry.query ∈ entry.toRaw.storedQueries := by
  simp only [RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.storedQueries]
  exact List.mem_append_right _ (List.mem_cons_self ..)

theorem RichGroupedCapture.query_mem_storedQueries
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals declaredLeft available initial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals declaredLeft available initial rawCapture leftValue rightValue}
    (present : entry ∈ entries) :
    .observation entry.query ∈ (richGroupedEntriesRaw entries).storedQueries := by
  induction entries with
  | nil => cases present
  | cons head entries ih =>
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.storedQueries]
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_append_left _ (RichGroupedCaptureEntry.query_mem_storedQueries entry)
    · exact List.mem_append_right _ (ih present)


/-- A requested head need selects the exact original owner query and its
hereditary generation. The newly requested input may be richer than a
previous cursor input; selection uses the actual completed group entries. -/
theorem WorldGenerated.historyGroup_selectedOwner
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals
        (raw.comp commonLeft) (raw.comp commonRight) available}
      {controls : OriginalWorldControls strata headerEnv}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (headerOrdered : headerEnv.Ordered)
      (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture leftValue rightValue)
      (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
        (seed.owner.context seed.initialContext))
      (seedControls : OriginalWorldControls strata ownerEnv)
      (seedGenerated : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw seedControls)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (priorGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight graph prior.frame.raw controls)
      (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
      (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ownerOrdered) ×
        WorldEnvironmentProvenance strata U (prior.frame.dependencyEnvironment headerOrdered))
      (routeInputs : history.route.WorldInputs strata)
      (historyWellFormed : history.route.WellFormed)
      (historyControls : ∀ index : Fin history.route.frames.length,
      OriginalWorldControls strata (history.route.frames[index]).sourceEnv)
      (historyGenerated : ∀ index : Fin history.route.frames.length,
        WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
          (history.route.frames[index]).graph (history.route.frames[index]).frame.realization.frame.raw (historyControls index))
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (ownerControls : OriginalWorldControls strata ownerEnv)
      (owners : ∀ entry member, WorldGenerated strata P base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw ownerControls)
      (ownerAmbient : ownerGraph.Ambient env)
      (nominalAmbient : nominalGraph.Ambient env)
      (priorAmbient : prior.frame.Ambient)
      (routeAmbient : history.route.Ambient)
      (ownerSources : ownerGraph.AllSources P)
      (nominalSources : nominalGraph.AllSources P)
      (priorSources : prior.frame.raw.AllSources P)
      (routeSources : history.route.AllSources P)
      (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
      (ready : (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Controlled frontier)
      (sameCutoff : ownerControls.cutoff = controls.cutoff)
      (sameFuel : ownerControls.fuel = controls.fuel)
      (need : Need) (member : need ∈ entries.needs) :
      ∃ entry, ∃ present : entry ∈ entries,
        need ∈ captureNeeds entry.input ∧
        Nonempty (ControlledStoredQuery ownerControls frontier (.observation entry.query)) ∧
        Nonempty ((owners entry present).Controlled frontier) ∧
        ∃ bound : need.rank ≤ entry.queryRank,
          Nonempty (GeneralNormalProfileAdapter env U registry target entry.queryInput
            (raiseProfile entry.queryRank bound need.profile)) := by
  let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  have queryMember : .observation entry.query ∈ group.retainedQueries := by
    change _ ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact RichGroupedCapture.query_mem_storedQueries entries present
  have ownerIncluded : (owners entry present).retainedQueries ⊆ group.retainedQueries := by
    intro query queryMember
    change _ ∈ _ ++ entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries)
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨⟨entry, present⟩, List.mem_attach _ _, queryMember⟩
  obtain ⟨queryReady⟩ := ready.selectStored queryMember
  let queryReady := queryReady.recontrol ownerControls sameCutoff.symm sameFuel.symm
  have ownerReady := ready.selectGeneration (owners entry present) ownerIncluded sameCutoff sameFuel
  have needBound := (captureNeeds_covered entry.input need requested).1
  have needCovered := (captureNeeds_covered entry.input need requested).2
  exact ⟨entry, present, requested, ⟨queryReady⟩, ownerReady,
    Nat.le_trans needBound entry.queryBound,
    ⟨needAdapter entry.queryBound entry.queryAdapter needBound needCovered⟩⟩


/-- A source head packet keeps both its actual scoped frame and the exact
stored observer, with the control prefix inherited from this family replay. -/
structure WorldCapturedHeadQuery
    (strata : EquationStratification env) (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (common : List VExpr) (commonLeft commonRight : Subst) (expression : VExpr)
    (need : Need) (capacity cutoff : Nat) (fuel : Nat → Nat)
    (frontier envelope : List (EquationWorldClosureOrder.World strata.rules.length))
    extends CapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity where
  controls : OriginalWorldControls strata display.sourceEnv
  generated : WorldGenerated strata P base caps left right display.graph realization.frame.raw controls
  compatible : generated.UsesControlPrefix cutoff fuel
  ready : generated.Controlled frontier
  queryReady : ControlledStoredQuery controls frontier (.observation query)
  replayable : generated.Replayable
  baselineEnvironment : List Closure
  baseline : WorldEnvironmentProvenance strata U baselineEnvironment
  frameCapacity : environmentCost (realization.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment
  frameCovered : EquationWorldClosureOrder.Covered (@EquationControlMeasure.Less strata.rules.length)
    generated.worlds baseline.worlds
  baselineMember : originalCallWorld controls .expressionReindex display.node baseline ∈ envelope
  hereditary : generated.Hereditary frontier

private theorem realizeHeadQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (replayable : generated.Replayable)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (compatible : generated.UsesControlPrefix cutoff fuel)
    (ready : generated.Controlled frontier)
    {node : EndpointState sourceEnv U source expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (queryReady : ControlledStoredQuery controls frontier (.observation query)) :
    ∃ realization : OriginalCaptureRealization graph env registry target locals left right available,
    ∃ next : WorldGenerated strata P base caps left right graph realization.frame.raw controls,
    ∃ actual : RichObs sourceEnv env U registry target node locals (raw.comp left) profile footprint,
      next.Replayable ∧ next.worlds = generated.worlds ∧
      next.UsesControlPrefix cutoff fuel ∧ Nonempty (next.Controlled frontier) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation actual)) ∧
      HEq actual query ∧
      (∀ ordered, realization.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered) ∧
      Nonempty (next.Hereditary frontier) := by
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, query, replayable, rfl, compatible, ⟨ready⟩, ⟨queryReady⟩,
    HEq.rfl, (fun _ => rfl), ⟨hereditary⟩⟩

theorem WorldGenerated.historyGroup_headQuery
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
      {context : ContextDerivation headerEnv U headerSource}
      {graph : OriginalCaptureMap (common := common) context raw}
      {tail : RawOriginalRichFrame headerEnv env U registry target context locals
        (raw.comp commonLeft) (raw.comp commonRight) available}
      {controls : OriginalWorldControls strata headerEnv}
      (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
      {nominalContext : ContextDerivation nominalEnv U nominalSource}
      (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
      (nominal : EndpointState nominalEnv U nominalSource argument assigned)
      (provenance : EndpointProvenance nominalContext nominal)
      (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
      {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
      {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
      (ownerOrdered : ownerEnv.Ordered) (headerOrdered : headerEnv.Ordered)
      (ownerInitial : List Closure)
      (seed : PendingRichCapture (field := field) (major := major) domain env registry target
        seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture leftValue rightValue)
      (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
        (seed.owner.context seed.initialContext))
      (seedControls : OriginalWorldControls strata ownerEnv)
      (seedGenerated : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw seedControls)
      (domainProvenance : EndpointProvenance context (.ref domain))
      (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
      (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance prior
        ownerOrdered headerOrdered)
      (priorGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight graph prior.frame.raw controls)
      (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
      (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ownerOrdered) ×
        WorldEnvironmentProvenance strata U (prior.frame.dependencyEnvironment headerOrdered))
      (routeInputs : history.route.WorldInputs strata)
      (historyWellFormed : history.route.WellFormed)
      (historyControls : ∀ index : Fin history.route.frames.length,
      OriginalWorldControls strata (history.route.frames[index]).sourceEnv)
      (historyGenerated : ∀ index : Fin history.route.frames.length,
        WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
          (history.route.frames[index]).graph (history.route.frames[index]).frame.realization.frame.raw (historyControls index))
      (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered))
      (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext))
      (ownerControls : OriginalWorldControls strata ownerEnv)
      (owners : ∀ entry member, WorldGenerated strata P base (scopes entry member).caps (scopes entry member).left
        (scopes entry member).right (scopes entry member).graph entry.frame.raw ownerControls)
      (ownerAmbient : ownerGraph.Ambient env)
      (nominalAmbient : nominalGraph.Ambient env)
      (priorAmbient : prior.frame.Ambient)
      (routeAmbient : history.route.Ambient)
      (ownerSources : ownerGraph.AllSources P)
      (nominalSources : nominalGraph.AllSources P)
      (priorSources : prior.frame.raw.AllSources P)
      (routeSources : history.route.AllSources P)
      (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
      (replayable : (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Replayable)
      (ready : (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Controlled frontier)
      (compatible : (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).UsesControlPrefix cutoff fuel)
      (hereditary : (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Hereditary frontier)
      (valid : tail.Valid)
      (need : Need) (member : need ∈ entries.needs) :
      Nonempty (WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight
        (rawCapture.subst ownerRaw) need
        (environmentCost ((OriginalRichFrame.group ⟨tail, valid⟩ domain ownerOrdered ownerInitial entries).dependencyEnvironment headerOrdered))
        cutoff fuel frontier
        (WorldEnvironmentProvenance.group ownerControls controls initialProvenance generated.environment entries).worlds) := by
  let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  have ownerCompatible : ∀ entry member, (owners entry member).UsesControlPrefix cutoff fuel := compatible.2.2.2.2.1
  have parentPrefix := compatible.controls_match
  obtain ⟨witness, witnessPresent, _⟩ := List.mem_flatMap.mp member
  have ownerPrefix := (ownerCompatible witness witnessPresent).controls_match
  have controlEq := ownerPrefix.same parentPrefix
  obtain ⟨entry, present, requested, ⟨queryReady⟩, ⟨ownerReady⟩, bound, ⟨adapter⟩⟩ :=
    WorldGenerated.historyGroup_selectedOwner generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources frontier ready
      controlEq.1 controlEq.2 need member
  let scope := scopes entry present
  have ownerBases : (owners entry present).baseUses.Sublist group.baseUses := by
    change (owners entry present).baseUses.Sublist (_ ++ entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
    exact (sublist_flatMap_member (fun entry : { x // x ∈ entries } =>
      (owners entry.val entry.property).baseUses) (List.mem_attach entries ⟨entry, present⟩)).trans
      (List.sublist_append_right _ _)
  obtain ⟨ownerHereditary⟩ := hereditary.selectGeneration (owners entry present)
    (hereditary.tablesClosed.2.2.2.2 entry present) ownerBases controlEq.1 controlEq.2
  obtain ⟨realized, ownerGenerated, actualQuery, ownerReplayable, actualWorlds, ownerCompatible, ⟨ownerReady⟩, ⟨queryReady⟩,
      sameQuery, sameEnvironment, ⟨ownerHereditary⟩⟩ := realizeHeadQuery entry.frame (owners entry present)
      (replayable.2.2.2.2.1 entry present) ownerHereditary entry.substitutions (ownerCompatible entry present) ownerReady entry.query queryReady
  refine ⟨{
    depth := entry.depth, scope := scope.scope, insertion := scope.insertion
    left := scope.left, right := scope.right, leftTail := scope.leftTail, rightTail := scope.rightTail
    caps := scope.caps, capsTail := scope.capsTail
    assigned := entry.owner.assigned.subst scope.raw, display := entry.scopeDisplay scope
    ordered := ownerControls.ordered, locals := entry.ownerLocals, available := entry.ownerAvailable
    realization := realized, capped := ownerGenerated.erase.capped
    rank := entry.queryRank, bound := bound, profile := entry.queryInput, footprint := entry.footprint
    query := actualQuery, resources := entry.queryAvailable, adapter := adapter,
    cost := ?_, controls := ownerControls, generated := ownerGenerated,
    compatible := ownerCompatible, ready := ownerReady, queryReady := queryReady,
    replayable := ownerReplayable, baselineEnvironment := entry.owner.dependencyEnvironment ownerControls.ordered ownerInitial,
    baseline := entry.owner.worldEnvironment ownerControls initialProvenance,
    frameCapacity := by rw [sameEnvironment]; exact entry.frame_environment_le ownerControls.ordered,
    frameCovered := by rw [actualWorlds]; exact replayable.2.2.2.2.2.1 entry present,
    baselineMember := WorldEnvironmentProvenance.group_owner_reindex_mem ownerControls controls initialProvenance generated.environment entries present
    hereditary := ownerHereditary }⟩
  rw [sameEnvironment]
  exact entries.ownerQuery_cost_le_environment ownerControls.ordered headerOrdered ⟨tail, valid⟩ present


def WorldCapturedHeadQuery.relabel
    (head : WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight expression need capacity cutoff fuel frontier envelope)
    (same : expression = nextExpression) :
    WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight nextExpression need capacity cutoff fuel frontier envelope := by
  cases same
  exact head

def WorldCapturedHeadQuery.enlarge
    (head : WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight expression need capacity cutoff fuel frontier envelope)
    (bound : capacity ≤ nextCapacity) (included : envelope ⊆ nextEnvelope) :
    WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight expression need nextCapacity cutoff fuel frontier nextEnvelope :=
  { head with toCapturedHeadQuery := head.toCapturedHeadQuery.enlarge bound, baselineMember := included head.baselineMember }

private theorem ownHeadQueryWorld
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (ordered : sourceEnv.Ordered)
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (controls : OriginalWorldControls strata sourceEnv)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail.raw controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix cutoff fuel)
    (ready : generated.Controlled frontier)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (queryAvailable : argumentFootprint.Available available)
    (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (need : Need) (member : need ∈ needs) :
    Nonempty (WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight (a.subst raw) need
      (environmentCost (((tail.capture domain initial argument location lineage query queryAvailable certificate resources
        typed arguments needs bounded covered).reserve
          [Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
            (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)]).dependencyEnvironment ordered))
        cutoff fuel frontier (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).worlds) := by
  obtain ⟨realized, ownerGenerated, actualQuery, ownerReplayable, actualWorlds, ownerCompatible, ⟨ownerReady⟩, ⟨queryReady⟩,
      sameQuery, environment, ⟨ownerHereditary⟩⟩ := realizeHeadQuery tail generated replayable hereditary substitutions compatible ready query queryReady
  let display : OriginalNestedDisplay U common ((a.subst raw).lift' (.skipN .refl 0)) (A.subst raw) := {
    sourceEnv := sourceEnv, source := source, sourceExpression := a, sourceType := A
    context := context, node := argument, provenance := ⟨_, _, _, root, initial, location, lineage.symm⟩
    raw := raw, graph := graph, expression_eq := by simp only [Lift.skipN, lift'_refl]
    type_eq := rfl }
  refine ⟨{
    depth := 0, scope := common, insertion := .refl
    left := commonLeft, right := commonRight, leftTail := rfl, rightTail := rfl
    caps := commonCaps, capsTail := rfl, assigned := A.subst raw, display := display, ordered := ordered
    locals := locals, available := available, realization := realized, capped := ownerGenerated.erase.capped
    rank := k, bound := Nat.le_trans (bounded need member) queryBound
    profile := rawInput, footprint := argumentFootprint, query := actualQuery, resources := queryAvailable
    adapter := needAdapter queryBound queryAdapter (bounded need member) (covered need member)
    cost := ?_, controls := controls, generated := ownerGenerated,
    compatible := ownerCompatible, ready := ownerReady, queryReady := queryReady,
    replayable := ownerReplayable, baselineEnvironment := tail.dependencyEnvironment controls.ordered,
    baseline := generated.environment,
    frameCapacity := by rw [environment]; exact Nat.le_refl _,
    frameCovered := by rw [actualWorlds]; exact EquationWorldClosureOrder.Covered.refl _,
    baselineMember := by exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
    hereditary := ownerHereditary }⟩
  rw [environment]
  exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

private def capturedWorldInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame controls)
    (cutoff : Nat) (fuel : Nat → Nat)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length)) : Prop :=
  match graph with
  | .capture .. => generated.Replayable → generated.UsesControlPrefix cutoff fuel → generated.Controlled frontier → Nonempty (generated.Hereditary frontier) →
      frame.Valid → Ctx.SubstEq env U target σ τ source →
      ∀ ordered : sourceEnv.Ordered, ∀ need ∈ available 0,
      Nonempty (WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight (raw 0) need
        (environmentCost (frame.dependencyEnvironment ordered)) cutoff fuel frontier generated.worlds)
  | _ => True

private theorem capturedWorldInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    {first : WorldGenerated strata P base commonCaps commonLeft commonRight graph left controls}
    {second : WorldGenerated strata P base commonCaps commonLeft commonRight graph right controls}
    (firstIH : capturedWorldInvariant first cutoff fuel frontier)
    (secondIH : capturedWorldInvariant second cutoff fuel frontier) :
    capturedWorldInvariant (.merge first second) cutoff fuel frontier := by
  cases graph <;> try trivial
  intro replayable compatible ready ⟨hereditary⟩ valid substitutions ordered need member
  simp only [RawOriginalRichFrame.Valid] at valid
  rcases List.mem_append.mp member with member | member
  · obtain ⟨firstReady⟩ := ready.selectGeneration first
      (fun _ present => List.mem_append_left _ present) rfl rfl
    obtain ⟨answer⟩ := firstIH replayable.1 compatible.1 firstReady (hereditary.selectGeneration first hereditary.tablesClosed.1 (List.sublist_append_left _ _) rfl rfl) valid.1 substitutions ordered need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
      rw [merge_environmentCost_append]
      exact Nat.le_max_left _ _) (fun _ member => by
        simp only [WorldGenerated.worlds, WorldGenerated.environment, WorldEnvironmentProvenance.worlds_append]
        exact List.mem_append_left _ member)⟩
  · obtain ⟨secondReady⟩ := ready.selectGeneration second
      (fun _ present => List.mem_append_right _ present) rfl rfl
    obtain ⟨answer⟩ := secondIH replayable.2 compatible.2 secondReady (hereditary.selectGeneration second hereditary.tablesClosed.2 (List.sublist_append_right _ _) rfl rfl) valid.2 substitutions ordered need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _) (fun _ member => by
        simp only [WorldGenerated.worlds, WorldGenerated.environment, WorldEnvironmentProvenance.worlds_append]
        exact List.mem_append_right _ member)⟩

private theorem WorldGenerated.headQueryInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame controls) :
    capturedWorldInvariant generated cutoff fuel frontier := by
  induction generated with
  | merge _ _ first second => exact capturedWorldInvariant_merge first second
  | identity | empty | bind | weaken => trivial
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered _ =>
    intro replayable compatible ready ⟨hereditary⟩ valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    have tailSubstitutions := by cases substitutions with | cons tail _ _ => exact tail
    obtain ⟨queryReady⟩ := ready.selectStored (query := .observation query) (List.mem_cons_self ..)
    obtain ⟨tailReady⟩ := ready.selectGeneration generated
      (fun _ present => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)) rfl rfl
    exact ownHeadQueryWorld ordered ⟨_, valid⟩ _ generated baseline replayable.1 compatible tailReady
      ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩ tailSubstitutions
      domain initial argument location lineage query queryReady queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered need member
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      _ _ _ _ _ =>
    intro replayable compatible ready ⟨hereditary⟩ valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    change Nonempty (WorldCapturedHeadQuery _ _ _ _ _ _ _ (VExpr.subst _ _) _ _ _ _ _ _)
    obtain ⟨answer⟩ := WorldGenerated.historyGroup_headQuery generated domain ownerGraph nominalGraph nominal provenance
      displayed ownerOrdered headerOrdered ownerInitial seed seedScope seedControls seedGenerated domainProvenance prior
      history priorGenerated initialProvenance baselines routeInputs historyWellFormed historyControls historyGenerated tailBound
      entries scopes ownerControls owners ownerAmbient nominalAmbient priorAmbient routeAmbient
      ownerSources nominalSources priorSources routeSources frontier replayable ready compatible hereditary valid.1 need member
    exact ⟨(answer.enlarge (by
      change _ ≤ environmentCost (_ ++ _)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _) (fun _ member => by
      simp only [WorldGenerated.worlds, WorldGenerated.environment, WorldGenerated.callControls,
        WorldEnvironmentProvenance.worlds_append]
      apply List.mem_append_right
      rw [headEnvironment_worlds_mpr]
      · exact member
      · simp only [RawOriginalRichFrame.dependencyEnvironment, rawOwners, RichGroupedCapture.environment])).relabel displayed⟩

/-- Every demanded head of this compatible-control family capture has an
actual scoped owner observer. Branch selection is structural, including
merges, and does not make a recursive semantic call at the unchanged node. -/
theorem WorldGenerated.headQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    {nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw}
    {nominal : EndpointState nominalEnv U nominalSource argument assigned}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {provenance : EndpointProvenance nominalContext nominal}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance) frame controls)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix cutoff fuel)
    (ready : generated.Controlled frontier)
    (hereditary : generated.Hereditary frontier)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: source))
    (ordered : sourceEnv.Ordered) (need : Need) (member : need ∈ available 0) :
    Nonempty (WorldCapturedHeadQuery strata P base commonCaps common commonLeft commonRight
      (argument.subst nominalRaw) need (environmentCost (frame.dependencyEnvironment ordered)) cutoff fuel frontier generated.worlds) :=
  generated.headQueryInvariant replayable compatible ready ⟨hereditary⟩ valid substitutions ordered need member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
