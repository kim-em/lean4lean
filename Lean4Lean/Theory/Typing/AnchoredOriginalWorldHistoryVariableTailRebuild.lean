import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryHereditary
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryWorlds
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGroupCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection

/-! An upper history slot retains its complete original branch while a second
empty active slot carries the recursively selected lower demand. Both branches
reuse the exact dormant seed, prior, and positional route annotations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

private theorem sublist_middle (left middle right : List α) : middle.Sublist (left ++ middle ++ right) :=
  (List.sublist_append_right left middle).trans (List.sublist_append_left _ right)

theorem rebuildWorldHistoryGroupVariableDemand
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
 :
    let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
    ∀ (frontier : List (World strata.rules.length)),
    group.Replayable → group.Controlled frontier →
    group.UsesControlPrefix controls.cutoff controls.fuel → group.Hereditary frontier →
    tail.Valid →
    Ctx.SubstEq env U target ((raw.comp commonLeft).cons leftValue)
      ((raw.comp commonRight).cons rightValue) (A :: headerSource) →
    ∀ (selected : WorldVariableDemandReply P base commonCaps graph commonLeft commonRight
      controls generated.environment frontier index requested),
    Nonempty (WorldVariableDemandReply P base commonCaps
      (.capture graph domain nominalGraph nominal provenance) commonLeft commonRight
      controls group.environment frontier (index + 1) requested) := by
  dsimp only
  let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  intro frontier replayable ready compatible hereditary valid substitutions selected
  have sameLocals : selected.locals = locals :=
    selected.generation.erase.capped.generated.locals_eq.trans generated.erase.capped.generated.locals_eq.symm
  rcases selected with ⟨selectedLocals, selectedAvailable, selected, selectedWorld, selectedReplayable,
    selectedReady, selectedCompatible, selectedH, selectedCapacity, selectedCovered, demand⟩
  dsimp only at sameLocals
  cases sameLocals
  have seedPrefix := WorldGenerated.UsesControlPrefix.controls_match (generated := seedGenerated) compatible.2.1
  have ownerPrefix : ownerControls.HasPrefix controls.cutoff controls.fuel := compatible.2.2.2.2.2
  rcases replayable with ⟨tailReplayable, seedReplayable, priorReplayable, routeReplayable,
    ownersReplayable, ownersCovered, seedCovered, seedBaselineCovered, priorBaselineCovered,
    boundaryData, tailCovered⟩
  have seedQueries : seedGenerated.retainedQueries ⊆ group.retainedQueries := by
    intro query member
    change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    simp only [List.mem_append, List.mem_cons]
    exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr member))))
  have priorQueries : priorGenerated.retainedQueries ⊆ group.retainedQueries := by
    intro query member
    change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  have routeQueries (index : Fin history.route.frames.length) :
      (historyGenerated index).retainedQueries ⊆ group.retainedQueries := by
    intro query member
    change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨index, List.mem_finRange index, member⟩))
  obtain ⟨seedReady⟩ := ready.selectGeneration seedGenerated seedQueries seedPrefix.1 seedPrefix.2
  obtain ⟨priorReady⟩ := ready.selectGeneration priorGenerated priorQueries rfl rfl
  have seedMember : StoredOriginalQuery.observation seed.query ∈ group.retainedQueries := by
    change _ ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    simp only [List.mem_append, List.mem_cons]
    exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl trivial))))
  obtain ⟨seedQuery⟩ := ready.selectStored seedMember
  have seedBases : seedGenerated.baseUses.Sublist group.baseUses := by
    change seedGenerated.baseUses.Sublist (generated.baseUses ++ seedGenerated.baseUses ++ priorGenerated.baseUses ++
      (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
      entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
    simpa only [List.append_assoc] using sublist_middle generated.baseUses seedGenerated.baseUses
      (priorGenerated.baseUses ++ (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
        entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
  have priorBases : priorGenerated.baseUses.Sublist group.baseUses := by
    change priorGenerated.baseUses.Sublist (generated.baseUses ++ seedGenerated.baseUses ++ priorGenerated.baseUses ++
      (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
      entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
    simpa only [List.append_assoc] using sublist_middle (generated.baseUses ++ seedGenerated.baseUses) priorGenerated.baseUses
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
        entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
  have routeBases (index : Fin history.route.frames.length) : (historyGenerated index).baseUses.Sublist group.baseUses := by
    apply (sublist_flatMap_member (fun index => (historyGenerated index).baseUses) (List.mem_finRange index)).trans
    change (_ : List _).Sublist (generated.baseUses ++ seedGenerated.baseUses ++ priorGenerated.baseUses ++
      (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
      entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
    exact sublist_middle _ _ _
  obtain ⟨seedHereditary⟩ := hereditary.selectGeneration seedGenerated hereditary.tablesClosed.2.1 seedBases seedPrefix.1 seedPrefix.2
  obtain ⟨priorHereditary⟩ := hereditary.selectGeneration priorGenerated hereditary.tablesClosed.2.2.1 priorBases rfl rfl
  have frameData (index : Fin history.route.frames.length) :
      Nonempty ((historyGenerated index).Controlled frontier × (historyGenerated index).Hereditary frontier) := by
    have same := WorldGenerated.UsesControlPrefix.controls_match (generated := historyGenerated index) (compatible.2.2.2.1 index)
    obtain ⟨frameReady⟩ := ready.selectGeneration (historyGenerated index) (routeQueries index) same.1 same.2
    obtain ⟨frameHereditary⟩ := hereditary.selectGeneration (historyGenerated index)
      (hereditary.tablesClosed.2.2.2.1 index) (routeBases index) same.1 same.2
    exact ⟨⟨frameReady, frameHereditary⟩⟩
  classical
  let emptyEntries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals (raw.comp commonLeft) selectedAvailable ownerInitial rawCapture leftValue rightValue := []
  let emptyScopes : ∀ entry ∈ emptyEntries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext) := fun entry member => False.elim (List.not_mem_nil member)
  let emptyOwners : ∀ entry member, WorldGenerated strata P base (emptyScopes entry member).caps
      (emptyScopes entry member).left (emptyScopes entry member).right (emptyScopes entry member).graph
      entry.frame.raw ownerControls := fun entry member => False.elim (List.not_mem_nil member)
  have selectedBound : environmentCost (selected.frame.dependencyEnvironment headerOrdered) ≤
      environmentCost (prior.frame.dependencyEnvironment headerOrdered) :=
    Nat.le_trans (selectedCapacity headerOrdered) tailBound
  have selectedPriorCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selectedWorld.worlds baselines.2.worlds :=
    Covered.trans EquationControlMeasure.less_trans selectedCovered tailCovered
  let emptyWorld := WorldGenerated.historyGroup selectedWorld domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated selectedBound emptyEntries emptyScopes ownerControls emptyOwners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  have emptyReplayable : emptyWorld.Replayable :=
    ⟨selectedReplayable, seedReplayable, priorReplayable, routeReplayable,
      (fun entry member => False.elim (List.not_mem_nil member)),
      (fun entry member => False.elim (List.not_mem_nil member)), seedCovered,
      seedBaselineCovered, priorBaselineCovered, boundaryData, selectedPriorCovered⟩
  have emptyCompatible : emptyWorld.UsesControlPrefix controls.cutoff controls.fuel :=
    ⟨selectedCompatible, compatible.2.1, compatible.2.2.1, compatible.2.2.2.1,
      (fun entry member => False.elim (List.not_mem_nil member)), ownerPrefix⟩
  obtain ⟨emptyReady⟩ := WorldGenerated.Controlled.historyGroup selectedWorld domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated selectedBound emptyEntries emptyScopes ownerControls emptyOwners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      selectedReady (by intro query member; simp only [emptyEntries, richGroupedEntriesRaw, RawRichGroupEntries.storedQueries, List.not_mem_nil] at member) seedQuery seedReady seedPrefix priorReady
      (fun index => (Classical.choice (frameData index)).1)
      (fun index => WorldGenerated.UsesControlPrefix.controls_match (compatible.2.2.2.1 index))
      (fun entry member => False.elim (List.not_mem_nil member)) ownerPrefix
  let emptyH := WorldGenerated.Hereditary.historyGroup selectedWorld domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated selectedBound emptyEntries emptyScopes ownerControls emptyOwners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      selectedH seedHereditary seedPrefix priorHereditary
      (fun index => (Classical.choice (frameData index)).2)
      (fun index => WorldGenerated.UsesControlPrefix.controls_match (compatible.2.2.2.1 index))
      (fun entry member => False.elim (List.not_mem_nil member)) ownerPrefix
  let reserve := groupCaptureHistoryReserve field major domain ownerOrdered headerOrdered ownerInitial
    (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
  let originalTail : OriginalRichFrame headerEnv env U registry target context locals
      (raw.comp commonLeft) (raw.comp commonRight) available := ⟨tail, valid⟩
  let originalFrame := (originalTail.group domain ownerOrdered ownerInitial entries).reserve reserve
  let emptyFrame := (selected.frame.group domain ownerOrdered ownerInitial emptyEntries).reserve reserve
  let merged := emptyFrame.merge originalFrame
  let mergedWorld := emptyWorld.merge group
  have groupReplayable : group.Replayable :=
    ⟨tailReplayable, seedReplayable, priorReplayable, routeReplayable, ownersReplayable,
      ownersCovered, seedCovered, seedBaselineCovered, priorBaselineCovered, boundaryData, tailCovered⟩
  have mergedReplayable : mergedWorld.Replayable := ⟨emptyReplayable, groupReplayable⟩
  let mergedReady := emptyReady.merge ready
  have mergedCompatible : mergedWorld.UsesControlPrefix controls.cutoff controls.fuel :=
    ⟨emptyCompatible, compatible⟩
  let mergedH := emptyH.merge hereditary
  obtain ⟨realized, actual, actualReplayable, ⟨actualReady⟩, actualCompatible, ⟨actualH⟩, actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail merged mergedWorld substitutions mergedReplayable mergedReady mergedCompatible mergedH
  have localCapacity (ordered : headerEnv.Ordered) :
      environmentCost (realized.frame.dependencyEnvironment ordered) ≤
      environmentCost group.environment.closures := by
    rw [actualEnvironment ordered, OriginalRichFrame.merge_environmentCost]
    apply Nat.max_le.mpr
    constructor
    · change environmentCost (emptyFrame.dependencyEnvironment ordered) ≤ environmentCost (originalFrame.dependencyEnvironment controls.ordered)
      rw [show ordered = headerOrdered from Subsingleton.elim _ _,
        show controls.ordered = headerOrdered from Subsingleton.elim _ _]
      rw [selected.frame.historyGroup_environmentCost ownerOrdered headerOrdered emptyEntries _ _ selectedBound,
        originalTail.historyGroup_environmentCost ownerOrdered headerOrdered entries _ _ tailBound]
      exact Nat.le_refl _
    · exact Nat.le_of_eq (congrArg environmentCost (congrArg originalFrame.dependencyEnvironment (Subsingleton.elim _ _)))
  have emptyWorlds : emptyWorld.worlds =
      ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
        baselines.2 (history.route.worldReserve routeInputs)).append
        (WorldEnvironmentProvenance.group ownerControls controls initialProvenance selectedWorld.environment emptyEntries)).worlds :=
    WorldGenerated.historyGroup_worlds selectedWorld domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated selectedBound emptyEntries emptyScopes ownerControls emptyOwners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  have groupWorlds : group.worlds =
      ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
        baselines.2 (history.route.worldReserve routeInputs)).append
        (WorldEnvironmentProvenance.group ownerControls controls initialProvenance generated.environment entries)).worlds :=
    WorldGenerated.historyGroup_worlds generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  have emptyCovered : Covered (@EquationControlMeasure.Less strata.rules.length) emptyWorld.worlds group.worlds := by
    rw [emptyWorlds, groupWorlds, WorldEnvironmentProvenance.worlds_append, WorldEnvironmentProvenance.worlds_append]
    have reserveIncluded : Covered (@EquationControlMeasure.Less strata.rules.length)
        (WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
          baselines.2 (history.route.worldReserve routeInputs)).worlds
        ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
          baselines.2 (history.route.worldReserve routeInputs)).worlds ++
          (WorldEnvironmentProvenance.group ownerControls controls initialProvenance generated.environment entries).worlds) :=
      fun world member => ⟨world, List.mem_append_left _ member, .inl rfl⟩
    exact reserveIncluded.merge (Covered.trans EquationControlMeasure.less_trans
      (WorldEnvironmentProvenance.group_covered_history ownerControls controls initialProvenance
        selectedWorld.environment baselines.2 emptyEntries (history.route.worldReserve routeInputs)
        selectedBound selectedPriorCovered) reserveIncluded)
  have localCovered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds group.worlds := by
    rw [actualWorlds, WorldGenerated.merge_worlds]
    exact emptyCovered.merge (Covered.refl _)
  let wanted : WorldVariableDemand env U registry target
      ((selectedAvailable.push []).append (available.push entries.needs)) (index + 1) requested :=
    (demand.push []).availableMono (fun i need member => List.mem_append_left _ member)
  exact ⟨{
    locals := Locals.push locals
    available := (selectedAvailable.push []).append (available.push entries.needs)
    realization := realized
    generation := actual
    replayable := actualReplayable
    controlled := actualReady
    compatible := actualCompatible
    hereditary := actualH
    capacity := localCapacity
    covered := localCovered
    demand := wanted }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
