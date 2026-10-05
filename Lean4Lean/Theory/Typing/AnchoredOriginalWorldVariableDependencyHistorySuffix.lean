import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyHistoryTailRebuild

/-! The history suffix invokes the structural demand IH on its exact active
tail and rebuilds the full dormant history under the original caller. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem environmentCost_append_right (first second : List Closure) :
    environmentCost second ≤ environmentCost (first ++ second) := by
  rw [merge_environmentCost_append]
  exact Nat.le_max_right _ _

theorem WorldGenerated.ReindexDependencyAt.historyGroupTail
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
    (ih : generated.ReindexDependencyAt index) :
    (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).ReindexDependencyAt (index + 1) := by
  let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  have tailSubstitutions := by
    cases substitutions with
    | cons tail _ _ => exact tail
  have tailQueries : generated.retainedQueries ⊆ group.retainedQueries := by
    intro query member
    change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr member))))
  obtain ⟨tailReady⟩ := ready.selectGeneration generated tailQueries rfl rfl
  have tailBases : generated.baseUses.Sublist group.baseUses := by
    change generated.baseUses.Sublist (generated.baseUses ++ seedGenerated.baseUses ++ priorGenerated.baseUses ++
      (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
      entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
    simpa only [List.append_assoc] using List.sublist_append_left generated.baseUses
      (seedGenerated.baseUses ++ priorGenerated.baseUses ++
        (List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses) ++
        entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses))
  obtain ⟨tailHereditary⟩ := hereditary.selectGeneration generated hereditary.tablesClosed.1 tailBases rfl rfl
  have tailCapacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost group.environment.closures := by
    change environmentCost (tail.dependencyEnvironment controls.ordered) ≤
      environmentCost (_ ++ (_ :: _ :: _ :: _ ++ tail.dependencyEnvironment controls.ordered))
    rw [merge_environmentCost_append]
    apply Nat.le_trans ?_ (Nat.le_max_right _ _)
    apply Nat.le_trans ?_ (Nat.le_max_right _ _)
    apply Nat.le_trans ?_ (Nat.le_max_right _ _)
    apply Nat.le_trans ?_ (Nat.le_max_right _ _)
    exact environmentCost_append_right _ _
  have entriesMember (values : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals (raw.comp commonLeft) available ownerInitial rawCapture leftValue rightValue)
      {world} (member : world ∈ generated.worlds) :
      world ∈ (WorldEnvironmentProvenance.groupEntries ownerControls controls initialProvenance generated.environment values).worlds := by
    induction values with
    | nil => exact member
    | cons entry rest ih => exact List.mem_append_right _ ih
  have tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds destinationBaseline.worlds := by
    intro world member
    apply destinationCovered world
    change world ∈ group.worlds
    dsimp only [group]
    rw [WorldGenerated.historyGroup_worlds, WorldEnvironmentProvenance.worlds_append]
    apply List.mem_append_right
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (entriesMember entries member)))
  obtain ⟨selected⟩ := ih frontier (Nat.lt_of_succ_lt_succ inRange) replayable.1 compatible.1 tailReady tailHereditary valid.1 tailSubstitutions
    destinationBaseline (Nat.le_trans tailCapacity destinationCapacity) tailCovered
    caller insertion leftTail rightTail capsTail left leftControls sameCutoff sameFuel
    leftBaseline leftFrame leftData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary
  exact rebuildWorldHistoryGroupVariableDependency generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
        frontier replayable ready compatible hereditary valid.1 substitutions selected

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
