import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryGroupActivation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerScopeInsertion
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHeadQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection

/-! The history capture arm extracts the actual dormant seed, prior and
positional route frames. Its fixed outer destination budget survives merges;
only proper retained child calls are transferred to that budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeHeadQuery from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHeadQuery
open private rawOwners from Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration
open private lifted_substitution from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedCaptureReindex
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

private theorem controls_ext (first second : OriginalWorldControls strata sourceEnv)
    (cutoff : first.cutoff = second.cutoff) (fuel : first.fuel = second.fuel) : first = second := by
  cases first
  cases second
  cases cutoff
  cases fuel
  rfl

private theorem sublist_middle (left middle right : List α) : middle.Sublist (left ++ middle ++ right) :=
  (List.sublist_append_right left middle).trans (List.sublist_append_left _ right)

theorem WorldGenerated.ReindexDemandAt.historyGroup
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
    (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).ReindexDemandAt 0 := by
  let group := WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  intro frontier replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps ρ insertion leftTail rightTail capsTail
    leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  have seedPrefix := WorldGenerated.UsesControlPrefix.controls_match (generated := seedGenerated) compatible.2.1
  have ownerPrefix : ownerControls.HasPrefix controls.cutoff controls.fuel := compatible.2.2.2.2.2
  have ownerEq : ownerControls = seedControls := controls_ext _ _
    (ownerPrefix.1.trans seedPrefix.1.symm) (ownerPrefix.2.trans seedPrefix.2.symm)
  subst ownerControls
  rcases replayable with ⟨tailReplayable, seedReplayable, priorReplayable, routeReplayable,
    ownersReplayable, ownersCovered, ⟨seedArgument, seedCovered⟩, seedBaselineCovered, priorBaselineCovered,
    ⟨boundary, coherent⟩, tailCovered⟩
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
  let seedQueryReady := seedQuery.recontrol seedControls seedPrefix.1.symm seedPrefix.2.symm
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
  let routeData : history.route.ControlledWorldData P base seedScope.caps seedControls.cutoff seedControls.fuel frontier := {
    generated := {
      wellFormed := historyWellFormed, ambient := routeAmbient, sources := routeSources
      frames := by
        intro boxed member
        obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
        subst boxed
        exact (historyGenerated ⟨index, bound⟩).erase }
    inputs := routeInputs, controls := historyControls, frames := historyGenerated
    ready := fun index => (Classical.choice (frameData index)).1
    compatible := fun index => by
      rw [seedPrefix.1, seedPrefix.2]
      exact compatible.2.2.2.1 index
    replayable := routeReplayable
    hereditary := fun index => (Classical.choice (frameData index)).2 }
  have seedCompatible : seedGenerated.UsesControlPrefix seedControls.cutoff seedControls.fuel := by
    rw [seedPrefix.1, seedPrefix.2]
    exact compatible.2.1
  let currentTail := WorldEnvironmentProvenance.group seedControls controls initialProvenance generated.environment entries
  have currentWorlds : group.worlds =
      ((WorldEnvironmentProvenance.groupHistory field major domain seedControls controls initialProvenance
        baselines.2 (history.route.worldReserve routeInputs)).append currentTail).worlds :=
    WorldGenerated.historyGroup_worlds generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes seedControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
  have sourceEqual : seed.owner.expression.subst seedScope.raw =
      (argument.subst nominalRaw).lift' (.skipN .refl seed.depth) := by
    rw [seed.expression_eq, seedScope.raw_eq, ← displayed]
    exact lifted_substitution _ _ _
  obtain ⟨expanded, across, over⟩ := ownerScopeInsertion seedScope.insertion insertion
  let expandedLeft := retainedPrefix seed.depth seedScope.left nextLeft
  let expandedRight := retainedPrefix seed.depth seedScope.right nextRight
  let expandedCaps := retainedPrefix seed.depth seedScope.caps nextCaps
  have leftOver : Subst.lift_l (.skipN .refl seed.depth) expandedLeft = nextLeft := by
    funext i
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, expandedLeft, expandedRight, expandedCaps] using
      retainedPrefix_tail seed.depth seedScope.left nextLeft i
  have rightOver : Subst.lift_l (.skipN .refl seed.depth) expandedRight = nextRight := by
    funext i
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, expandedLeft, expandedRight, expandedCaps] using
      retainedPrefix_tail seed.depth seedScope.right nextRight i
  have capsOver : (fun i => expandedCaps ((Lift.skipN .refl seed.depth).liftVar i)) = nextCaps := by
    funext i
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, expandedLeft, expandedRight, expandedCaps] using
      retainedPrefix_tail seed.depth seedScope.caps nextCaps i
  have leftAcross : Subst.lift_l (ρ.consN seed.depth) expandedLeft = seedScope.left := by
    funext i
    apply retainedPrefix_pullback ρ seed.depth seedScope.left nextLeft _ i
    intro j
    have before := congrFun seedScope.leftTail j
    have after := congrFun leftTail j
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar] using after.trans before.symm
  have rightAcross : Subst.lift_l (ρ.consN seed.depth) expandedRight = seedScope.right := by
    funext i
    apply retainedPrefix_pullback ρ seed.depth seedScope.right nextRight _ i
    intro j
    have before := congrFun seedScope.rightTail j
    have after := congrFun rightTail j
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar] using after.trans before.symm
  have capsAcross : (fun i => expandedCaps ((ρ.consN seed.depth).liftVar i)) = seedScope.caps := by
    funext i
    apply retainedPrefix_pullback ρ seed.depth seedScope.caps nextCaps _ i
    intro j
    have before := congrFun seedScope.capsTail j
    have after := congrFun capsTail j
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar] using after.trans before.symm
  have sourceAcross : (seed.owner.expression.subst seedScope.raw).lift' (ρ.consN seed.depth) =
      ((argument.subst nominalRaw).lift' ρ).lift' (.skipN .refl seed.depth) := by
    rw [sourceEqual, ← VExpr.lift'_comp, ← VExpr.lift'_comp]
    simp only [Lift.skipN_comp_consN, Lift.refl_comp, Lift.comp_skipN, Lift.comp]
  let lifted := left.weaken over
  let scopedLeft : OriginalNestedDisplay U expanded
      ((seed.owner.expression.subst seedScope.raw).lift' (ρ.consN seed.depth))
      (leftAssigned.lift' (.skipN .refl seed.depth)) :=
    { lifted with expression_eq := sourceAcross.trans lifted.expression_eq }
  let scopedGenerated := WorldGenerated.weaken leftData.generation over leftOver rightOver capsOver
  have scopedReady : scopedGenerated.Controlled frontier :=
    ⟨leftData.controlled.annotation, leftData.controlled.within, leftData.controlled.sponsored⟩
  let scopedHereditary := leftData.hereditary.weaken over leftOver rightOver capsOver
  obtain ⟨scopedFrame, actual, actualQuery, actualReplayable, actualWorlds, actualCompatible,
      ⟨actualReady⟩, ⟨actualQueryReady⟩, sameQuery, sameEnvironment, ⟨actualHereditary⟩⟩ :=
    realizeHeadQuery leftFrame.frame scopedGenerated leftData.replayable scopedHereditary leftFrame.substitutions
      leftData.compatible scopedReady requested requestedReady
  let scopedData : WorldCallFrameData (P := P) (base := base) (caps := expandedCaps)
      (display := scopedLeft) leftControls leftBaseline frontier scopedFrame := {
    generation := actual, replayable := actualReplayable, controlled := actualReady, compatible := actualCompatible
    closed := leftData.closed
    capacity := by rw [sameEnvironment]; exact leftData.capacity
    covered := by rw [actualWorlds]; exact leftData.covered
    hereditary := actualHereditary }
  obtain ⟨answer⟩ := reindexWorldHistoryGroupDemandAt ownerGraph nominalGraph nominal provenance displayed
    seed seedScope seedControls controls frontier _ seedGenerated seedReplayable seedArgument seedHereditary seedReady
    seedCompatible seedQueryReady domainProvenance prior priorGenerated priorReplayable priorHereditary priorReady
    compatible.2.2.1 history initialProvenance baselines ⟨seedBaselineCovered, priorBaselineCovered⟩ seedCovered
    routeData boundary coherent ownerAmbient ownerSources nominalAmbient nominalSources caller
    henv hscoped formed bank unary currentTail destinationBaseline (by
      simpa only [WorldEnvironmentProvenance.closures, RawOriginalRichFrame.dependencyEnvironment,
        rawOwners, RichGroupedCapture.environment] using destinationCapacity) (by rw [← currentWorlds]; exact destinationCovered)
    across leftAcross rightAcross capsAcross scopedLeft leftControls leftBaseline
    (sameCutoff.trans seedPrefix.1.symm) (sameFuel.trans seedPrefix.2.symm)
    scopedFrame scopedData rfl sponsored actualQuery requestedAvailable actualQueryReady
  exact ⟨{ answer with
    capacity := fun ordered => by
      simpa only [WorldEnvironmentProvenance.closures, RawOriginalRichFrame.dependencyEnvironment,
        rawOwners, RichGroupedCapture.environment] using answer.capacity ordered
    covered := by
      change Covered _ answer.generation.worlds group.worlds
      rw [currentWorlds]
      exact answer.covered }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
