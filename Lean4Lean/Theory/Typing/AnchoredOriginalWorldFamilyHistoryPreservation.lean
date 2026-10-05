import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix

/-! The actual family history producer preserves controls on all retained
queries: current entries, tail, seed, prior frame, route frames and owners.
All independent controls must have the genuine inherited cutoff/fuel.
This theorem preserves annotations and their existing sponsor frontier;
it neither reconstructs missing generation witnesses nor assumes coverage
of captured worlds from a scalar capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem controlled_list
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (queries : List (StoredOriginalQuery env U registry target))
    (ready : ∀ query ∈ queries, Nonempty (ControlledStoredQuery controls frontier query)) :
    ∃ annotation : RetainedQueryProvenance strata queries,
      EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
        (fun control => StoredOriginalQuery.maximumDepth
          (stratifiedHeadPolicy (strata.headOrdinal registry) control) queries) ∧
      Sponsored frontier annotation.worlds := by
  induction queries with
  | nil => exact ⟨.nil, fun _ _ => Nat.zero_le _, fun _ member => nomatch member⟩
  | cons query rest ih =>
    obtain ⟨head⟩ := ready query List.mem_cons_self
    obtain ⟨tail, bound, sponsored⟩ := ih (fun q member => ready q (List.mem_cons_of_mem _ member))
    refine ⟨.cons head.annotation tail, ?_, ?_⟩
    · intro control active
      exact Nat.max_le.mpr ⟨head.within control active, bound control active⟩
    · exact head.sponsored.merge sponsored

/-- Assemble the invariant for this exact generation, including every
query in its dormant histories. -/
theorem WorldGenerated.Controlled.ofRetainedQueries
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    {frontier : List (World strata.rules.length)}
    (ready : ∀ query ∈ generated.retainedQueries,
      Nonempty (ControlledStoredQuery controls frontier query)) :
    Nonempty (generated.Controlled frontier) := by
  obtain ⟨annotation, bound, sponsored⟩ := controlled_list controls frontier generated.retainedQueries ready
  refine ⟨⟨annotation, ?_, sponsored⟩⟩
  intro control active
  change generated.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ _
  rw [← generated.retainedQueries_depth]
  exact bound control active

private theorem selected_recontrol
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {childControls : OriginalWorldControls strata childSource}
    {generated : WorldGenerated strata P base caps left right graph frame childControls}
    {frontier : List (World strata.rules.length)}
    (controls : OriginalWorldControls strata sourceEnv)
    (same : childControls.HasPrefix controls.cutoff controls.fuel)
    (ready : generated.Controlled frontier)
    (member : query ∈ generated.retainedQueries) :
    Nonempty (ControlledStoredQuery controls frontier query) := by
  obtain ⟨selected⟩ := ready.selectStored member
  exact ⟨selected.recontrol controls same.1 same.2⟩

/-- Every constituent comes from the actual history constructor. No query,
frame or old history is replaced when the invariant is reassembled. -/
theorem WorldGenerated.Controlled.historyGroup
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {controls : OriginalWorldControls strata headerEnv}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : RawOriginalRichFrame headerEnv env U registry target context locals
      (raw.comp commonLeft) (raw.comp commonRight) available}
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
    {frontier : List (World strata.rules.length)}
    (tailReady : generated.Controlled frontier)
    (entryReady : ∀ query ∈ (richGroupedEntriesRaw entries).storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query))
    (seedQueryReady : ControlledStoredQuery controls frontier (.observation seed.query))
    (seedReady : seedGenerated.Controlled frontier)
    (seedSame : seedControls.HasPrefix controls.cutoff controls.fuel)
    (priorReady : priorGenerated.Controlled frontier)
    (routeReady : ∀ index, (historyGenerated index).Controlled frontier)
    (routeSame : ∀ index, (historyControls index).HasPrefix controls.cutoff controls.fuel)
    (ownersReady : ∀ entry member, (owners entry member).Controlled frontier)
    (ownerSame : ownerControls.HasPrefix controls.cutoff controls.fuel) :
    Nonempty ((WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Controlled frontier) := by
  apply WorldGenerated.Controlled.ofRetainedQueries
  intro query member
  change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
    (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
    ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
    (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries)) at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · rcases List.mem_append.mp member with member | member
          · exact entryReady query member
          · exact tailReady.selectStored member
        · rcases List.mem_cons.mp member with rfl | member
          · exact ⟨seedQueryReady⟩
          · exact selected_recontrol controls seedSame seedReady member
      · exact priorReady.selectStored member
    · obtain ⟨boxed, _, member⟩ := List.mem_flatMap.mp member
      exact selected_recontrol controls (routeSame boxed)
        (routeReady boxed) member
  · obtain ⟨entry, _, member⟩ := List.mem_flatMap.mp member
    exact selected_recontrol controls ownerSame (ownersReady entry.val entry.property) member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
