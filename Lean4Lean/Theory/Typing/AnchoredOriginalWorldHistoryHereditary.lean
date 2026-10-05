import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! Finite ancestry of the actual history-group producer, including every
positional route and owner occurrence. No semantic rebuilding answer is stored. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable def WorldGenerated.Hereditary.historyGroup
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
    (tailH : generated.Hereditary frontier)
    (seedH : seedGenerated.Hereditary frontier)
    (seedSame : seedControls.HasPrefix controls.cutoff controls.fuel)
    (priorH : priorGenerated.Hereditary frontier)
    (routeH : ∀ index, (historyGenerated index).Hereditary frontier)
    (routeSame : ∀ index, (historyControls index).HasPrefix controls.cutoff controls.fuel)
    (ownersH : ∀ entry member, (owners entry member).Hereditary frontier)
    (ownerSame : ownerControls.HasPrefix controls.cutoff controls.fuel) :
    (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).Hereditary frontier := by
  let routeBases := WorldBaseHistories.flatMap (List.finRange history.route.frames.length)
    (fun index => (historyGenerated index).baseUses) (fun index => (routeH index).bases)
  let ownerBases := WorldBaseHistories.flatMap entries.attach
    (fun entry => (owners entry.val entry.property).baseUses)
    (fun entry => (ownersH entry.val entry.property).bases)
  refine ⟨⟨tailH.tablesClosed, seedH.tablesClosed, priorH.tablesClosed,
    (fun index => (routeH index).tablesClosed), (fun entry member => (ownersH entry member).tablesClosed)⟩,
    (((tailH.bases.append seedH.bases).append priorH.bases).append routeBases).append ownerBases, ?_⟩
  apply WorldBaseHistories.ready_append
  · apply WorldBaseHistories.ready_append
    · apply WorldBaseHistories.ready_append
      · apply WorldBaseHistories.ready_append
        · exact tailH.ready
        · simpa only [seedSame.1, seedSame.2] using seedH.ready
      · exact priorH.ready
    · apply WorldBaseHistories.ready_flatMap
      intro index _
      simpa only [(routeSame index).1, (routeSame index).2] using (routeH index).ready
  · apply WorldBaseHistories.ready_flatMap
    intro entry _
    simpa only [ownerSame.1, ownerSame.2] using (ownersH entry.val entry.property).ready

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
