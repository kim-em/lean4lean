import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryPreservation

/-! Exact world ledger of the real history-group producer. The original
prior and the selected current tail remain distinct witnesses. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private historyLedgerOfEntries rawOwners from Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem environment_worlds_mpr
    {first second : List OriginalClosureMeasure.Closure}
    (indices : first = second)
    (equal : WorldEnvironmentProvenance strata U first = WorldEnvironmentProvenance strata U second)
    (annotation : WorldEnvironmentProvenance strata U second) :
    (equal.mpr annotation).worlds = annotation.worlds := by
  cases indices
  cases equal
  rfl

theorem WorldGenerated.historyGroup_worlds
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
    (routeSources : history.route.AllSources P) :
    (WorldGenerated.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).worlds =
      ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls
        initialProvenance baselines.2 (history.route.worldReserve routeInputs)).append
        (WorldEnvironmentProvenance.group ownerControls controls initialProvenance generated.environment entries)).worlds := by
  simp only [WorldGenerated.worlds, WorldGenerated.environment, WorldGenerated.callControls,
    WorldEnvironmentProvenance.worlds_append, historyLedgerOfEntries]
  congr 1
  rw [environment_worlds_mpr]
  simp only [RawOriginalRichFrame.dependencyEnvironment, rawOwners, RichGroupedCapture.environment]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
