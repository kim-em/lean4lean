import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientScopedSeedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientParameterComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedLedger

/-! Build an operative empty declaration slot from its retained original seed
history. Even without current demands, the raw substitution is justified by
the actual history replay, and both the history and fixed baseline survive. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

section
variable
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {ownerContext : ContextDerivation sourceEnv U source}
    (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (nominalProvenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedGenerated : AmbientCaptureGenerated base scope.caps scope.left scope.right scope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (history : OriginalSeedTypeHistory seed scope.toOriginalOwnerScope graph domainProvenance prior ordered headerOrdered)
    (historyGenerated : history.route.AmbientGenerated base scope.caps)

include seedGenerated historyGenerated displayed in
/-- Empty query replay still returns a checked raw type path. It therefore
constructs the substitution of an empty group without an alignment premise. -/
theorem OriginalSeedTypeHistory.captureEmptyAmbient
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ownerAmbient : ownerGraph.Ambient env) (nominalAmbient : nominalGraph.Ambient env)
    (priorAmbient : prior.frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : history.route.schedule < limit) :
    ∃ next : AmbientParameterReplyFrame base commonCaps
        (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight,
      environmentCost (next.realization.frame.dependencyEnvironment headerOrdered) =
        environmentCost (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
          (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve) := by
  let display := seed.assignedOwnerScopeDisplay scope.toOriginalOwnerScope
  let empty : RichGradedResult sourceEnv env U registry target seed.owner.node.typeFormation.node
      seed.ownerLocals seed.ownerLeft seed.ownerAvailable (Profile.empty : Profile 0) := {
    rank := 0, bound := Nat.le_refl _, raw := .empty, footprint := []
    observation := .code (.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ member => nomatch member
    live := Profile.Live.empty }
  obtain ⟨incoming⟩ := AmbientBoundedGeneratedQueryReply.ofFrame
    (capacity := environmentCost (seed.frame.dependencyEnvironment ordered)) display seed.frame seedGenerated
    seed.substitutions seed.ownerClosed empty (fun _ => Nat.le_refl _)
  have realized : (seed.owner.assigned.subst scope.raw).subst scope.left =
      seed.owner.assigned.subst seed.ownerLeft := by
    rw [subst_subst, ← seedGenerated.capped.generated.realizations.1]
  let initial : AmbientBoundedParameterReply base scope.caps
      (seed.owner.assigned.subst seed.ownerLeft) display scope.left scope.right
      (Profile.empty : Profile 0) (environmentCost (seed.frame.dependencyEnvironment ordered)) := {
    reply := incoming.toBoundedGeneratedQueryReply
    generation := incoming.generation
    related := by intro future lift insertion atom member; cases member
    path := by
      change TypeConversion _ _ _ _ ((seed.owner.assigned.subst scope.raw).subst scope.left)
      rw [realized]
      exact .refl }
  obtain ⟨transported⟩ := history.route.replayAmbient historyGenerated henv hscoped formed bank scheduled initial
    (Profile.HasType.empty (Profile.WF.sort true))
  let selected : AmbientBoundedGeneratedQueryReply base scope.caps
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      scope.left scope.right (Profile.empty : Profile 0)
      (environmentCost (prior.frame.dependencyEnvironment headerOrdered)) :=
    ⟨transported.reply, transported.generation⟩
  obtain ⟨chosen⟩ := selected.unweaken scope.insertion scope.leftTail scope.rightTail scope.capsTail
  let entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      chosen.answer.reply.locals (raw.comp commonLeft) chosen.answer.reply.available
      ownerInitial rawCapture leftValue rightValue := []
  let reserve := groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
    (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
  let next := (chosen.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve reserve
  have generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) next.raw :=
    .historyGroup chosen.generation domain ownerGraph nominalGraph nominal nominalProvenance displayed
      ordered headerOrdered ownerInitial seed scope seedGenerated domainProvenance prior history
      historyGenerated.wellFormed historyGenerated.frames (chosen.bounded headerOrdered)
      entries (by intro entry member; simp only [entries, List.not_mem_nil] at member)
      (by intro entry member; simp only [entries, List.not_mem_nil] at member)
      ownerAmbient nominalAmbient priorAmbient historyGenerated.ambient
  have destination : (((A.subst raw).lift' (.skipN .refl seed.depth)).subst scope.left) =
      A.subst (raw.comp commonLeft) := by
    rw [subst_lift', scope.leftTail, subst_subst]
  have path : TypeConversion env U target (seed.owner.assigned.subst seed.ownerLeft)
      (A.subst (raw.comp commonLeft)) := by
    simpa only [OriginalOwnerScope.declaredTypeDisplay, destination] using transported.path
  have rawPair := (seed.owner.node.sound.defeq.mono seedGenerated.ambient.2.below).substDF henv
    seed.substitutions.wf formed seed.substitutions
  have atDeclared := path.cast rawPair
  rw [seed.left_eq, seed.right_eq] at atDeclared
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons leftValue) ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    .cons chosen.answer.reply.realization.substitutions (domain.sound.defeq.mono priorAmbient.below) atDeclared
  obtain ⟨realized, realizedGenerated, same⟩ := generated.realize next substitutions
  refine ⟨{ locals := Locals.push chosen.answer.reply.locals
            available := chosen.answer.reply.available.push []
            realization := realized
            capped := realizedGenerated.capped
            closed := ?_
            generation := realizedGenerated }, ?_⟩
  · exact Valuation.push_atomized_closed chosen.answer.reply.closed []
  · rw [same]
    exact chosen.answer.reply.realization.frame.historyGroup_environmentCost ordered headerOrdered entries
      (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve (chosen.bounded headerOrdered)

end

/-- Every auxiliary prefix advances one source slot. The same actual route
ledger is used for each parallel declaration context. -/
noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteOccurrence.historyGroupLedger
    (sources : ParameterRouteSources sourceEnv U)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {headerOrdered : headerEnv.Ordered}
    (occurrence : ParameterRouteOccurrence sources headerOrdered (.ref domain))
    (previous : ParameterRouteLedger sources ownerInitial count priorEnvironment)
    (charged : ParameterRouteCharges sources ownerInitial count reserve) :
    ParameterRouteLedger sources ownerInitial (count+1)
      (groupCaptureHistoryReserve sources.field sources.major domain sources.ordered headerOrdered
        ownerInitial priorEnvironment reserve) := by
  let next := ParameterRouteLedger.capture occurrence.captureDomain sources.rootOwners previous charged
  apply ParameterRouteLedger.bounded next
  simpa only [actualParameterRouteStepEnvironment, groupCaptureHistoryReserve, groupCaptureBaseline,
    ParameterRouteSources.rootOwners, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, groupedOwnerClosure, Dependency.LocatedOrigin.closure, Located.dependencyEnvironment,
    EndpointState.dependencyOrigin] using
    occurrence.actualStep_bound sources.rootOwners priorEnvironment reserve ownerInitial

theorem OriginalSeedTypeHistory.captureEmptyAmbient_counted
    {base : OriginalCaptureBase env U registry target}
    (sources : ParameterRouteSources sourceEnv U)
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (headerOrdered : headerEnv.Ordered)
    {ownerContext : ContextDerivation sourceEnv U sources.source}
    (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (nominalProvenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (seed : PendingRichCapture (field := sources.field) (major := sources.major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedGenerated : AmbientCaptureGenerated base scope.caps scope.left scope.right scope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (history : OriginalSeedTypeHistory seed scope.toOriginalOwnerScope graph domainProvenance prior
      sources.ordered headerOrdered)
    (historyGenerated : history.route.AmbientGenerated base scope.caps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ownerAmbient : ownerGraph.Ambient env) (nominalAmbient : nominalGraph.Ambient env)
    (priorAmbient : prior.frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : history.route.schedule < limit)
    (occurrence : ParameterRouteOccurrence sources headerOrdered (.ref domain))
    (previous : ParameterRouteLedger sources ownerInitial count (prior.frame.dependencyEnvironment headerOrdered))
    (charged : history.route.Charged sources ownerInitial count) :
    ∃ next : AmbientParameterReplyFrame base commonCaps
        (.capture graph domain nominalGraph nominal nominalProvenance) commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (next.realization.frame.dependencyEnvironment headerOrdered)) := by
  obtain ⟨next, cost⟩ := history.captureEmptyAmbient sources.ordered headerOrdered ownerGraph nominalGraph nominal
    nominalProvenance displayed seed scope seedGenerated domainProvenance prior historyGenerated
    henv hscoped formed ownerAmbient nominalAmbient priorAmbient bank scheduled
  exact ⟨next, ⟨.bounded (occurrence.historyGroupLedger sources previous
    (history.route.chargedReserve charged)) _ (Nat.le_of_eq cost)⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
