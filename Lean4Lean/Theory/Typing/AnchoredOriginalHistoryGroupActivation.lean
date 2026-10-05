import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalScopedSeedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedScopedGroupActivation

/-! Activate a retained capture by replaying its original finite type history.
Query selection changes entries and the active declaration tail, never the
seed, history, or baseline reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

section
variable
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalCaptureRealization graph env registry target headerLocals commonLeft commonRight headerAvailable)
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
    (seedCapped : CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (history : OriginalSeedTypeHistory seed scope.toOriginalOwnerScope graph domainProvenance prior ordered headerOrdered)
    (historyGenerated : history.route.Generated base scope.caps)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode)

private noncomputable def activationReserve : List Closure :=
  groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
    (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve

include ownerGraph displayed seedCapped historyGenerated

/-- The only semantic calls are the fixed original owner F and the finite
original calls stored in the seed history. The selected owner reply is an
actual smaller R result; no source equality between inferred and declared
types is assumed. -/
theorem generatedHistoryGroupActivation
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (selected : BoundedGeneratedQueryReply base scope.caps (seed.seedDisplay scope.graph)
      scope.left scope.right (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered)))
    (ownerF : seed.owner.ComputationalInductionAt env registry ordered seed.initialContext
      (Closure.close (variableNode.dependencyOrigin headerOrdered)
        (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered)).cost)
    (calls : history.route.Calls base scope.caps
      (richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin headerOrdered)
        (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered)).cost)) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance variableNode variableProvenance)
      commonLeft commonRight requested,
      environmentCost (reply.reply.realization.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered) := by
  let pending := (seed.requery scope.graph seedCapped ordered selected).reheader
    headerLocals (raw.comp commonLeft) headerAvailable
  have pendingCapped := seed.requery_capped scope.graph seedCapped ordered selected
  let reserve := activationReserve ordered headerOrdered seed scope domainProvenance prior history
  let incoming := (tail.frame.group domain ordered ownerInitial entries).reserve reserve
  have ownerBound := pending.group_owner_activation_bound ordered headerOrdered tail.frame entries
    (variableNode.dependencyOrigin headerOrdered)
  have parentBound : (Closure.close (variableNode.dependencyOrigin headerOrdered)
      ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost ≤
      (Closure.close (variableNode.dependencyOrigin headerOrdered) (incoming.dependencyEnvironment headerOrdered)).cost := by
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    change _ ≤ environmentCost (reserve ++ _)
    rw [merge_environmentCost_append]
    exact Nat.le_max_right _ _
  obtain ⟨value⟩ := ownerF.apply pending.frame
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ownerBound) parentBound)
    pending.ownerClosed formed pending.substitutions pending.query pending.queryAvailable
  have scheduled : history.route.schedule < richSchedule .fundamental
      (Closure.close (variableNode.dependencyOrigin headerOrdered) (incoming.dependencyEnvironment headerOrdered)).cost :=
    history.route.paid _ _ (fun closure member =>
      List.mem_append_left _ (List.mem_append_left _ member))
  obtain ⟨chosen, alignment, valueEq⟩ := pending.alignScopeRoute scope pendingCapped domainProvenance
    ordered (seed.frame.dependencyEnvironment ordered) (selected.bounded ordered)
    history.route historyGenerated henv hscoped formed calls scheduled value.toRichSupportedValue
  let current := pending.reheader chosen.answer.reply.locals (raw.comp commonLeft) chosen.answer.reply.available
  let entry := current.complete alignment
  let nextEntries : RichGroupedCapture (field := field) (major := major) domain env registry target
      chosen.answer.reply.locals (raw.comp commonLeft) chosen.answer.reply.available ownerInitial
      rawCapture leftValue rightValue := [entry]
  let frame := (chosen.answer.reply.realization.frame.group domain ordered ownerInitial nextEntries).reserve reserve
  have capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) frame.raw :=
    .historyGroup chosen.answer.capped domain ownerGraph nominalGraph nominal nominalProvenance displayed
      ordered headerOrdered ownerInitial seed scope seedCapped domainProvenance prior history
      historyGenerated.wellFormed historyGenerated.frames (chosen.bounded headerOrdered) nextEntries
      (fun e member => by cases List.mem_singleton.mp member; exact scope)
      (by intro e member; cases List.mem_singleton.mp member; exact pendingCapped)
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  rw [pending.left_eq, pending.right_eq] at rawPair
  have atDeclared := alignment.path.cast rawPair
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons leftValue) ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    .cons chosen.answer.reply.realization.substitutions (domain.sound.defeq.mono headerBelow) atDeclared
  obtain ⟨realized, realizedCapped, same⟩ := capped.realize frame substitutions
  refine ⟨⟨{
    locals := Locals.push chosen.answer.reply.locals
    available := chosen.answer.reply.available.push nextEntries.needs
    realization := realized
    generated := realizedCapped.generated
    query := {
      rank := selected.answer.reply.query.rank
      bound := selected.answer.reply.query.bound
      raw := selected.answer.reply.query.raw
      footprint := [(0, Need.mk pending.rank pending.input)]
      observation := .legacy (.legacy (.var _ _ 0 pending.input))
      adapter := selected.answer.reply.query.adapter
      resources := ?_
      live := value.related.live henv hscoped formed }
    closed := ?_ }, realizedCapped⟩, ?_⟩
  · intro i need member
    cases List.mem_singleton.mp member
    change Need.mk pending.rank pending.input ∈ captureNeeds pending.input ++ []
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
  · change (chosen.answer.reply.available.push (captureNeeds pending.input ++ [])).AtomClosed
    simpa only [captureNeeds, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      Valuation.push_atomized_closed chosen.answer.reply.closed [⟨pending.rank, pending.input⟩]
  · rw [same]
    exact chosen.answer.reply.realization.frame.historyGroup_replay_nonGrowth ordered headerOrdered
      nextEntries (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
      (chosen.bounded headerOrdered) (tail.frame.group domain ordered ownerInitial entries)

/-- Full activation starts from the actual incoming query and constructs the
selected owner query by the strictly smaller original expression-R call. -/
theorem reindexHistoryGroupHead
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (left : OriginalNestedDisplay U scope.scope (seed.owner.expression.subst scope.raw) leftAssigned)
    (leftOrdered : left.sourceEnv.Ordered)
    (leftFrame : OriginalCaptureRealization left.graph env registry target
      leftLocals scope.left scope.right leftAvailable)
    (leftCapped : CappedCaptureGenerated base scope.caps scope.left scope.right left.graph leftFrame.frame.raw)
    (leftClosed : leftAvailable.AtomClosed)
    (reindex : GeneratedObservationCall base scope.caps left (seed.seedDisplay scope.graph)
      scope.left scope.right leftOrdered ordered
      (richSchedule .expressionReindex
        ((Closure.close (left.node.dependencyOrigin leftOrdered)
          (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (variableNode.dependencyOrigin headerOrdered)
          (((tail.frame.group domain ordered ownerInitial entries).reserve
            (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered)).cost)))
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp scope.left) (requested : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (ownerF : seed.owner.ComputationalInductionAt env registry ordered seed.initialContext
      (Closure.close (variableNode.dependencyOrigin headerOrdered)
        (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered)).cost)
    (calls : history.route.Calls base scope.caps
      (richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin headerOrdered)
        (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered)).cost)) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance variableNode variableProvenance)
      commonLeft commonRight requested,
      environmentCost (reply.reply.realization.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost (((tail.frame.group domain ordered ownerInitial entries).reserve
          (activationReserve ordered headerOrdered seed scope domainProvenance prior history)).dependencyEnvironment headerOrdered) := by
  let reserve := activationReserve ordered headerOrdered seed scope domainProvenance prior history
  let incoming := (tail.frame.group domain ordered ownerInitial entries).reserve reserve
  let headerSeed := seed.reheader headerLocals (raw.comp commonLeft) headerAvailable
  obtain ⟨seedFrame, actualSeedCapped, same⟩ := seedCapped.realize seed.frame seed.substitutions
  have ownerBound := headerSeed.group_owner_activation_bound ordered headerOrdered tail.frame entries
    (variableNode.dependencyOrigin headerOrdered)
  have parentBound : (Closure.close (variableNode.dependencyOrigin headerOrdered)
      ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost ≤
      (Closure.close (variableNode.dependencyOrigin headerOrdered) (incoming.dependencyEnvironment headerOrdered)).cost := by
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    change _ ≤ environmentCost (reserve ++ _)
    rw [merge_environmentCost_append]
    exact Nat.le_max_right _ _
  have strict : richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
       (Closure.close (seed.owner.node.dependencyOrigin ordered) (seedFrame.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
       (Closure.close (variableNode.dependencyOrigin headerOrdered) (incoming.dependencyEnvironment headerOrdered)).cost) := by
    rw [same ordered]
    exact richSchedule_strict (Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ownerBound) parentBound) _) _ _
  obtain ⟨answer⟩ := reindex leftFrame leftCapped leftClosed seedFrame actualSeedCapped seed.ownerClosed
    strict query resources
  let selected : BoundedGeneratedQueryReply base scope.caps (seed.seedDisplay scope.graph)
      scope.left scope.right requested (environmentCost (seed.frame.dependencyEnvironment ordered)) :=
    ⟨answer.answer, fun formed => by simpa only [same ordered] using answer.bounded formed⟩
  exact generatedHistoryGroupActivation (ownerGraph := ownerGraph) (displayed := displayed)
    ordered headerOrdered tail nominalGraph nominal nominalProvenance seed scope seedCapped
    domainProvenance prior history historyGenerated entries variableNode variableProvenance
    henv hscoped formed sourceBelow headerBelow selected ownerF calls

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
