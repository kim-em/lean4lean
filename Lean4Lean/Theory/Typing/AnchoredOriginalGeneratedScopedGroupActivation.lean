import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedGroupActivation
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex

/-! Actual heterogeneous activation under an arbitrary retained owner scope.
Recursive query selection may merge its frame; source maps, complete tails,
and immutable common caps remain explicit instead of a fabricated linear
frame-extension trace. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def PendingRichCapture.assignedScopeDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (sourceEqual : pending.owner.assigned.subst scope.raw = (A.subst raw).lift' (.skipN .refl pending.depth)) :
    OriginalNestedDisplay U scope.scope ((A.subst raw).lift' (.skipN .refl pending.depth))
      (.sort pending.owner.node.typeFormation.level) where
  sourceEnv := sourceEnv
  source := pending.owner.source
  sourceExpression := pending.owner.assigned
  sourceType := .sort pending.owner.node.typeFormation.level
  context := pending.owner.context pending.initialContext
  node := pending.owner.node.typeFormation.node
  provenance := {
    rootSource := (pending.owner.provenance pending.initialContext).rootSource
    rootExpression := (pending.owner.provenance pending.initialContext).rootExpression
    rootType := (pending.owner.provenance pending.initialContext).rootType
    root := (pending.owner.provenance pending.initialContext).root
    initial := (pending.owner.provenance pending.initialContext).initial
    location := .assignedFormation (pending.owner.provenance pending.initialContext).location
    context_eq := (pending.owner.provenance pending.initialContext).context_eq }
  raw := scope.raw
  graph := scope.graph
  expression_eq := sourceEqual.symm
  type_eq := rfl

theorem generatedScopedGroupActivation
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (tail : OriginalCaptureRealization graph env registry target headerLocals commonLeft commonRight headerAvailable)
    (tailCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (nominalProvenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture
      leftValue rightValue)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture
      leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (pendingCapped : CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph pending.frame.raw)
    (sourceEqual : pending.owner.assigned.subst scope.raw = (A.subst raw).lift' (.skipN .refl pending.depth))
    (tailClosed : headerAvailable.AtomClosed)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode)
    (ownerF : pending.owner.ComputationalInductionAt env registry ordered pending.initialContext
      (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost)
    (assignedR : GeneratedObservationCall base scope.caps
      (pending.assignedScopeDisplay scope sourceEqual)
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      scope.left scope.right ordered headerOrdered
      (richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost)) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance
        variableNode variableProvenance) commonLeft commonRight pending.input,
      environmentCost (reply.reply.realization.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered) := by
  have ownerBound := pending.group_owner_activation_bound ordered headerOrdered tail.frame entries
    (variableNode.dependencyOrigin headerOrdered)
  obtain ⟨value⟩ := ownerF.apply pending.frame
    (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ownerBound) pending.ownerClosed formed
    pending.substitutions pending.query pending.queryAvailable
  obtain ⟨sourceFrame, sourceCapped, sourceEnvironment⟩ := pendingCapped.realize pending.frame pending.substitutions
  obtain ⟨declaredFrame, declaredCapped, declaredEnvironment⟩ := tail.weakenCapped tailCapped
    scope.insertion scope.leftTail scope.rightTail scope.capsTail
  have schedule : richSchedule .expressionReindex
      ((Closure.close (pending.owner.node.typeFormation.node.dependencyOrigin ordered)
        (sourceFrame.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (domain.dependencyOrigin headerOrdered)
        (declaredFrame.frame.dependencyEnvironment headerOrdered)).cost) <
      richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost := by
    rw [sourceEnvironment, declaredEnvironment]
    exact richSchedule_strict (pending.group_activation_bound ordered headerOrdered tail.frame entries
      (variableNode.dependencyOrigin headerOrdered)) _ _
  have observation : RichObs sourceEnv env U registry target pending.owner.node.typeFormation.node
      pending.ownerLocals (scope.raw.comp scope.left) value.support value.footprint := by
    rw [← pendingCapped.generated.realizations.1]
    exact .code value.certificate
  obtain ⟨scopedPrior⟩ := assignedR sourceFrame sourceCapped pending.ownerClosed
    declaredFrame declaredCapped tailClosed schedule observation value.resources
  obtain ⟨unscoped⟩ := scopedPrior.unweaken scope.insertion scope.leftTail scope.rightTail scope.capsTail
  let prior := unscoped.answer
  have priorBound : environmentCost (prior.reply.realization.frame.dependencyEnvironment headerOrdered) ≤
      environmentCost (tail.frame.dependencyEnvironment headerOrdered) := by
    simpa only [declaredEnvironment] using unscoped.bounded headerOrdered
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.reply.query.code henv value.certificate.formed
  have pendingLeft := pendingCapped.generated.realizations.1
  have realizedEqual : pending.owner.assigned.subst pending.ownerLeft = A.subst (raw.comp commonLeft) := by
    rw [pendingLeft, ← subst_subst, sourceEqual, subst_lift', scope.leftTail, subst_subst]
  let chosen := pending.reheader prior.reply.locals (raw.comp commonLeft) prior.reply.available
  let entry := chosen.completeReconstructed value certificate resources realizedEqual
  let selected : RichGroupedCapture (field := field) (major := major) domain env registry target
      prior.reply.locals (raw.comp commonLeft) prior.reply.available ownerInitial rawCapture
      leftValue rightValue := [entry]
  let frame := prior.reply.realization.frame.group domain ordered ownerInitial selected
  have capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) frame.raw :=
    .scopedGroup prior.capped domain ownerGraph nominalGraph nominal nominalProvenance displayed
      ordered ownerInitial chosen scope pendingCapped selected
      (fun e member => by cases List.mem_singleton.mp member; exact scope)
      (by intro e member; cases List.mem_singleton.mp member; exact pendingCapped)
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  rw [pending.left_eq, pending.right_eq, realizedEqual] at rawPair
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons leftValue)
      ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    Ctx.SubstEq.cons prior.reply.realization.substitutions
    (domain.sound.defeq.mono headerBelow) rawPair
  obtain ⟨realized, realizedCapped, same⟩ := capped.realize frame substitutions
  refine ⟨⟨{
    locals := Locals.push prior.reply.locals
    available := prior.reply.available.push selected.needs
    realization := realized
    generated := realizedCapped.generated
    query := ?_
    closed := ?_ }, realizedCapped⟩, ?_⟩
  · refine {
      rank := pending.rank, bound := Nat.le_refl _, raw := pending.input
      footprint := [(0, Need.mk pending.rank pending.input)]
      observation := .legacy (.legacy (.var _ _ 0 pending.input))
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := ?_
      live := value.related.live henv hscoped formed }
    intro i need member
    cases List.mem_singleton.mp member
    change Need.mk pending.rank pending.input ∈ captureNeeds pending.input ++ []
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
  · change (prior.reply.available.push (captureNeeds pending.input ++ [])).AtomClosed
    simpa only [captureNeeds, List.flatMap_cons, List.flatMap_nil, List.append_nil] using Valuation.push_atomized_closed prior.reply.closed [⟨pending.rank, pending.input⟩]
  · rw [same, OriginalRichFrame.group_environment, OriginalRichFrame.group_environment]
    exact entries.environment_mono ordered headerOrdered selected _ _ priorBound

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
