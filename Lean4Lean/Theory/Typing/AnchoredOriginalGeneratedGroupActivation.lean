import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedVariableDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedCaptureCapacity
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Query-selected heterogeneous activation. The only reconstruction call
is at the exact assigned/declared source-display pair. It may select a new
prior frame, but must satisfy the recursive reply's computed non-growth
invariant. No prior alignment, new semantic capability, or resource table is
supplied. The owner F call is below the existing (possibly empty) group. -/
theorem generatedGroupActivation
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
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (nominalProvenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture
      (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture
      (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
    (extension : OriginalFrameExtension ownerFrame.raw pending.frame.raw)
    {pendingRaw : Subst}
    (pendingGraph : OriginalCaptureMap (common := common) (pending.owner.context pending.initialContext) pendingRaw)
    (pendingCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight pendingGraph pending.frame.raw)
    (sourceEqual : pending.owner.assigned.subst pendingRaw = A.subst raw)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode)
    (ownerF : pending.owner.ComputationalInductionAt env registry ordered pending.initialContext
      (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost)
    (assignedR : richSchedule .expressionReindex
      ((Closure.close (pending.owner.node.typeFormation.node.dependencyOrigin ordered)
        (pending.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (domain.dependencyOrigin headerOrdered) (tail.frame.dependencyEnvironment headerOrdered)).cost) <
      richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost →
      ∀ {n : Nat} {support : Profile n} {footprint : Footprint},
        RichCert sourceEnv env U registry target pending.owner.node.typeFormation.node
          pending.ownerLocals pending.ownerLeft true support footprint →
        footprint.Available pending.ownerAvailable →
        ∃ reply : CappedGeneratedQueryReply base commonCaps
          (graph.parameterCellDisplay domain domainProvenance) commonLeft commonRight support,
          environmentCost (reply.reply.realization.frame.dependencyEnvironment headerOrdered) ≤
            environmentCost (tail.frame.dependencyEnvironment headerOrdered)) :
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
  obtain ⟨prior, priorBound⟩ := assignedR
    (richSchedule_strict (pending.group_activation_bound ordered headerOrdered tail.frame entries
      (variableNode.dependencyOrigin headerOrdered)) _ _) value.certificate value.resources
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.reply.query.code henv value.certificate.formed
  have pendingLeft := pendingCapped.generated.realizations.1
  have realizedEqual : pending.owner.assigned.subst pending.ownerLeft = A.subst (raw.comp commonLeft) := by
    rw [pendingLeft]
    simpa only [subst_subst] using congrArg (fun e => e.subst commonLeft) sourceEqual
  let chosen := pending.reheader prior.reply.locals (raw.comp commonLeft) prior.reply.available
  let entry := chosen.completeReconstructed value certificate resources realizedEqual
  let selected : RichGroupedCapture (field := field) (major := major) domain env registry target
      prior.reply.locals (raw.comp commonLeft) prior.reply.available ownerInitial rawCapture
      (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight) := [entry]
  let frame := prior.reply.realization.frame.group domain ordered ownerInitial selected
  have capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) frame.raw :=
    .groupOfValues prior.capped domain ownerCapped nominalGraph nominal nominalProvenance displayed
      ordered ownerInitial chosen extension selected (by intro e member; cases List.mem_singleton.mp member; exact ⟨extension⟩) rfl rfl
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  rw [pending.left_eq, pending.right_eq, realizedEqual] at rawPair
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (rawCapture.subst ownerLeft))
      ((raw.comp commonRight).cons (rawCapture.subst ownerRight)) (A :: headerSource) :=
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
