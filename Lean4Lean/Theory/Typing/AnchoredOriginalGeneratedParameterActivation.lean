import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterCells
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedGroupActivation

/-! A computed parameter-cell answer becomes a real declared capture
slot. The whole original owner query and frame are retained independently
of subsequent selection of the slot's individual atoms. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Only the answer's selected prior valuation is used. Its raw path casts
the original paired owner typing even when the two source domains differ. -/
theorem PendingRichCapture.activateParameterReply
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
    (domainProvenance : EndpointProvenance context (.ref domain))
    {ownerLocals : List Nat} {ownerLeft ownerRight : Subst} {ownerAvailable : Valuation}
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
    (value : RichComputationalValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (alignment : BoundedParameterReply base commonCaps (pending.owner.assigned.subst pending.ownerLeft)
      (graph.parameterCellDisplay domain domainProvenance) commonLeft commonRight value.support
      (environmentCost (tail.frame.dependencyEnvironment headerOrdered)))
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode) :
    ∃ entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
        alignment.reply.answer.reply.locals (raw.comp commonLeft) alignment.reply.answer.reply.available
        ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight),
    ∃ reply : BoundedGeneratedQueryReply base commonCaps
        (groupCaptureVariableDisplay graph domain nominalGraph nominal nominalProvenance
          variableNode variableProvenance) commonLeft commonRight pending.input
        (environmentCost ((tail.frame.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)),
      entry.owner = pending.owner ∧ HEq entry.frame pending.frame ∧ HEq entry.query pending.query ∧
      ∀ hf : headerEnv.Ordered, reply.answer.reply.realization.frame.dependencyEnvironment hf =
        (alignment.reply.answer.reply.realization.frame.group domain ordered ownerInitial [entry]).dependencyEnvironment hf := by
  let prior := alignment.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.query.code henv value.certificate.formed
  let chosen := pending.reheader prior.locals (raw.comp commonLeft) prior.available
  have related : TypeRelated env U registry target (pending.owner.assigned.subst pending.ownerLeft)
      (A.subst (raw.comp commonLeft)) value.support := by
    simpa only [subst_subst] using alignment.related
  have path : TypeConversion env U target (pending.owner.assigned.subst pending.ownerLeft)
      (A.subst (raw.comp commonLeft)) := by
    simpa only [subst_subst] using alignment.path
  let entry := chosen.complete {
    value := value.toRichBinderValue
    aligned := { footprint := footprint, certificate := certificate, resources := resources, related := related }
    path := path }
  let selected : RichGroupedCapture (field := field) (major := major) domain env registry target
      prior.locals (raw.comp commonLeft) prior.available ownerInitial rawCapture
      (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight) := [entry]
  let frame := prior.realization.frame.group domain ordered ownerInitial selected
  have capped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal nominalProvenance) frame.raw :=
    .groupOfValues alignment.reply.answer.capped domain ownerCapped nominalGraph nominal nominalProvenance displayed
      ordered ownerInitial chosen extension selected (by intro e member; cases List.mem_singleton.mp member; exact ⟨extension⟩) rfl rfl
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  rw [pending.left_eq, pending.right_eq] at rawPair
  have declaredPair := path.cast rawPair
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (rawCapture.subst ownerLeft))
      ((raw.comp commonRight).cons (rawCapture.subst ownerRight)) (A :: headerSource) :=
    Ctx.SubstEq.cons prior.realization.substitutions (domain.sound.defeq.mono headerBelow) declaredPair
  obtain ⟨realized, realizedCapped, same⟩ := capped.realize frame substitutions
  refine ⟨entry, ⟨⟨{
      locals := Locals.push prior.locals,
      available := prior.available.push selected.needs,
      realization := realized,
      generated := realizedCapped.generated,
      query := ?_,
      closed := ?_ }, realizedCapped⟩, ?_⟩, rfl, HEq.rfl, HEq.rfl, same⟩
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
  · change (prior.available.push (captureNeeds pending.input ++ [])).AtomClosed
    simpa only [captureNeeds, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      Valuation.push_atomized_closed prior.closed [⟨pending.rank, pending.input⟩]
  · intro orderedHeader
    rw [same, OriginalRichFrame.group_environment, OriginalRichFrame.group_environment]
    exact entries.environment_mono ordered orderedHeader selected _ _ (alignment.reply.bounded orderedHeader)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
