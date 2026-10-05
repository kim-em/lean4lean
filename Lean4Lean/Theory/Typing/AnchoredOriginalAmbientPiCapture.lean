import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplicationRow
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientExtensionScope
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedHeadQueryAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCapture

/-! Reconstruct the actual captured body reply with hereditary generation.
The original seed, finite history, and every selected owner remain attached
 to the same returned frame, including when no current needs are present. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

theorem AmbientBoundedParameterReply.captureArgumentHistoryReply
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (whole : AmbientBoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi sourceA sourceB support [(key, output)]).HasType (.sort true))
    (domainF : OriginalAmbientCodeInductionAt env registry headerOrdered initial (.piDomain location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    (bodyF : OriginalAmbientCodeInductionAt env registry headerOrdered initial (.piBody location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
      ownerInitial rawCapture key.anchor rightValue)
    (extension : OriginalFrameExtension ownerFrame.raw pending.frame.raw)
    (bound : n ≤ pending.rank)
    (adapter : GeneralNormalProfileAdapter env U registry target pending.input (raiseProfile pending.rank bound key.input))
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable key.input)
    (sameSupport : value.support = support)
    (sameDomain : pending.owner.assigned.subst pending.ownerLeft = sourceA)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture key.anchor rightValue)
    (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedGenerated : AmbientCaptureGenerated base seedScope.caps seedScope.left seedScope.right
      seedScope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance (location.contextDerivation initial) (.ref domain))
    (originalPrior : OriginalCaptureRealization graph env registry target
      originalLocals commonLeft commonRight originalAvailable)
    (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance
      originalPrior ordered headerOrdered)
    (historyWellFormed : history.route.WellFormed)
    (historyGenerated : ∀ boxed ∈ history.route.frames,
      AmbientCaptureGenerated base seedScope.caps seedScope.left seedScope.right
        boxed.graph boxed.frame.realization.frame.raw)
    (nominalAmbient : nominalGraph.Ambient env)
    (priorAmbient : originalPrior.frame.Ambient)
    (routeAmbient : history.route.Ambient)
    (capacity_eq : capacity = environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered)) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance)
          commonLeft commonRight output,
        AmbientCaptureGenerated base commonCaps commonLeft commonRight
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance).graph
          reply.reply.realization.frame.raw ∧
        (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
          ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
            (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
              (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
        Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) := by
  obtain ⟨row⟩ := whole.nativePiRow initial location graph henv hscoped headerOrdered headerBelow
    formed sorted domainF bodyF
  obtain ⟨alignment⟩ := whole.toBoundedParameterReply.argumentAlignment initial location graph
    henv hscoped formed sorted pending.owner value sameSupport sameDomain
  obtain ⟨entries, _bareGenerated, ⟨certificate⟩, resources, closed, inputPresent, owners, extensions⟩ :=
    row.captureAdaptedCapped whole.reply.answer.reply.realization whole.reply.answer.capped domain
      ownerFrame ownerGenerated.capped nominalGraph nominal provenance displayed henv formed ordered
      pending extension bound adapter alignment whole.reply.answer.reply.closed
  let prior := whole.reply.answer.reply
  let reserve := groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
    (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve
  let next := (prior.realization.frame.group domain ordered ownerInitial entries).reserve reserve
  have scopeExists : ∀ entry ∈ entries,
      ∃ scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
          (entry.owner.context entry.initialContext),
        AmbientCaptureGenerated base scope.caps scope.left scope.right scope.graph entry.frame.raw := by
    intro entry member
    obtain ⟨extension⟩ := extensions entry member
    obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextCaps, nextGraph, capped,
      rawEq, insertion, leftTail, rightTail, capsTail⟩ := extension.generateAmbientScope ownerGenerated
    have depthEq := (entry.extensionRealizations extension).1
    rw [depthEq] at rawEq insertion leftTail rightTail capsTail
    exact ⟨{
      scope := nextCommon, raw := nextRaw, left := nextLeft, right := nextRight,
      graph := nextGraph, insertion := insertion, raw_eq := rawEq,
      leftTail := leftTail, rightTail := rightTail, caps := nextCaps, capsTail := capsTail }, capped⟩
  let scopes := fun entry member => Classical.choose (scopeExists entry member)
  have generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance) next.raw :=
    .historyGroup whole.generation domain ownerGraph nominalGraph nominal provenance displayed
      ordered headerOrdered ownerInitial seed seedScope seedGenerated domainProvenance originalPrior history
      historyWellFormed historyGenerated (Nat.le_trans (whole.reply.bounded headerOrdered) (Nat.le_of_eq capacity_eq))
      entries scopes (fun entry member => Classical.choose_spec (scopeExists entry member))
      ownerGenerated.ambient.1 nominalAmbient priorAmbient routeAmbient
  have wholeRelated : TypeRelated env U registry target (.forallE sourceA sourceB)
      (.forallE (A.subst (raw.comp commonLeft)) (B.subst (raw.comp commonLeft).lift))
      (Profile.pi sourceA sourceB support [(key, output)]) := by
    simpa only [OriginalNestedDisplay.ofOccurrence, subst_subst, subst, ← Subst.comp_lift] using whole.related
  have path := TypeRelated.literalPiDomainPath henv formed wholeRelated
  rw [← sameDomain] at path
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  have declaredPair := path.cast rawPair
  rw [pending.left_eq, pending.right_eq] at declaredPair
  have substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons key.anchor)
      ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    .cons prior.realization.substitutions (domain.sound.defeq.mono headerBelow) declaredPair
  obtain ⟨realized, capped, same⟩ := generated.realize next substitutions
  refine ⟨entries, {
    reply := {
      locals := Locals.push prior.locals
      available := prior.available.push entries.needs
      realization := realized
      generated := capped.capped.generated
      query := ?_
      closed := closed }
    capped := capped.capped }, capped, same, ⟨⟨extension, bound, adapter, inputPresent, owners, extensions⟩⟩⟩
  refine {
    rank := n
    bound := Nat.le_refl _
    raw := output
    footprint := row.bodyFootprint
    observation := ?_
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := Profile.HasType.sortable_live certificate.formed }
  change RichObs headerEnv env U registry target body (Locals.push prior.locals)
    ((raw.cons (argument.subst nominalRaw)).comp commonLeft) output row.bodyFootprint
  rw [← generated.capped.generated.realizations.1]
  exact .code certificate

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
