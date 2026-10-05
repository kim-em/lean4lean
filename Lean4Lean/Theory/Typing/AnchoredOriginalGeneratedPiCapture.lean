import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCaptureData
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationRow
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentValue
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedFamilyCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterActivation

/-! Adapted original argument queries enter the actual chosen header frame.
Their declared alignment is extracted from the same whole-Pi answer that
supplies the row; it is never an independent completed alignment premise. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
open private needCoverage_cast from Lean4Lean.Theory.Typing.AnchoredOriginalGenericFamilyDeclaredPrefix

/-- Domain extraction uses the exact requested support, including empty
support, at the SAME selected frame as the nonempty codomain row. -/
theorem BoundedParameterReply.argumentAlignment
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (answer : BoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) rows) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi sourceA sourceB support rows).HasType (.sort true))
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major)
    (value : RichSupportedValue sourceEnv env U registry target owner.node ownerLocals ownerLeft ownerRight ownerAvailable input)
    (sameSupport : value.support = support)
    (sameDomain : owner.assigned.subst ownerLeft = sourceA) :
    Nonempty (HeaderValueAlignment owner domain env registry target ownerLocals answer.reply.answer.reply.locals
      ownerLeft ownerRight (raw.comp commonLeft) ownerAvailable answer.reply.answer.reply.available input) := by
  obtain ⟨fp, ⟨certificate⟩, resources⟩ := answer.reply.answer.reply.query.code henv sorted
  obtain ⟨domainCode⟩ := certificate.piDomain hu hv (.done _) resources
  have whole : TypeRelated env U registry target (.forallE sourceA sourceB)
      (.forallE (A.subst (raw.comp commonLeft)) (B.subst (raw.comp commonLeft).lift))
      (Profile.pi sourceA sourceB support rows) := by
    simpa only [OriginalNestedDisplay.ofOccurrence, subst_subst, subst, ← Subst.comp_lift] using answer.related
  have related := TypeRelated.literalPiDomain henv hscoped formed whole
  have path := TypeRelated.literalPiDomainPath henv formed whole
  rw [← sameDomain] at related path
  cases sameSupport
  exact ⟨{
    value := value.toRichBinderValue
    aligned := { footprint := domainCode.footprint, certificate := domainCode.certificate,
                 resources := domainCode.resources, related := related }
    path := path }⟩

/-- Restrict an advertised input without changing the original raw observer.
The actual pending seed stays independent of which finite needs the row uses. -/
theorem RichPiRowCertificate.captureAdaptedCapped
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (tailCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.frame.raw)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      locals (raw.comp commonLeft) available ownerInitial rawCapture key.anchor rightValue)
    (extension : OriginalFrameExtension ownerFrame.raw pending.frame.raw)
    (bound : n ≤ pending.rank)
    (adapter : GeneralNormalProfileAdapter env U registry target pending.input (raiseProfile pending.rank bound key.input))
    (answer : HeaderValueAlignment pending.owner domain env registry target pending.ownerLocals locals
      pending.ownerLeft pending.ownerRight (raw.comp commonLeft) pending.ownerAvailable available key.input)
    (row : RichPiRowCertificate env U registry target locals (raw.comp commonLeft) available relevant
      (.ref domain) body (key : Key n) result)
    (closed : available.AtomClosed) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (raw.comp commonLeft) available ownerInitial rawCapture key.anchor rightValue,
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        ((tail.frame.group domain ordered ownerInitial entries).raw) ∧
      Nonempty (RichCert headerEnv env U registry target body (Locals.push locals)
        ((raw.comp commonLeft).cons key.anchor) relevant result row.bodyFootprint) ∧
      row.bodyFootprint.Available (available.push entries.needs) ∧
      (available.push entries.needs).AtomClosed ∧
      (⟨n, key.input⟩ : Need) ∈ entries.needs ∧
      (∀ selected ∈ entries, selected.owner = pending.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw selected.frame.raw)) := by
  let entry := pending.completeAdapted key.input bound adapter answer
  let needs := row.bodyFootprint.localNeeds ++ [Need.mk n key.input]
  have bounded : ∀ need ∈ needs, need.rank ≤ n := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · exact (row.pack.localNeeds need member).1
    · cases List.mem_singleton.mp member; exact Nat.le_refl _
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
    intro need member atom atomMember
    rcases List.mem_append.mp member with member | member
    · exact row.covered atom ((row.pack.localNeeds need member).2 atom atomMember)
    · cases List.mem_singleton.mp member
      simpa only [Need.atGrade, dif_pos (Nat.le_refl _), raiseProfile_self] using atomMember
  obtain ⟨entries, coverage, owners, extensions⟩ := entry.coverNeedsGenerated henv formed extension needs bounded covered
  have values := entry.extensionRealizations extension
  have bodyResources := row.pack.available row.outsideAvailable
  refine ⟨entries, ?_, ⟨row.body⟩, ?_, entries.closed closed,
    coverage _ (List.mem_append_right _ (List.mem_singleton_self _)), owners, extensions⟩
  · exact .groupOfValues tailCapped domain ownerCapped nominalGraph nominal provenance displayed
      ordered ownerInitial pending extension entries extensions values.2.2.2.1 values.2.2.2.2
  · intro index need member
    cases index with
    | zero => exact coverage need (List.mem_append_left _ (Footprint.mem_localNeeds.mpr member))
    | succ index => exact bodyResources (index + 1) need member


/-- Whole-history replay produces both the selected row and the declared
alignment in ONE chosen prior frame. The next captured frame and every local
need are constructed here; no completed row or alignment is a premise. -/
theorem BoundedParameterReply.captureArgument
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (whole : BoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi sourceA sourceB support [(key, output)]).HasType (.sort true))
    (domainF : OriginalCodeInductionAt env registry headerOrdered initial (.piDomain location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    (bodyF : OriginalCodeInductionAt env registry headerOrdered initial (.piBody location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
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
    (sameDomain : pending.owner.assigned.subst pending.ownerLeft = sourceA) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).raw) ∧
      ∃ footprint,
        Nonempty (RichCert headerEnv env U registry target body (Locals.push whole.reply.answer.reply.locals)
          ((raw.comp commonLeft).cons key.anchor) true output footprint) ∧
        footprint.Available (whole.reply.answer.reply.available.push entries.needs) ∧
        (whole.reply.answer.reply.available.push entries.needs).AtomClosed ∧
        (⟨n, key.input⟩ : Need) ∈ entries.needs ∧
        (∀ selected ∈ entries, selected.owner = pending.owner) ∧
        (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw selected.frame.raw)) := by
  obtain ⟨row⟩ := whole.nativePiRow initial location graph henv hscoped headerOrdered headerBelow formed sorted domainF bodyF
  obtain ⟨alignment⟩ := whole.argumentAlignment initial location graph henv hscoped formed sorted
    pending.owner value sameSupport sameDomain
  obtain ⟨entries, generated, certificate, resources, closed, inputPresent, owners, extensions⟩ :=
    row.captureAdaptedCapped whole.reply.answer.reply.realization whole.reply.answer.capped domain
      ownerFrame ownerCapped nominalGraph nominal provenance displayed henv formed ordered pending extension
      bound adapter alignment whole.reply.answer.reply.closed
  exact ⟨entries, generated, row.bodyFootprint, certificate, resources, closed, inputPresent, owners, extensions⟩


/-- The chosen row enters an actual paired source realization. Even when
its output profile is empty, the whole-Pi domain path types the raw captured
pair; no empty observation is used as a substitute for raw conversion. -/
theorem BoundedParameterReply.captureArgumentReply
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (whole : BoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi sourceA sourceB support [(key, output)]).HasType (.sort true))
    (domainF : OriginalCodeInductionAt env registry headerOrdered initial (.piDomain location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    (bodyF : OriginalCodeInductionAt env registry headerOrdered initial (.piBody location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
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
    (sameDomain : pending.owner.assigned.subst pending.ownerLeft = sourceA) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance)
          commonLeft commonRight output,
        (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
          (whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).dependencyEnvironment hf) ∧
        Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) := by
  obtain ⟨entries, generated, footprint, ⟨certificate⟩, resources, closed, inputPresent, owners, extensions⟩ :=
    whole.captureArgument initial location graph henv hscoped ordered headerOrdered headerBelow formed sorted
      domainF bodyF ownerFrame ownerCapped nominalGraph nominal provenance displayed pending extension bound adapter
      value sameSupport sameDomain
  let prior := whole.reply.answer.reply
  let next := prior.realization.frame.group domain ordered ownerInitial entries
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
      generated := capped.generated
      query := ?_
      closed := closed }
    capped := capped }, same, ⟨⟨extension, bound, adapter, inputPresent, owners, extensions⟩⟩⟩
  refine {
    rank := n
    bound := Nat.le_refl _
    raw := output
    footprint := footprint
    observation := ?_
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := Profile.HasType.sortable_live certificate.formed }
  change RichObs headerEnv env U registry target body (Locals.push prior.locals)
    ((raw.cons (argument.subst nominalRaw)).comp commonLeft) output footprint
  rw [← generated.generated.realizations.1]
  exact .code certificate


/-- The actual selected row enters an operative history-bearing group. Its
reserve retains both the original type route and the fixed original group
baseline, while the selected tail is paid by the whole-Pi reply's bound. -/
theorem BoundedParameterReply.captureArgumentHistoryReply
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (whole : BoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi sourceA sourceB support [(key, output)]).HasType (.sort true))
    (domainF : OriginalCodeInductionAt env registry headerOrdered initial (.piDomain location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    (bodyF : OriginalCodeInductionAt env registry headerOrdered initial (.piBody location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin headerOrdered).weight * (1 + capacity)))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw)
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
    (seedGenerated : CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right
      seedScope.graph seed.frame.raw)
    (domainProvenance : EndpointProvenance (location.contextDerivation initial) (.ref domain))
    (originalPrior : OriginalCaptureRealization graph env registry target
      originalLocals commonLeft commonRight originalAvailable)
    (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance
      originalPrior ordered headerOrdered)
    (historyWellFormed : history.route.WellFormed)
    (historyGenerated : ∀ boxed ∈ history.route.frames,
      CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right
        boxed.graph boxed.frame.realization.frame.raw)
    (capacity_eq : capacity = environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered)) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance)
          commonLeft commonRight output,
        (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
          ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
            (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
              (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
        Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) := by
  obtain ⟨entries, _bareGenerated, footprint, ⟨certificate⟩, resources, closed, inputPresent, owners, extensions⟩ :=
    whole.captureArgument initial location graph henv hscoped ordered headerOrdered headerBelow formed sorted
      domainF bodyF ownerFrame ownerCapped nominalGraph nominal provenance displayed pending extension bound adapter
      value sameSupport sameDomain
  let prior := whole.reply.answer.reply
  let reserve := groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
    (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve
  let next := (prior.realization.frame.group domain ordered ownerInitial entries).reserve reserve
  have scopeExists : ∀ entry ∈ entries,
      ∃ scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
          (entry.owner.context entry.initialContext),
        CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph entry.frame.raw := by
    intro entry member
    obtain ⟨extension⟩ := extensions entry member
    obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextCaps, nextGraph, capped,
      rawEq, insertion, leftTail, rightTail, capsTail⟩ := extension.generateCappedScope ownerCapped
    have depthEq := (entry.extensionRealizations extension).1
    rw [depthEq] at rawEq insertion leftTail rightTail capsTail
    exact ⟨{
      scope := nextCommon, raw := nextRaw, left := nextLeft, right := nextRight,
      graph := nextGraph, insertion := insertion, raw_eq := rawEq,
      leftTail := leftTail, rightTail := rightTail, caps := nextCaps, capsTail := capsTail }, capped⟩
  let scopes := fun entry member => Classical.choose (scopeExists entry member)
  have generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance) next.raw :=
    .historyGroup whole.reply.answer.capped domain ownerGraph nominalGraph nominal provenance displayed
      ordered headerOrdered ownerInitial seed seedScope seedGenerated domainProvenance originalPrior history
      historyWellFormed historyGenerated (Nat.le_trans (whole.reply.bounded headerOrdered) (Nat.le_of_eq capacity_eq))
      entries scopes (fun entry member => Classical.choose_spec (scopeExists entry member))
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
      generated := capped.generated
      query := ?_
      closed := closed }
    capped := capped }, same, ⟨⟨extension, bound, adapter, inputPresent, owners, extensions⟩⟩⟩
  refine {
    rank := n
    bound := Nat.le_refl _
    raw := output
    footprint := footprint
    observation := ?_
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := Profile.HasType.sortable_live certificate.formed }
  change RichObs headerEnv env U registry target body (Locals.push prior.locals)
    ((raw.cons (argument.subst nominalRaw)).comp commonLeft) output footprint
  rw [← generated.generated.realizations.1]
  exact .code certificate

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
