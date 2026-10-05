import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientPiCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientExtensionScope
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedHeadQueryAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCapture

/-! Pure retained-family capture assembly. The only semantic values are
actual lower-call answers; scalar route schedules play no role here. Earlier
parameter resources are retained by a concrete maximum-cost frame merge. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

/-- Keep every earlier parameter demand when the whole-Pi replay selects
another frame. The selected query itself is unchanged, and merging the
actual baseline does not enlarge the pre-call capacity. -/
theorem AmbientBoundedParameterReply.retainPrefix
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (whole : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity)
    (baseline : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (generated : AmbientCaptureGenerated base caps commonLeft commonRight display.graph
      baseline.realization.frame.raw)
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (baseline.realization.frame.dependencyEnvironment ordered) ≤ capacity) :
    ∃ output : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity,
      (∀ index need, need ∈ baseline.available index → need ∈ output.reply.answer.reply.available index) ∧
      (∀ index need, need ∈ whole.reply.answer.reply.available index → need ∈ output.reply.answer.reply.available index) ∧
      HEq output.reply.answer.reply.query.observation whole.reply.answer.reply.query.observation ∧
      output.reply.answer.reply.query.footprint = whole.reply.answer.reply.query.footprint := by
  rcases whole with ⟨⟨⟨⟨⟨locals, available, realization, sourceGenerated, query, closed⟩, capped⟩, bound⟩,
    related, path⟩, ambient⟩
  rcases baseline with ⟨oldLocals, oldAvailable, oldRealization, oldClosed⟩
  have sameLocals : oldLocals = locals := generated.capped.generated.locals_eq.trans sourceGenerated.locals_eq.symm
  cases sameLocals
  let merged := realization.frame.merge oldRealization.frame
  have included : ∀ index need, need ∈ available index → need ∈ (available.append oldAvailable) index :=
    fun _ _ member => List.mem_append_left _ member
  have oldIncluded : ∀ index need, need ∈ oldAvailable index → need ∈ (available.append oldAvailable) index :=
    fun _ _ member => List.mem_append_right _ member
  have combinedClosed : (available.append oldAvailable).AtomClosed := by
    intro i need member atom atomMember
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed i need member atom atomMember)
    · exact List.mem_append_right _ (oldClosed i need member atom atomMember)
  let output : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile capacity := {
    reply := {
      answer := {
        reply := ⟨locals, available.append oldAvailable, ⟨merged, realization.substitutions⟩,
          .merge sourceGenerated generated.capped.generated, query.availableMono included, combinedClosed⟩
        capped := .merge capped generated.capped }
      bounded := fun ordered => by
        change environmentCost ((realization.frame.merge oldRealization.frame).dependencyEnvironment ordered) ≤ capacity
        rw [OriginalRichFrame.merge_environmentCost]
        exact Nat.max_le.mpr ⟨bound ordered, bounded ordered⟩ }
    related := related
    path := path
    generation := .merge ambient generated }
  exact ⟨output, oldIncluded, included, HEq.rfl, rfl⟩

/-- Reconstruct the operative history group from a concrete row at the
same selected whole-Pi reply. Obtaining this row belongs to actual header
child F; the finite assembly itself assumes no numerical recursion budget. -/
theorem AmbientBoundedParameterReply.captureArgumentHistoryReplyOfRow
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
    (row : RichPiRowCertificate env U registry target whole.reply.answer.reply.locals
      (raw.comp commonLeft) whole.reply.answer.reply.available true (.ref domain) body key output)
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
        reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
        reply.reply.locals = Locals.push whole.reply.answer.reply.locals ∧
        (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
          ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
            (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
              (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
        Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) := by
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
    capped := capped.capped }, capped, rfl, rfl, same, ⟨⟨extension, bound, adapter, inputPresent, owners, extensions⟩⟩⟩
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

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

/-- Actual later-family-prefix replay. The source argument is at the major's
own context (no intervening binder), as supplied by the family-spine lineage.
The queried input and its declared alignment are outputs, never premises. -/
theorem OriginalApplyPiHistory.replayApplicationPackedAssemble
    {n : Nat} {profile : Profile n}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.AmbientGenerated base commonCaps)
    (selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
    (selectedGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight sourceGraph selected.realization.frame.raw)
    (selectedBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      selected.locals (sourceRaw.comp commonLeft) selected.available true profile)
    (value : RichSupportedValue sourceEnv env U registry target argument selected.locals
      (sourceRaw.comp commonLeft) (sourceRaw.comp commonRight) selected.available packed.request.key.input)
    (supportEq : value.support = packed.request.support)
    (whole : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE A B).subst (sourceRaw.comp commonLeft)) (headerSide).display
      commonLeft commonRight
      (Profile.pi (A.subst (sourceRaw.comp commonLeft)) (B.subst (sourceRaw.comp commonLeft).lift)
        packed.request.support [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)])
      (environmentCost history.final))
    (row : RichPiRowCertificate env U registry target whole.reply.answer.reply.locals
      (headerRaw.comp commonLeft) whole.reply.answer.reply.available true (.ref headerDomain) headerBody
      packed.request.key (raiseProfile packed.request.rank packed.request.bound profile)) :
    ∃ answer : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile,
      answer.selected = selected ∧ HEq answer.packed packed ∧
      HEq answer.whole whole.toBoundedParameterReply ∧
      (∀ index need, need ∈ whole.reply.answer.reply.available index →
        need ∈ answer.reply.reply.available (index+1)) := by
  let seed : PendingRichCapture (field := field) (major := major) headerDomain env registry target
      history.headerFrame.locals (headerRaw.comp commonLeft) history.headerFrame.available ownerInitial
      a packed.request.key.anchor (a.subst (sourceRaw.comp commonRight)) := {
    owner := .inr ⟨source, a, A, argument, .appArgument location⟩
    ownerLocals := selected.locals
    ownerLeft := sourceRaw.comp commonLeft
    ownerRight := sourceRaw.comp commonRight
    ownerAvailable := selected.available
    ownerClosed := selected.closed
    initialContext := initial
    frame := selected.realization.frame
    substitutions := selected.realization.substitutions
    frame_environment_le := fun ordered => Nat.le_trans (selectedBound ordered) (sourceBound ordered)
    depth := 0
    sourcePrefix := []
    source_eq := rfl
    depth_eq := rfl
    expression_eq := by simp [HeaderOwner.expression]
    left_eq := packed.request.anchor_eq.symm
    right_eq := rfl
    rank := packed.argumentQuery.rank
    input := packed.argumentQuery.raw
    footprint := packed.argumentQuery.footprint
    query := packed.argumentQuery.observation
    queryAvailable := packed.argumentQuery.resources }
  let pendingAt := seed.reheader whole.reply.answer.reply.locals (headerRaw.comp commonLeft) whole.reply.answer.reply.available
  have headerEq : history.rightDomain = headerDomain :=
    (EndpointState.ref.inj history.rightDomainEq).symm
  dsimp only [originalNativePiRouteSide, originalApplicationTypeRouteSide] at headerEq
  let emptyQuery : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (sourceRaw.comp commonLeft) ([] : Profile 0) [] := .legacy (.legacy .empty)
  have emptyResources : Footprint.Available [] history.sourceFrame.available := fun _ _ member => nomatch member
  let originalSeed := history.argumentSeed (field := field) initial domain body function argument result hu hv
    location sourceGraph noBinders sourceBound emptyQuery emptyResources
  let retainedSeed : PendingRichCapture (field := field) (major := major) history.rightDomain env registry target
      history.headerFrame.locals (headerRaw.comp commonLeft) history.headerFrame.available ownerInitial
      a packed.request.key.anchor (a.subst (sourceRaw.comp commonRight)) :=
    { originalSeed with left_eq := packed.request.anchor_eq.symm }
  let seedScope : CappedOwnerScope common sourceRaw commonLeft commonRight commonCaps retainedSeed.depth
      (retainedSeed.owner.context retainedSeed.initialContext) := {
    toOriginalOwnerScope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv
      location sourceGraph noBinders sourceBound emptyQuery emptyResources
    caps := commonCaps
    capsTail := rfl }
  let headerProvenance := history.headerDomainProvenance initial domain body function argument result hu hv location sourceGraph
  obtain ⟨seedHistory, seedGenerated, seedReserve⟩ := history.argumentSeedHistoryAmbient (field := field)
    initial domain body function argument result hu hv location sourceGraph noBinders sourceBound emptyQuery emptyResources
    generated.source generated.header generated.whole
  let retainedHistory : OriginalSeedTypeHistory retainedSeed seedScope.toOriginalOwnerScope
      headerGraph headerProvenance history.headerFrame.realization history.leftOrdered history.rightOrdered :=
    ⟨seedHistory.route⟩
  have captured :
      ∃ entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
          whole.reply.answer.reply.locals (headerRaw.comp commonLeft) whole.reply.answer.reply.available
          ownerInitial a packed.request.key.anchor (a.subst (sourceRaw.comp commonRight)),
        ∃ reply : CappedGeneratedQueryReply base commonCaps
            (capturedPiBodyDisplay headerInitial headerLocation headerGraph sourceGraph argument
              (.ofLocation (.appArgument location) initial)) commonLeft commonRight
            (raiseProfile packed.request.rank packed.request.bound profile),
          AmbientCaptureGenerated base commonCaps commonLeft commonRight
            (capturedPiBodyDisplay headerInitial headerLocation headerGraph sourceGraph argument
              (.ofLocation (.appArgument location) initial)).graph reply.reply.realization.frame.raw ∧
          reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
          (∀ ordered : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment ordered =
            ((whole.reply.answer.reply.realization.frame.group headerDomain history.leftOrdered ownerInitial entries).reserve
              (groupCaptureHistoryReserve field major headerDomain history.leftOrdered history.rightOrdered ownerInitial
                history.final history.argumentSeedReserve)).dependencyEnvironment ordered) ∧
          Nonempty (GeneratedArgumentCaptureTrace selected.realization.frame pendingAt packed.request.key.input entries) := by
    cases history with
    | mk leftOrdered rightOrdered leftBelow chosen chosenEq sourceFrame headerFrame originalWhole =>
      have chosenEq' : headerDomain = chosen := EndpointState.ref.inj chosenEq
      subst chosen
      obtain ⟨entries, reply, replyGenerated, availableEq, _localsEq, environment, trace⟩ := whole.captureArgumentHistoryReplyOfRow headerInitial headerLocation headerGraph
        henv hscoped leftOrdered rightOrdered leftBelow headerBelow formed packed.request.certificate.formed
        row selected.realization.frame selectedGenerated sourceGraph argument
        (.ofLocation (.appArgument location) initial) rfl pendingAt
        (by simpa only [pendingAt, seed, PendingRichCapture.reheader] using
          (OriginalFrameExtension.refl (base := selected.realization.frame.raw)))
        packed.argumentQuery.bound packed.argumentQuery.adapter value supportEq rfl
        retainedSeed seedScope generated.source headerProvenance headerFrame.realization
        retainedHistory seedGenerated.wellFormed seedGenerated.frames
        selectedGenerated.ambient.1 generated.header.ambient.2 seedGenerated.ambient rfl
      refine ⟨entries, reply, replyGenerated, availableEq, ?_, trace⟩
      intro ordered
      simpa only [retainedHistory, seedReserve, OriginalApplyPiHistory.final] using environment ordered
  obtain ⟨entries, reply, replyGenerated, availableEq, environment, ⟨captureTrace⟩⟩ := captured
  let lowered := reply.reply.query.adaptRequest henv hscoped formed packed.request.bound (by exact .refl _)
  let finalReply : CappedGeneratedQueryReply base commonCaps
      (capturedPiBodyDisplay headerInitial headerLocation headerGraph sourceGraph argument
        (.ofLocation (.appArgument location) initial)) commonLeft commonRight profile :=
    ⟨{ reply.reply with query := lowered }, reply.capped⟩
  have destinationEq : history.destination = capturedPiBodyDisplay headerInitial headerLocation headerGraph
      sourceGraph argument (.ofLocation (.appArgument location) initial) := by
    cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      rfl
  have semantics := history.resultSemantics henv hscoped formed packed.request whole.toBoundedParameterReply
  refine ⟨{
    selected := selected
    selectedGenerated := selectedGenerated.capped
    selectedBound := selectedBound
    packed := packed
    whole := whole.toBoundedParameterReply
    seed := retainedSeed
    sourceGenerated := generated.source.capped
    seedScope := seedScope
    seedGenerated := generated.source.capped
    headerProvenance := headerProvenance
    seedHistory := retainedHistory
    seedHistoryGenerated := seedGenerated.generated
    seedHistoryReserve := seedReserve
    pending := ?_
    pendingOwner := ?_
    entries := ?_
    captureTrace := ?_
    reply := ?_
    environment_eq := ?_
    related := semantics.2
    path := semantics.1
    selectedGeneration := selectedGenerated
    sourceGeneration := generated.source
    wholeGeneration := whole.generation
    seedGeneration := generated.source
    historyGeneration := seedGenerated
    generation := ?_ }, rfl, HEq.rfl, HEq.rfl, ?_⟩
  · exact headerEq.symm ▸ pendingAt
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      rfl
  · exact headerEq.symm ▸ entries
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact captureTrace
  · exact destinationEq.symm ▸ finalReply
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      simpa only [finalReply, originalNativePiRouteSide, originalApplicationTypeRouteSide] using environment
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact replyGenerated

  · intro index need present
    cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame originalWhole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      change need ∈ reply.reply.available (index+1)
      rw [availableEq]
      exact present

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
