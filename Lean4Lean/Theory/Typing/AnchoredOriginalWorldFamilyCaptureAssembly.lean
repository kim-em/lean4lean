import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyOwnerCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCaptureData
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryWorlds
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryHereditary
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! The actual selected Pi row builds one history-bearing reply together
with its world generation and controlled payloads. All finite entries are
constructed from the same pending argument and selected domain certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem realizeWorld
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.raw controls)
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ result : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available,
      ∃ next : WorldGenerated strata P base caps commonLeft commonRight graph result.frame.raw controls,
        next.worlds = generated.worlds ∧ Nonempty (next.Controlled frontier) ∧
        next.UsesControlPrefix controls.cutoff controls.fuel ∧
        (∀ ordered : sourceEnv.Ordered, result.frame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered) ∧
        (next.Replayable ↔ generated.Replayable) ∧ HEq next.environment generated.environment ∧
        Nonempty (next.Hereditary frontier) := by
  obtain ⟨left, right⟩ := generated.erase.ambientGenerated.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, rfl, ⟨ready⟩, compatible, (fun _ => rfl), Iff.rfl, HEq.rfl, ⟨hereditary⟩⟩

private theorem controlledBodyObservation
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (same : σ = τ) :
    ∃ query : RichObs sourceEnv env U registry target node locals τ profile footprint,
      Nonempty (ControlledStoredQuery controls frontier (.observation query)) := by
  cases same
  refine ⟨.code certificate, ⟨⟨.code ready.annotation, ?_, ready.sponsored⟩⟩⟩
  simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using ready.within

private theorem transportDomain
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {first second : Profile n} (same : first = second)
    (code : RichDomainCertificate env U registry target domain locals σ available first)
    (ready : ControlledStoredQuery controls frontier (.certificate code.certificate)) :
    ∃ output : RichDomainCertificate env U registry target domain locals σ available second,
      Nonempty (ControlledStoredQuery controls frontier (.certificate output.certificate)) := by
  cases same
  exact ⟨code, ⟨ready⟩⟩

/-- Internal row assembly after exact controlled domain extraction. The
semantic alignment is computed here from the SAME whole-Pi answer. -/
theorem AmbientBoundedParameterReply.captureHistoryWorldFromDomain
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata headerEnv)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (whole : AmbientBoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (tailWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph
      whole.reply.answer.reply.realization.frame.raw controls)
    (tailReplayable : tailWorld.Replayable)
    (tailReady : tailWorld.Controlled frontier)
    (tailHereditary : tailWorld.Hereditary frontier)
    (tailCompatible : tailWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target whole.reply.answer.reply.locals
      (raw.comp commonLeft) whole.reply.answer.reply.available true (.ref domain) body key output)
    (rowReady : ControlledStoredQuery controls frontier (.certificate row.body))
    (domainCode : RichDomainCertificate env U registry target (.ref domain)
      whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available support)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domainCode.certificate))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerWorld : WorldGenerated strata P base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw ownerControls)
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
    (pendingScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (pendingWorld : WorldGenerated strata P base pendingScope.caps pendingScope.left pendingScope.right
      pendingScope.graph pending.frame.raw ownerControls)
    (pendingReplayable : pendingWorld.Replayable)
    (pendingReady : pendingWorld.Controlled frontier)
    (pendingHereditary : pendingWorld.Hereditary frontier)
    (pendingCompatible : pendingWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (queryReady : ControlledStoredQuery controls frontier (.observation pending.query))
    (bound : n ≤ pending.rank)
    (adapter : GeneralNormalProfileAdapter env U registry target pending.input (raiseProfile pending.rank bound key.input))
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable key.input)
    (valueReady : ControlledStoredQuery controls frontier (.certificate value.certificate))
    (sameSupport : value.support = support)
    (sameDomain : pending.owner.assigned.subst pending.ownerLeft = sourceA)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture key.anchor rightValue)
    (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedControls : OriginalWorldControls strata sourceEnv)
    (seedWorld : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
      seedScope.graph seed.frame.raw seedControls)
    (seedReplayable : seedWorld.Replayable)
    (seedReady : seedWorld.Controlled frontier)
    (seedHereditary : seedWorld.Hereditary frontier)
    (seedCompatible : seedWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (seedQueryReady : ControlledStoredQuery controls frontier (.observation seed.query))
    (seedSame : seedControls.HasPrefix controls.cutoff controls.fuel)
    (domainProvenance : EndpointProvenance (location.contextDerivation initial) (.ref domain))
    (originalPrior : OriginalCaptureRealization graph env registry target
      originalLocals commonLeft commonRight originalAvailable)
    (priorWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph originalPrior.frame.raw controls)
    (priorReplayable : priorWorld.Replayable)
    (priorReady : priorWorld.Controlled frontier)
    (priorHereditary : priorWorld.Hereditary frontier)
    (priorCompatible : priorWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance
      originalPrior ordered headerOrdered)
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ordered) ×
      WorldEnvironmentProvenance strata U (originalPrior.frame.dependencyEnvironment headerOrdered))
    (baselineCoverage : Covered (@EquationControlMeasure.Less strata.rules.length) seedWorld.worlds baselines.1.worlds ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) priorWorld.worlds baselines.2.worlds)
    (tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) tailWorld.worlds baselines.2.worlds)
    (seedArgument : seed.owner.Argument)
    (seedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      baselines.1.worlds (seed.owner.worldEnvironment seedControls initialProvenance).worlds)
    (pendingCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      pendingWorld.worlds (pending.owner.worldEnvironment ownerControls initialProvenance).worlds)
    (routeInputs : history.route.WorldInputs strata)
    (historyWellFormed : history.route.WellFormed)
    (historyControls : ∀ i : Fin history.route.frames.length,
      OriginalWorldControls strata (history.route.frames[i]).sourceEnv)
    (historyWorld : ∀ i : Fin history.route.frames.length,
      WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
        (history.route.frames[i]).graph (history.route.frames[i]).frame.realization.frame.raw (historyControls i))
    (routeReplayable : ∀ i, (historyWorld i).Replayable)
    (boundary : history.route.WorldBoundary routeInputs seedControls controls
      baselines.1 baselines.2)
    (coherent : boundary.FrameOccurrenceCoherent historyControls historyWorld)
    (routeReady : ∀ i, (historyWorld i).Controlled frontier)
    (routeHereditary : ∀ i, (historyWorld i).Hereditary frontier)
    (routeCompatible : ∀ i, (historyWorld i).UsesControlPrefix controls.cutoff controls.fuel)
    (routeSame : ∀ i, (historyControls i).HasPrefix controls.cutoff controls.fuel)
    (ownerSame : ownerControls.HasPrefix controls.cutoff controls.fuel)
    (nominalAmbient : nominalGraph.Ambient env)
    (nominalSources : nominalGraph.AllSources P)
    (routeAmbient : history.route.Ambient)
    (routeSources : history.route.AllSources P)
    (capacity_eq : capacity = environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered)) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance)
          commonLeft commonRight output,
        ∃ generation : WorldGenerated strata P base commonCaps commonLeft commonRight
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance).graph
          reply.reply.realization.frame.raw controls,
          generation.Replayable ∧
          Nonempty (generation.Controlled frontier) ∧
          generation.UsesControlPrefix controls.cutoff controls.fuel ∧
          Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
          reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
          reply.reply.locals = Locals.push whole.reply.answer.reply.locals ∧
          (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
            ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
              (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
                (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
          generation.worlds =
            ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
              baselines.2 (history.route.worldReserve routeInputs)).append
              (WorldEnvironmentProvenance.group ownerControls controls initialProvenance tailWorld.environment entries)).worlds ∧
          Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) ∧
          (∀ selected ∈ entries, selected.answer.value.support.sortFlags = support.sortFlags) ∧
          (∀ selected ∈ entries, Nonempty (ControlledStoredQuery controls frontier
            (.certificate selected.answer.aligned.certificate))) ∧
          Nonempty (generation.Hereditary frontier) := by
  have wholeRelated : TypeRelated env U registry target (.forallE sourceA sourceB)
      (.forallE (A.subst (raw.comp commonLeft)) (B.subst (raw.comp commonLeft).lift))
      (Profile.pi sourceA sourceB support [(key, output)]) := by
    simpa only [OriginalNestedDisplay.ofOccurrence, subst_subst, subst, ← Subst.comp_lift] using whole.related
  have related := TypeRelated.literalPiDomain henv hscoped formed wholeRelated
  have path := TypeRelated.literalPiDomainPath henv formed wholeRelated
  rw [← sameDomain] at related path
  obtain ⟨alignedCode, ⟨alignedReady⟩⟩ := transportDomain sameSupport.symm domainCode domainReady
  have alignedRelated : TypeRelated env U registry target (pending.owner.assigned.subst pending.ownerLeft)
      (A.subst (raw.comp commonLeft)) value.support := sameSupport.symm ▸ related
  let alignment : HeaderValueAlignment pending.owner domain env registry target pending.ownerLocals
      whole.reply.answer.reply.locals pending.ownerLeft pending.ownerRight (raw.comp commonLeft)
      pending.ownerAvailable whole.reply.answer.reply.available key.input := {
    value := value.toRichBinderValue
    aligned := ⟨alignedCode.footprint, alignedCode.certificate, alignedCode.resources, alignedRelated⟩
    path := path }
  let entry := pending.completeAdapted key.input bound adapter alignment
  let packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight commonCaps
      controls ownerControls frontier entry :=
    ⟨pendingScope, pendingWorld, pendingReplayable, pendingReady, pendingCompatible, queryReady, valueReady, alignedReady, pendingHereditary⟩
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
  obtain ⟨entries, coverage, owners, extensions, coveredPackets⟩ :=
    packet.coverNeedsOwnerCovered henv formed initialProvenance pendingCovered extension needs bounded covered
  let selected := fun entry member => Classical.choose (coveredPackets entry member)
  have selectedCovered := fun entry member => (Classical.choose_spec (coveredPackets entry member)).2.1
  have packets := fun entry member => Nonempty.intro (selected entry member)
  let scopes := fun entry member => (selected entry member).scope
  let ownerWorlds := fun entry member => (selected entry member).generation
  have collect : ∀ (list : RichGroupedCapture (field := field) (major := major) domain env registry target
      whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
      ownerInitial rawCapture key.anchor rightValue),
      (∀ entry ∈ list, Nonempty (WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight commonCaps
        controls ownerControls frontier entry)) →
      ∀ query ∈ (richGroupedEntriesRaw list).storedQueries,
        Nonempty (ControlledStoredQuery controls frontier query) := by
    intro list
    induction list with
    | nil =>
      intro _ query member
      simp only [richGroupedEntriesRaw, RawRichGroupEntries.storedQueries] at member
      cases member
    | cons entry rest ih =>
      intro packets query member
      simp only [richGroupedEntriesRaw, RawRichGroupEntries.storedQueries] at member
      rcases List.mem_append.mp member with member | member
      · exact (Classical.choice (packets entry List.mem_cons_self)).storedReady ownerSame query member
      · exact ih (fun e hm => packets e (List.mem_cons_of_mem _ hm)) query member
  have entryReady := collect entries packets
  let prior := whole.reply.answer.reply
  let reserve := groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
    (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve
  let next := (prior.realization.frame.group domain ordered ownerInitial entries).reserve reserve
  have tailBound : environmentCost (prior.realization.frame.dependencyEnvironment headerOrdered) ≤
      environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered) :=
    Nat.le_trans (whole.reply.bounded headerOrdered) (Nat.le_of_eq capacity_eq)
  let generated : WorldGenerated strata P base commonCaps commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance) next.raw controls :=
    .historyGroup tailWorld domain ownerGraph nominalGraph nominal provenance displayed ordered headerOrdered ownerInitial
      seed seedScope seedControls seedWorld domainProvenance originalPrior history priorWorld initialProvenance baselines routeInputs
      historyWellFormed historyControls historyWorld tailBound entries scopes ownerControls ownerWorlds
      ownerWorld.erase.ambientGenerated.ambient.1 nominalAmbient priorWorld.erase.ambientGenerated.ambient.2 routeAmbient
      ownerWorld.erase.sources.1 nominalSources priorWorld.erase.sources.2 routeSources
  obtain ⟨generatedReady⟩ := WorldGenerated.Controlled.historyGroup tailWorld domain ownerGraph nominalGraph nominal provenance displayed
    ordered headerOrdered ownerInitial seed seedScope seedControls seedWorld domainProvenance originalPrior history priorWorld
    initialProvenance baselines routeInputs historyWellFormed historyControls historyWorld tailBound entries scopes ownerControls ownerWorlds
    ownerWorld.erase.ambientGenerated.ambient.1 nominalAmbient priorWorld.erase.ambientGenerated.ambient.2 routeAmbient
    ownerWorld.erase.sources.1 nominalSources priorWorld.erase.sources.2 routeSources
    tailReady entryReady seedQueryReady seedReady seedSame priorReady routeReady routeSame
    (fun entry member => (selected entry member).ready) ownerSame
  let generatedHereditary : generated.Hereditary frontier := WorldGenerated.Hereditary.historyGroup tailWorld domain ownerGraph nominalGraph nominal provenance displayed
    ordered headerOrdered ownerInitial seed seedScope seedControls seedWorld domainProvenance originalPrior history priorWorld
    initialProvenance baselines routeInputs historyWellFormed historyControls historyWorld tailBound entries scopes ownerControls ownerWorlds
    ownerWorld.erase.ambientGenerated.ambient.1 nominalAmbient priorWorld.erase.ambientGenerated.ambient.2 routeAmbient
    ownerWorld.erase.sources.1 nominalSources priorWorld.erase.sources.2 routeSources
    tailHereditary seedHereditary seedSame priorHereditary routeHereditary routeSame
    (fun entry member => (selected entry member).hereditary) ownerSame
  have replayable : generated.Replayable :=
    ⟨tailReplayable, seedReplayable, priorReplayable, routeReplayable,
      (fun entry member => (selected entry member).replayable), selectedCovered, ⟨seedArgument, seedCovered⟩, baselineCoverage.1, baselineCoverage.2, ⟨boundary, coherent⟩, tailCovered⟩
  have compatible : generated.UsesControlPrefix controls.cutoff controls.fuel :=
    ⟨tailCompatible, seedCompatible, priorCompatible, routeCompatible,
      (fun entry member => (selected entry member).compatible), ownerSame⟩
  have rawPair := (pending.owner.node.sound.defeq.mono sourceBelow).substDF henv
    pending.substitutions.wf formed pending.substitutions
  have declaredPair := path.cast rawPair
  rw [pending.left_eq, pending.right_eq] at declaredPair
  have substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons key.anchor)
      ((raw.comp commonRight).cons rightValue) (A :: headerSource) :=
    .cons prior.realization.substitutions (domain.sound.defeq.mono headerBelow) declaredPair
  obtain ⟨realized, actualWorld, actualWorlds, ⟨actualReady⟩, actualCompatible, sameEnvironment, actualReplayable, _actualEnvironment, ⟨actualHereditary⟩⟩ :=
    realizeWorld next generated generatedReady compatible generatedHereditary substitutions
  obtain ⟨query, ⟨queryControlled⟩⟩ := controlledBodyObservation row.body rowReady
    generated.erase.ambientGenerated.capped.generated.realizations.1
  have resources : row.bodyFootprint.Available (prior.available.push entries.needs) := by
    intro index need member
    cases index with
    | zero => exact coverage need (List.mem_append_left _ (Footprint.mem_localNeeds.mpr member))
    | succ index => exact (row.pack.available row.outsideAvailable) (index+1) need member
  let reply : CappedGeneratedQueryReply base commonCaps
      (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance) commonLeft commonRight output := {
    reply := {
      locals := Locals.push prior.locals
      available := prior.available.push entries.needs
      realization := realized
      generated := actualWorld.erase.ambientGenerated.capped.generated
      query := {
        rank := n, bound := Nat.le_refl _, raw := output, footprint := row.bodyFootprint,
        observation := query, adapter := by rw [raiseProfile_self]; exact .refl _,
        resources := resources, live := Profile.HasType.sortable_live row.body.formed }
      closed := entries.closed prior.closed }
    capped := actualWorld.erase.ambientGenerated.capped }
  refine ⟨entries, reply, actualWorld, actualReplayable.mpr replayable, ⟨actualReady⟩, actualCompatible, ⟨queryControlled⟩, rfl, rfl,
    sameEnvironment, ?_, ⟨⟨extension, bound, adapter, ?_, owners, extensions⟩⟩, ?_, ?_, ⟨actualHereditary⟩⟩
  · rw [actualWorlds]
    exact WorldGenerated.historyGroup_worlds tailWorld domain ownerGraph nominalGraph nominal provenance displayed
      ordered headerOrdered ownerInitial seed seedScope seedControls seedWorld domainProvenance originalPrior history priorWorld
      initialProvenance baselines routeInputs historyWellFormed historyControls historyWorld tailBound entries scopes ownerControls ownerWorlds
      ownerWorld.erase.ambientGenerated.ambient.1 nominalAmbient priorWorld.erase.ambientGenerated.ambient.2 routeAmbient
      ownerWorld.erase.sources.1 nominalSources priorWorld.erase.sources.2 routeSources
  · exact coverage _ (List.mem_append_right _ (List.mem_singleton_self _))
  · intro selected member
    exact (Classical.choose_spec (coveredPackets selected member)).2.2.trans
      (congrArg Profile.sortFlags sameSupport)
  · exact fun entry member => ⟨(selected entry member).declaredReady⟩

/-- The selected whole-Pi observer computes the exact declared-domain
certificate internally. The caller supplies actual child answers and their
controls, never a completed owner/domain alignment or output generation. -/
theorem AmbientBoundedParameterReply.captureArgumentHistoryReplyOfRowWorld
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata headerEnv)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (whole : AmbientBoundedParameterReply base commonCaps (.forallE sourceA sourceB)
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi sourceA sourceB (support : Profile n) [(key, output)]) capacity)
    (tailWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph
      whole.reply.answer.reply.realization.frame.raw controls)
    (tailReplayable : tailWorld.Replayable)
    (tailReady : tailWorld.Controlled frontier)
    (tailHereditary : tailWorld.Hereditary frontier)
    (tailCompatible : tailWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target whole.reply.answer.reply.locals
      (raw.comp commonLeft) whole.reply.answer.reply.available true (.ref domain) body key output)
    (rowReady : ControlledStoredQuery controls frontier (.certificate row.body))
    (wholeQueryReady : ControlledStoredQuery controls frontier (.observation whole.reply.answer.reply.query.observation))
    (sorted : (Profile.pi sourceA sourceB support [(key, output)]).HasType (.sort true))
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerWorld : WorldGenerated strata P base commonCaps commonLeft commonRight ownerGraph ownerFrame.raw ownerControls)
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
    (pendingScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (pendingWorld : WorldGenerated strata P base pendingScope.caps pendingScope.left pendingScope.right
      pendingScope.graph pending.frame.raw ownerControls)
    (pendingReplayable : pendingWorld.Replayable)
    (pendingReady : pendingWorld.Controlled frontier)
    (pendingHereditary : pendingWorld.Hereditary frontier)
    (pendingCompatible : pendingWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (queryReady : ControlledStoredQuery controls frontier (.observation pending.query))
    (bound : n ≤ pending.rank)
    (adapter : GeneralNormalProfileAdapter env U registry target pending.input (raiseProfile pending.rank bound key.input))
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable key.input)
    (valueReady : ControlledStoredQuery controls frontier (.certificate value.certificate))
    (sameSupport : value.support = support)
    (sameDomain : pending.owner.assigned.subst pending.ownerLeft = sourceA)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial rawCapture key.anchor rightValue)
    (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedControls : OriginalWorldControls strata sourceEnv)
    (seedWorld : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
      seedScope.graph seed.frame.raw seedControls)
    (seedReplayable : seedWorld.Replayable)
    (seedReady : seedWorld.Controlled frontier)
    (seedHereditary : seedWorld.Hereditary frontier)
    (seedCompatible : seedWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (seedQueryReady : ControlledStoredQuery controls frontier (.observation seed.query))
    (seedSame : seedControls.HasPrefix controls.cutoff controls.fuel)
    (domainProvenance : EndpointProvenance (location.contextDerivation initial) (.ref domain))
    (originalPrior : OriginalCaptureRealization graph env registry target
      originalLocals commonLeft commonRight originalAvailable)
    (priorWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph originalPrior.frame.raw controls)
    (priorReplayable : priorWorld.Replayable)
    (priorReady : priorWorld.Controlled frontier)
    (priorHereditary : priorWorld.Hereditary frontier)
    (priorCompatible : priorWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance
      originalPrior ordered headerOrdered)
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ordered) ×
      WorldEnvironmentProvenance strata U (originalPrior.frame.dependencyEnvironment headerOrdered))
    (baselineCoverage : Covered (@EquationControlMeasure.Less strata.rules.length) seedWorld.worlds baselines.1.worlds ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) priorWorld.worlds baselines.2.worlds)
    (tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) tailWorld.worlds baselines.2.worlds)
    (seedArgument : seed.owner.Argument)
    (seedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      baselines.1.worlds (seed.owner.worldEnvironment seedControls initialProvenance).worlds)
    (pendingCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      pendingWorld.worlds (pending.owner.worldEnvironment ownerControls initialProvenance).worlds)
    (routeInputs : history.route.WorldInputs strata)
    (historyWellFormed : history.route.WellFormed)
    (historyControls : ∀ i : Fin history.route.frames.length,
      OriginalWorldControls strata (history.route.frames[i]).sourceEnv)
    (historyWorld : ∀ i : Fin history.route.frames.length,
      WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
        (history.route.frames[i]).graph (history.route.frames[i]).frame.realization.frame.raw (historyControls i))
    (routeReplayable : ∀ i, (historyWorld i).Replayable)
    (boundary : history.route.WorldBoundary routeInputs seedControls controls
      baselines.1 baselines.2)
    (coherent : boundary.FrameOccurrenceCoherent historyControls historyWorld)
    (routeReady : ∀ i, (historyWorld i).Controlled frontier)
    (routeHereditary : ∀ i, (historyWorld i).Hereditary frontier)
    (routeCompatible : ∀ i, (historyWorld i).UsesControlPrefix controls.cutoff controls.fuel)
    (routeSame : ∀ i, (historyControls i).HasPrefix controls.cutoff controls.fuel)
    (ownerSame : ownerControls.HasPrefix controls.cutoff controls.fuel)
    (nominalAmbient : nominalGraph.Ambient env)
    (nominalSources : nominalGraph.AllSources P)
    (routeAmbient : history.route.Ambient)
    (routeSources : history.route.AllSources P)
    (capacity_eq : capacity = environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered)) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial rawCapture key.anchor rightValue,
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance)
          commonLeft commonRight output,
        ∃ generation : WorldGenerated strata P base commonCaps commonLeft commonRight
          (capturedPiBodyDisplay initial location graph nominalGraph nominal provenance).graph
          reply.reply.realization.frame.raw controls,
          generation.Replayable ∧
          Nonempty (generation.Controlled frontier) ∧
          generation.UsesControlPrefix controls.cutoff controls.fuel ∧
          Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
          reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
          reply.reply.locals = Locals.push whole.reply.answer.reply.locals ∧
          (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
            ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
              (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
                (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
          generation.worlds =
            ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
              baselines.2 (history.route.worldReserve routeInputs)).append
              (WorldEnvironmentProvenance.group ownerControls controls initialProvenance tailWorld.environment entries)).worlds ∧
          Nonempty (GeneratedArgumentCaptureTrace ownerFrame pending key.input entries) ∧
          (∀ selected ∈ entries, selected.answer.value.support.sortFlags = support.sortFlags) ∧
          (∀ selected ∈ entries, Nonempty (ControlledStoredQuery controls frontier
            (.certificate selected.answer.aligned.certificate))) ∧
          Nonempty (generation.Hereditary frontier) := by
  obtain ⟨footprint, certificate, certificateReady, resources, _worlds⟩ :=
    whole.reply.answer.reply.query.code_controlled henv controls wholeQueryReady sorted
  obtain ⟨domainCode, domainReady, _domainWorlds, _domainDepth⟩ :=
    certificate.piDomain_controlled hu hv (.done _) resources certificateReady
  exact whole.captureHistoryWorldFromDomain initial location graph controls ownerControls frontier
    tailWorld tailReplayable tailReady tailHereditary tailCompatible henv hscoped ordered headerOrdered sourceBelow headerBelow formed
    row rowReady domainCode domainReady ownerFrame ownerWorld nominalGraph nominal provenance displayed
    pending extension pendingScope pendingWorld pendingReplayable pendingReady pendingHereditary pendingCompatible queryReady bound adapter
    value valueReady sameSupport sameDomain seed seedScope seedControls seedWorld seedReplayable seedReady seedHereditary seedCompatible
    seedQueryReady seedSame domainProvenance originalPrior priorWorld priorReplayable priorReady priorHereditary priorCompatible history
    initialProvenance baselines baselineCoverage tailCovered seedArgument seedCovered pendingCovered routeInputs historyWellFormed historyControls historyWorld routeReplayable boundary coherent routeReady routeHereditary routeCompatible
    routeSame ownerSame nominalAmbient nominalSources routeAmbient routeSources capacity_eq

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
