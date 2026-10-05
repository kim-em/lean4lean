import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiPackedAssembly
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldArgumentValue
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationRow
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedWorld
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayData

/-! Operative application replay from the computed packed request. Argument
F, argument formation R, incoming Pi F, selected row reanchoring, the fixed
original seed history, and its active capture are composed here. Only the
exact whole-history child is recursively interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private located_worlds_nil from Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

structure WorldApplyPiReplayResult
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType)
    (major : EndpointRef left.sourceEnv U left.source majorExpression majorType)
    (ownerInitial : List Closure)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (profile : Profile n)
    {strata : EquationStratification env} (P : VEnv → Prop)
    (sourceControls : OriginalWorldControls strata left.sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (frontier : List (World strata.rules.length))
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceWorld : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (priorWorld : WorldEnvironmentProvenance strata U history.final)
    (wholeInputs : history.whole.WorldInputs strata)
    extends AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile where
  world : WorldGenerated strata P base commonCaps commonLeft commonRight history.destination.graph
    reply.reply.realization.frame.raw headerControls
  replayable : world.Replayable
  controlled : world.Controlled frontier
  compatible : world.UsesControlPrefix headerControls.cutoff headerControls.fuel
  queryReady : ControlledStoredQuery headerControls frontier (.observation reply.reply.query.observation)
  wholeWorld : WorldGenerated strata P base commonCaps commonLeft commonRight right.graph
    whole.reply.answer.reply.realization.frame.raw headerControls
  wholeCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
    wholeWorld.worlds priorWorld.worlds
  seedData : seedHistory.route.ControlledWorldData P base seedScope.caps
    sourceControls.cutoff sourceControls.fuel frontier
  seedWorlds : (seedHistory.route.worldReserve seedData.inputs).worlds =
    (history.argumentSeedWorld sourceControls headerControls sourceWorld priorWorld wholeInputs).worlds
  worlds : world.worlds =
    ((WorldEnvironmentProvenance.groupHistory field major history.rightDomain sourceControls headerControls
      initialProvenance priorWorld (seedHistory.route.worldReserve seedData.inputs)).append
      (WorldEnvironmentProvenance.group sourceControls headerControls initialProvenance wholeWorld.environment entries)).worlds
  entrySupports : ∀ entry ∈ entries, entry.answer.value.support.sortFlags = packed.request.support.sortFlags
  entryDeclaredReady : ∀ entry ∈ entries, Nonempty (ControlledStoredQuery headerControls frontier
    (.certificate entry.answer.aligned.certificate))
  hereditary : world.Hereditary frontier
  packedControlled : packed.Controlled sourceControls frontier

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


/-- The whole-route recursive clause returns the exact selected reply and
its world data. Every other semantic call is made here at an actual proper
original application or Pi child. -/
theorem OriginalApplyPiHistory.replayApplicationPackedWorldStep
    {n : Nat} {profile : Profile n}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (frontier : List (World strata.rules.length))
    (sourceWorld : WorldGenerated strata P base commonCaps commonLeft commonRight sourceGraph
      history.sourceFrame.realization.frame.raw sourceControls)
    (headerWorld : WorldGenerated strata P base commonCaps commonLeft commonRight headerGraph
      history.headerFrame.realization.frame.raw headerControls)
    (sourceBaseline : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (headerBaseline : WorldEnvironmentProvenance strata U history.final)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) sourceWorld.worlds sourceBaseline.worlds)
    (headerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) headerWorld.worlds headerBaseline.worlds)
    (sourceReplayable : sourceWorld.Replayable)
    (headerReplayable : headerWorld.Replayable)
    (sourceReady : sourceWorld.Controlled frontier)
    (sourceHereditary : sourceWorld.Hereditary frontier)
    (headerReady : headerWorld.Controlled frontier)
    (headerHereditary : headerWorld.Hereditary frontier)
    (sourceCompatible : sourceWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (headerCompatible : headerWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (wholeData : history.whole.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier)
    (wholeBoundary : history.whole.WorldBoundary wholeData.inputs sourceControls headerControls
      sourceBaseline headerBaseline)
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent wholeData.controls wholeData.frames)
    (selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
    (selectedData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := (sourceSide).termDisplay) sourceControls sourceBaseline frontier selected.realization)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceAdmission : Covered (@EquationControlMeasure.Less strata.rules.length)
      sourceBaseline.worlds initialProvenance.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sourceSponsored : Sponsored frontier [originalCallWorld sourceControls .fundamental
      (sourceSide).node sourceBaseline])
    (headerSponsored : Sponsored frontier [originalCallWorld headerControls .fundamental
      (headerSide).display.node headerBaseline])
    (sourceF : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .fundamental (sourceSide).node sourceBaseline]))
    (sourceR : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .fundamental (sourceSide).node sourceBaseline]))
    (headerF : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld headerControls .fundamental (headerSide).display.node headerBaseline]))
    (wholeReplay : ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
      (incoming : AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
        (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))) →
      WorldParameterReplyData (P := P) sourceControls sourceBaseline frontier incoming →
      queryProfile.HasType (.sort true) →
      ∃ output : AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
        queryProfile (environmentCost history.final),
        Nonempty (WorldParameterReplyData (P := P) headerControls headerBaseline frontier output))
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      selected.locals (sourceRaw.comp commonLeft) selected.available true profile)
    (packedReady : packed.Controlled sourceControls frontier) :
    ∃ answer : WorldApplyPiReplayResult history field major ownerInitial base commonCaps profile P
        sourceControls headerControls frontier initialProvenance sourceBaseline headerBaseline wholeData.inputs,
      answer.selected = selected ∧ HEq answer.packed packed := by
  have selectedBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) :=
    fun _ => selectedData.capacity
  have selectedOwnerBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial) :=
    fun ordered => Nat.le_trans (selectedBound ordered) (sourceBound ordered)
  let selectedGenerated := selectedData.generation.erase.ambientGenerated
  have headerSame := headerCompatible.controls_match
  have ownerSame : sourceControls.HasPrefix headerControls.cutoff headerControls.fuel :=
    ⟨headerSame.1.symm, headerSame.2.symm⟩
  have headerOwnCompatible : headerWorld.UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    rw [headerSame.1, headerSame.2]; exact headerCompatible
  let headerPackedReady : packed.Controlled headerControls frontier :=
    ⟨packedReady.request.recontrol headerControls ownerSame.1 ownerSame.2,
     packedReady.argument.recontrol headerControls ownerSame.1 ownerSame.2,
     packedReady.domain.recontrol headerControls ownerSame.1 ownerSame.2⟩
  obtain ⟨value, supportEq, ⟨valueReady⟩⟩ := packed.argumentValueWorld sourceControls selected.realization
    selectedData.generation frontier selectedData.controlled selectedData.replayable selectedData.compatible selectedData.hereditary sourceBaseline selectedData.capacity selectedData.covered
    henv hscoped formed selected.closed packedReady sourceSponsored sourceF sourceR
  obtain ⟨incoming, ⟨incomingData⟩⟩ := (sourceSide).piRequestReplyWorld sourceControls selected.realization
    selectedData.generation selectedData.replayable frontier selectedData.controlled selectedData.compatible selectedData.hereditary
    sourceBaseline selectedData.capacity selectedData.covered henv hscoped formed selected.closed
    packed.request packedReady.request sourceSponsored sourceF
  obtain ⟨whole, ⟨replyData⟩⟩ := wholeReplay incoming incomingData packed.request.certificate.formed
  obtain ⟨row, ⟨rowReady⟩⟩ := whole.nativePiRowWorld headerInitial headerLocation headerGraph headerControls
    headerBaseline frontier replyData henv hscoped headerBelow formed packed.request.certificate.formed
    headerSponsored headerF (by simpa only [packed.request.anchor_eq] using packed.request.admitted)
  let emptyQuery : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (sourceRaw.comp commonLeft) ([] : Profile 0) [] := .legacy (.legacy .empty)
  have emptyResources : Footprint.Available [] history.sourceFrame.available := fun _ _ member => nomatch member
  have emptyReady : ControlledStoredQuery headerControls frontier (.observation emptyQuery) :=
    ⟨.legacy _ (.legacy _ .empty), (by
      intro control active
      simp only [StoredOriginalQuery.headDepth, emptyQuery, RichObs.headDepth,
        SortableObs.headDepth, Obs.headDepth]
      exact Nat.zero_le _), (fun _ h => nomatch h)⟩
  let originalSeed := history.argumentSeed (field := field) initial domain body function argument result hu hv
    location sourceGraph noBinders sourceBound emptyQuery emptyResources
  let retainedSeed : PendingRichCapture (field := field) (major := major) history.rightDomain env registry target
      history.headerFrame.locals (headerRaw.comp commonLeft) history.headerFrame.available ownerInitial
      a packed.request.key.anchor (a.subst (sourceRaw.comp commonRight)) :=
    { originalSeed with left_eq := packed.request.anchor_eq.symm }
  have retainedSeedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      sourceBaseline.worlds (retainedSeed.owner.worldEnvironment sourceControls initialProvenance).worlds := by
    change Covered _ sourceBaseline.worlds (initialProvenance.located sourceControls (.appArgument location)).worlds
    rw [located_worlds_nil sourceControls (.appArgument location) initialProvenance noBinders]
    exact sourceAdmission
  let seedScope : CappedOwnerScope common sourceRaw commonLeft commonRight commonCaps retainedSeed.depth
      (retainedSeed.owner.context retainedSeed.initialContext) := {
    toOriginalOwnerScope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv
      location sourceGraph noBinders sourceBound emptyQuery emptyResources
    caps := commonCaps
    capsTail := rfl }
  let headerProvenance := history.headerDomainProvenance initial domain body function argument result hu hv location sourceGraph
  obtain ⟨seedHistory, seedData, seedReserve, seedWorlds, seedBoundary, seedCoherent⟩ :=
    history.argumentSeedHistoryWorld (field := field) initial domain body function argument result hu hv location sourceGraph
      sourceControls headerControls frontier noBinders sourceBound emptyQuery emptyResources sourceWorld headerWorld
      sourceBaseline headerBaseline sourceCovered headerCovered
      sourceReplayable headerReplayable sourceReady headerReady sourceHereditary headerHereditary sourceCompatible headerCompatible wholeData
      wholeBoundary wholeCoherent
  let retainedHistory : OriginalSeedTypeHistory retainedSeed seedScope.toOriginalOwnerScope
      headerGraph headerProvenance history.headerFrame.realization history.leftOrdered history.rightOrdered :=
    ⟨seedHistory.route⟩
  have routeCompatible : ∀ i, (seedData.frames i).UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    intro i; rw [headerSame.1, headerSame.2]; exact seedData.compatible i
  have routeSame : ∀ i, (seedData.controls i).HasPrefix headerControls.cutoff headerControls.fuel :=
    fun i => (routeCompatible i).controls_match
  have sourceHeaderCompatible : sourceWorld.UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    rw [headerSame.1, headerSame.2]; exact sourceCompatible
  let pendingAt := packed.pendingAt (field := field) (domain := headerDomain) initial domain body function argument result
    hu hv location sourceGraph selected selectedOwnerBound whole.reply.answer.reply.locals
    (headerRaw.comp commonLeft) whole.reply.answer.reply.available
  have captured :
      ∃ entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
          whole.reply.answer.reply.locals (headerRaw.comp commonLeft) whole.reply.answer.reply.available
          ownerInitial a packed.request.key.anchor (a.subst (sourceRaw.comp commonRight)),
        ∃ reply : CappedGeneratedQueryReply base commonCaps
            (capturedPiBodyDisplay headerInitial headerLocation headerGraph sourceGraph argument
              (.ofLocation (.appArgument location) initial)) commonLeft commonRight
            (raiseProfile packed.request.rank packed.request.bound profile),
          ∃ generation : WorldGenerated strata P base commonCaps commonLeft commonRight
              (capturedPiBodyDisplay headerInitial headerLocation headerGraph sourceGraph argument
                (.ofLocation (.appArgument location) initial)).graph reply.reply.realization.frame.raw headerControls,
            generation.Replayable ∧ Nonempty (generation.Controlled frontier) ∧
            generation.UsesControlPrefix headerControls.cutoff headerControls.fuel ∧
            Nonempty (ControlledStoredQuery headerControls frontier (.observation reply.reply.query.observation)) ∧
            reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
            reply.reply.locals = Locals.push whole.reply.answer.reply.locals ∧
            (∀ ordered : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment ordered =
              ((whole.reply.answer.reply.realization.frame.group headerDomain history.leftOrdered ownerInitial entries).reserve
                (groupCaptureHistoryReserve field major headerDomain history.leftOrdered history.rightOrdered ownerInitial
                  history.final history.argumentSeedReserve)).dependencyEnvironment ordered) ∧
            generation.worlds =
              ((WorldEnvironmentProvenance.groupHistory field major headerDomain sourceControls headerControls initialProvenance
                headerBaseline (seedHistory.route.worldReserve seedData.inputs)).append
                (WorldEnvironmentProvenance.group sourceControls headerControls initialProvenance replyData.generation.environment entries)).worlds ∧
            Nonempty (GeneratedArgumentCaptureTrace selected.realization.frame pendingAt packed.request.key.input entries) ∧
            (∀ entry ∈ entries, entry.answer.value.support.sortFlags = packed.request.support.sortFlags) ∧
            (∀ entry ∈ entries, Nonempty (ControlledStoredQuery headerControls frontier
              (.certificate entry.answer.aligned.certificate))) ∧ Nonempty (generation.Hereditary frontier) := by
    cases history with
    | mk leftOrdered rightOrdered leftBelow chosen chosenEq sourceFrame headerFrame originalWhole =>
      have chosenEq' : headerDomain = chosen := EndpointState.ref.inj chosenEq
      subst chosen
      obtain ⟨entries, reply, nextWorld, replayable, ready, compatible, query, availableEq, localsEq,
        environment, worlds, trace, supports, declaredReady, hereditary⟩ := packed.captureWorld initial domain body function argument result hu hv location
          sourceGraph selected headerInitial headerLocation headerGraph headerControls sourceControls frontier
          selectedOwnerBound noBinders sourceBaseline selectedData headerPackedReady whole
          replyData.generation replyData.replayable replyData.controlled replyData.hereditary replyData.compatible
          henv hscoped leftOrdered rightOrdered leftBelow headerBelow formed row rowReady.body replyData.query
          packed.request.certificate.formed value
          (valueReady.recontrol headerControls ownerSame.1 ownerSame.2) supportEq
          retainedSeed seedScope sourceControls sourceWorld sourceReplayable sourceReady sourceHereditary sourceHeaderCompatible
          emptyReady ownerSame headerProvenance headerFrame.realization headerWorld headerReplayable headerReady headerHereditary
          headerOwnCompatible retainedHistory initialProvenance ⟨sourceBaseline, headerBaseline⟩ ⟨sourceCovered, headerCovered⟩
          replyData.covered (.inr location) retainedSeedCovered sourceAdmission seedData.inputs
          seedData.generated.wellFormed seedData.controls seedData.frames seedData.replayable seedBoundary seedCoherent
          seedData.ready seedData.hereditary routeCompatible routeSame ownerSame seedData.generated.ambient seedData.generated.sources rfl
      refine ⟨entries, reply, nextWorld, replayable, ready, compatible, query, availableEq, localsEq, ?_, worlds, trace, supports, declaredReady, hereditary⟩
      intro ordered
      simpa only [retainedHistory, seedReserve, OriginalApplyPiHistory.final] using environment ordered
  obtain ⟨entries, reply, nextWorld, nextReplayable, ⟨nextReady⟩, nextCompatible, ⟨nextQueryReady⟩,
    availableEq, localsEq, environment, worlds, ⟨captureTrace⟩, supports, declaredReady, ⟨nextHereditary⟩⟩ := captured
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
  have headerEq : history.rightDomain = headerDomain := (EndpointState.ref.inj history.rightDomainEq).symm
  have semantics := history.resultSemantics henv hscoped formed packed.request whole.toBoundedParameterReply
  refine ⟨{
    selected := selected
    selectedGenerated := selectedGenerated.capped
    selectedBound := selectedBound
    packed := packed
    packedControlled := packedReady
    whole := whole.toBoundedParameterReply
    seed := retainedSeed
    sourceGenerated := sourceWorld.erase.capped
    seedScope := seedScope
    seedGenerated := sourceWorld.erase.capped
    headerProvenance := headerProvenance
    seedHistory := retainedHistory
    seedHistoryGenerated := seedData.generated.ambientGenerated.generated
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
    sourceGeneration := sourceWorld.erase.ambientGenerated
    wholeGeneration := replyData.generation.erase.ambientGenerated
    seedGeneration := sourceWorld.erase.ambientGenerated
    historyGeneration := seedData.generated.ambientGenerated
    generation := ?_
    world := ?_
    replayable := ?_
    controlled := ?_
    compatible := ?_
    queryReady := ?_
    wholeWorld := replyData.generation
    wholeCovered := replyData.covered
    seedData := seedData
    seedWorlds := ?_
    worlds := ?_
    entrySupports := ?_
    entryDeclaredReady := ?_
    hereditary := ?_ }, rfl, HEq.rfl⟩
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
      exact nextWorld.erase.ambientGenerated
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextWorld
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextReplayable
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextReady
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextCompatible
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextQueryReady
  · rw [history.argumentSeedWorld_worlds]
    exact seedWorlds
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact worlds
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact supports
  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact declaredReady

  · cases history with
    | mk leftOrdered rightOrdered leftBelow selected selectedEq sourceFrame headerFrame whole =>
      have selectedEq' : headerDomain = selected := EndpointState.ref.inj selectedEq
      subst selected
      exact nextHereditary

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
