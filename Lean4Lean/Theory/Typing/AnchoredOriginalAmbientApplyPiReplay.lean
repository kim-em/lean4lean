import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayData
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientArgumentValue
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientPiCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayBound
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiSeedHistory

/-! Actual application-history replay under the qualified original bank.
The only recursive semantic input is the exact finite whole-history child;
all source queries, values, rows, captures and budgets are constructed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
set_option Elab.async false


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
theorem OriginalApplyPiHistory.replayApplicationPackedAmbientStep
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
    (bank : OriginalLowerCallBank env U registry limit)
    (wholeReplay : history.whole.schedule < limit →
      ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
        AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
          (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)) →
        queryProfile.HasType (.sort true) →
        Nonempty (AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
          queryProfile (environmentCost history.final)))
    (scheduled : history.schedule < limit)
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      selected.locals (sourceRaw.comp commonLeft) selected.available true profile) :
    ∃ answer : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile,
      answer.selected = selected ∧ HEq answer.packed packed := by
  have selectedCostBound :
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (selected.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (selectedBound history.leftOrdered) 1)
  have selectedLimit : applicationReplayLimit initial domain body function argument result hu hv location
      selected.realization.frame history.leftOrdered ≤ limit := by
    have parent : richSchedule .fundamental
        (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
          (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤ history.schedule :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have phase : applicationReplayLimit initial domain body function argument result hu hv location
        selected.realization.frame history.leftOrdered ≤ richSchedule .fundamental
          (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
            (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 selectedCostBound) 0
    exact Nat.le_trans phase (Nat.le_of_lt (Nat.lt_of_le_of_lt parent scheduled))
  have applicationPaid : richSchedule .fundamental
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) scheduled
  have headerPaid : richSchedule .fundamental
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)) < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) scheduled
  let headerDomainF := bank.codeAt henv hscoped history.rightOrdered headerBelow headerInitial
    (.piDomain headerLocation) headerPaid
  let headerBodyF := bank.codeAt henv hscoped history.rightOrdered headerBelow headerInitial
    (.piBody headerLocation) headerPaid
  obtain ⟨value, supportEq⟩ := packed.argumentValueAmbient (frame := selected.realization.frame)
    (substitutions := selected.realization.substitutions) henv hscoped formed selected.closed
    selectedGenerated.ambient.2 bank selectedLimit
  obtain ⟨incoming⟩ := (sourceSide).piRequestReplyAmbient selected.realization selectedGenerated history.leftOrdered
    (selectedBound history.leftOrdered) henv hscoped formed selected.closed packed.request bank (Nat.le_of_lt applicationPaid)
  obtain ⟨whole⟩ := wholeReplay (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled)
    incoming packed.request.certificate.formed
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
          (∀ ordered : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment ordered =
            ((whole.reply.answer.reply.realization.frame.group headerDomain history.leftOrdered ownerInitial entries).reserve
              (groupCaptureHistoryReserve field major headerDomain history.leftOrdered history.rightOrdered ownerInitial
                history.final history.argumentSeedReserve)).dependencyEnvironment ordered) ∧
          Nonempty (GeneratedArgumentCaptureTrace selected.realization.frame pendingAt packed.request.key.input entries) := by
    cases history with
    | mk leftOrdered rightOrdered leftBelow chosen chosenEq sourceFrame headerFrame originalWhole =>
      have chosenEq' : headerDomain = chosen := EndpointState.ref.inj chosenEq
      subst chosen
      obtain ⟨entries, reply, replyGenerated, environment, trace⟩ := whole.captureArgumentHistoryReply headerInitial headerLocation headerGraph
        henv hscoped leftOrdered rightOrdered leftBelow headerBelow formed packed.request.certificate.formed
        headerDomainF headerBodyF selected.realization.frame selectedGenerated sourceGraph argument
        (.ofLocation (.appArgument location) initial) rfl pendingAt
        (by simpa only [pendingAt, seed, PendingRichCapture.reheader] using
          (OriginalFrameExtension.refl (base := selected.realization.frame.raw)))
        packed.argumentQuery.bound packed.argumentQuery.adapter value supportEq rfl
        retainedSeed seedScope generated.source headerProvenance headerFrame.realization
        retainedHistory seedGenerated.wellFormed seedGenerated.frames
        selectedGenerated.ambient.1 generated.header.ambient.2 seedGenerated.ambient rfl
      refine ⟨entries, reply, replyGenerated, ?_, trace⟩
      intro ordered
      simpa only [retainedHistory, seedReserve, OriginalApplyPiHistory.final] using environment ordered
  obtain ⟨entries, reply, replyGenerated, environment, ⟨captureTrace⟩⟩ := captured
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
    generation := ?_ }, rfl, HEq.rfl⟩
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

theorem OriginalApplyPiHistory.replayApplicationAmbientStep
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
    (bank : OriginalLowerCallBank env U registry limit)
    (wholeReplay : history.whole.schedule < limit →
      ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
        AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
          (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)) →
        queryProfile.HasType (.sort true) →
        Nonempty (AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
          queryProfile (environmentCost history.final)))
    (scheduled : history.schedule < limit)
    (certificate : RichCert sourceEnv env U registry target result selected.locals
      (sourceRaw.comp commonLeft) true (profile : Profile n) footprint)
    (resources : footprint.Available selected.available) :
    Nonempty (AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile) := by
  have selectedCostBound :
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (selected.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (selectedBound history.leftOrdered) 1)
  have selectedLimit : applicationReplayLimit initial domain body function argument result hu hv location
      selected.realization.frame history.leftOrdered ≤ limit := by
    have parent : richSchedule .fundamental
        (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
          (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤ history.schedule :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have phase : applicationReplayLimit initial domain body function argument result hu hv location
        selected.realization.frame history.leftOrdered ≤ richSchedule .fundamental
          (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
            (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 selectedCostBound) 0
    exact Nat.le_trans phase (Nat.le_of_lt (Nat.lt_of_le_of_lt parent scheduled))
  obtain ⟨packet, ⟨supply⟩⟩ := generatedAmbientApplicationArguments initial domain body function argument result hu hv location
    selected.realization.frame selected.realization.substitutions history.leftOrdered
    henv hscoped formed selected.closed selectedGenerated.ambient.2 bank selectedLimit certificate resources
  obtain ⟨packed⟩ := packet.toApplicationBackwardQueries.piRequestWithArgumentAmbient
    henv hscoped history.leftBelow formed selected.closed selectedGenerated.ambient.2 bank selectedLimit supply
  obtain ⟨answer, _, _⟩ := history.replayApplicationPackedAmbientStep (field := field)
    initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    generated selected selectedGenerated selectedBound noBinders sourceBound
    henv hscoped headerBelow formed bank wholeReplay scheduled packed
  exact ⟨answer⟩

theorem OriginalApplyPiHistory.replayApplicationReplyStepAmbient
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.AmbientGenerated base commonCaps)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (wholeReplay : history.whole.schedule < limit →
      ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
        AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
          (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)) →
        queryProfile.HasType (.sort true) →
        Nonempty (AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
          queryProfile (environmentCost history.final)))
    (scheduled : history.schedule < limit)
    (incoming : AmbientBoundedParameterReply base commonCaps start (sourceSide).resultDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)))
    (sorted : profile.HasType (.sort true)) :
    Nonempty (AmbientBoundedParameterReply base commonCaps start history.destination commonLeft commonRight profile
      (environmentCost (history.outputEnvironment field major ownerInitial))) := by
  let selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight := {
    locals := incoming.reply.answer.reply.locals
    available := incoming.reply.answer.reply.available
    realization := incoming.reply.answer.reply.realization
    closed := incoming.reply.answer.reply.closed }
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := incoming.reply.answer.reply.query.code henv sorted
  obtain ⟨answer⟩ := history.replayApplicationAmbientStep (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph generated selected incoming.generation
    (fun ordered => incoming.reply.bounded ordered) noBinders sourceBound henv hscoped headerBelow formed
    bank wholeReplay scheduled certificate resources
  let completed := answer.boundedReply
  have sourceRelated : TypeRelated env U registry target start ((B.inst a).subst (sourceRaw.comp commonLeft)) profile := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst, originalApplicationTypeRouteSide] using incoming.related
  have sourcePath : TypeConversion env U target start ((B.inst a).subst (sourceRaw.comp commonLeft)) := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst, originalApplicationTypeRouteSide] using incoming.path
  exact ⟨{ reply := completed.reply
           related := sourceRelated.trans henv completed.related
           path := sourcePath.trans completed.path
           generation := completed.generation }⟩


end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
