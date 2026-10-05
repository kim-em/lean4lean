import Lean4Lean.Theory.Typing.AnchoredOriginalCappedParameterPrefixCapture

/-! The first projection parameter capture starts with the actual argument
query in the major's original assigned-family application. It computes
normalization, declaration cells, and the constructor capture frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem firstFamilyParameterCaptureCapped
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    {initialContext : ContextDerivation sourceEnv U source}
    (occurrence : OriginalRichOccurrenceFrame (assignedFamilyApplication major 0 rfl).argument.location
      initialContext env registry target locals σ τ available ordered ownerInitial)
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {graph : OriginalCaptureMap (common := common)
      ((assignedFamilyApplication major 0 rfl).argument.location.contextDerivation initialContext) raw}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph occurrence.frame.raw)
    (availableClosed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target (assignedFamilyApplication major 0 rfl).view.argument
      locals σ (input : Profile n) footprint)
    (resources : footprint.Available available) :
    let captured := occurrence.frame.dependencyEnvironment ordered
    let application := assignedFamilyApplication major 0 rfl
    let pi := piPrefix (Located.assignedFormation (Located.appFunction application.view.location))
    ∀ value : RichBinderValue sourceEnv env U registry target application.view.argument locals σ τ available input,
    FormationRestoreCall env U registry target ordered captured
      ((EndpointState.app application.view.domainWF application.view.bodyWF application.view.domain
        application.view.codomain application.view.function application.view.argument application.view.result).dependencyOrigin ordered)
      application.view.argument.typeFormation.node application.view.domain locals σ available →
    FormationRestoreCall env U registry target ordered captured (application.node.dependencyOrigin ordered)
      application.view.domain pi.view.domain locals σ available →
    (∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction major) (.ref (constantPrefix (assignedFirstFamilyFunction major)).reference),
      route.PeelCalls env registry target ordered captured locals σ available) →
    PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ commonLeft available →
    PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference commonLeft →
    (∀ (selection : RichHeaderSelection sourceEnv U name levels ordered)
      (ledger : FamilyParameterLedger selection), ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight →
      ∀ cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
        levelsWF selection.seedWF selection.equivalent,
      FirstParameterCellCalls cells
        (normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) positive)
        (firstConstructorParameterPrefix ordered cells positive) env registry target commonLeft) →
    ∃ (selection : RichHeaderSelection sourceEnv U name levels ordered)
      (ledger : FamilyParameterLedger selection),
      ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      ∃ cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
        levelsWF selection.seedWF selection.equivalent,
      let ctor := firstConstructorParameterPrefix ordered cells positive
      ∃ entry : RichGroupedCaptureEntry (field := field) (major := major) ctor.domainOriginal env registry target
        [] commonLeft (fun _ => []) ownerInitial argument (argument.subst σ) (argument.subst τ),
      entry.owner = application.headerOwner ∧ (⟨entry.rank, entry.input⟩ : Need) = ⟨n, input⟩ ∧
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture (.empty common) ctor.domainOriginal graph application.view.argument
          (.ofLocation application.argument.location initialContext))
        ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight) (locals := []) (available := fun _ => [])).group
          ctor.domainOriginal ordered ownerInitial [entry]).raw ∧
      CappedFirstParameterPrefixes (base := base) (commonCaps := commonCaps) (field := field) (major := major) cells graph
        occurrence.frame application.view.argument (.ofLocation application.argument.location initialContext)
        ordered commonLeft commonRight ownerInitial argument input := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls normalizationCalls cellsIH
  let application := assignedFamilyApplication major 0 rfl
  obtain ⟨selection, ledger, bound, aligned, valueEq⟩ := assignedFirstFamilyAlignmentNormalized_retained
    (field := field) henv hscoped formed ordered registered positive major occurrence.frame value
    argumentR domainR prefixCalls headerCalls normalizationCalls
  let packet := selectProjectionParameters ordered registered selection.seedWF
  let familyHead := normalizedFamilyPrefix packet positive
  obtain ⟨cells⟩ := firstProjectionParameterCells packet levelsWF selection.seedWF selection.equivalent positive
  let ctor := firstConstructorParameterPrefix ordered cells positive
  have calls := cellsIH selection ledger bound cells
  let answer := calls.align henv below formed positive aligned
  have expressionEq : argument = argument.lift' (.skipN .refl application.argument.location.binderPrefix.length) := by
    rw [application.argument.prefix_eq]
    simp
  let entry := RichGroupedCaptureEntry.ofMajorOccurrence (field := field) application.argument.location occurrence
    expressionEq rfl rfl query resources answer
  let familyEntry := RichGroupedCaptureEntry.ofMajorOccurrence (field := field) application.argument.location occurrence
    expressionEq rfl rfl query resources aligned
  have prefixes := (calls.prefixTransfers henv below formed positive).captureGroupsCapped graph occurrence.frame
    generated application.view.argument (.ofLocation application.argument.location initialContext) rfl
    henv ordered familyEntry availableClosed .refl rfl
  refine ⟨selection, ledger, bound, cells, entry, rfl, rfl, ?_, prefixes⟩
  apply CappedCaptureGenerated.group (CappedCaptureGenerated.empty common commonLeft commonRight)
    ctor.domainOriginal generated graph application.view.argument
    (.ofLocation application.argument.location initialContext) rfl ordered ownerInitial (entry.pending availableClosed) .refl [entry]
  intro selected member
  cases List.mem_singleton.mp member
  exact ⟨.refl⟩

/-- The actual projection producer discharges all cell schedules internally. -/
theorem firstFamilyParameterCaptureCappedOfProjection
    {sourceEnv : VEnv} {U : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : (argument :: params).length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels (argument :: params) index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (majorOriginal : Derivation sourceEnv U source sourceMajor majorExpression
      (mkApps (.const name levels) ((argument :: params) ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (ownerInitial : List Closure)
    {initialContext : ContextDerivation sourceEnv U source}
    (occurrence : OriginalRichOccurrenceFrame (assignedFamilyApplication (.left majorOriginal) 0 rfl).argument.location
      initialContext env registry target locals σ τ available ordered ownerInitial)
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {graph : OriginalCaptureMap (common := common)
      ((assignedFamilyApplication (.left majorOriginal) 0 rfl).argument.location.contextDerivation initialContext) raw}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph occurrence.frame.raw)
    (availableClosed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target (assignedFamilyApplication (.left majorOriginal) 0 rfl).view.argument
      locals σ (input : Profile n) footprint)
    (resources : footprint.Available available) :
    let captured := occurrence.frame.dependencyEnvironment ordered
    let application := assignedFamilyApplication (.left majorOriginal) 0 rfl
    let pi := piPrefix (Located.assignedFormation (Located.appFunction application.view.location))
    ∀ value : RichBinderValue sourceEnv env U registry target application.view.argument locals σ τ available input,
    FormationRestoreCall env U registry target ordered captured
      ((EndpointState.app application.view.domainWF application.view.bodyWF application.view.domain
        application.view.codomain application.view.function application.view.argument application.view.result).dependencyOrigin ordered)
      application.view.argument.typeFormation.node application.view.domain locals σ available →
    FormationRestoreCall env U registry target ordered captured (application.node.dependencyOrigin ordered)
      application.view.domain pi.view.domain locals σ available →
    (∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction (.left majorOriginal)) (.ref (constantPrefix (assignedFirstFamilyFunction (.left majorOriginal))).reference),
      route.PeelCalls env registry target ordered captured locals σ available) →
    PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction (.left majorOriginal))).reference locals σ commonLeft available →
    PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction (.left majorOriginal))).reference commonLeft →
    ClosedParameterInduction env U registry target commonLeft
      (richSchedule .fundamental (Closure.close
        ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
          selected fieldWF (.ref field) majorOriginal closed allowed).dependencyOrigin ordered) ownerInitial).cost) →
    ∃ (selection : RichHeaderSelection sourceEnv U name levels ordered)
      (ledger : FamilyParameterLedger selection),
      ledger.pairWeight ≤ (majorOriginal.dependencyOrigin ordered).weight ∧
      ∃ cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
        levelsWF selection.seedWF selection.equivalent,
      let ctor := firstConstructorParameterPrefix ordered cells positive
      ∃ entry : RichGroupedCaptureEntry (field := field) (major := .left majorOriginal) ctor.domainOriginal env registry target
        [] commonLeft (fun _ => []) ownerInitial argument (argument.subst σ) (argument.subst τ),
      entry.owner = application.headerOwner ∧ (⟨entry.rank, entry.input⟩ : Need) = ⟨n, input⟩ ∧
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (.capture (.empty common) ctor.domainOriginal graph application.view.argument
          (.ofLocation application.argument.location initialContext))
        ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight) (locals := []) (available := fun _ => [])).group
          ctor.domainOriginal ordered ownerInitial [entry]).raw ∧
      CappedFirstParameterPrefixes (base := base) (commonCaps := commonCaps) (field := field) (major := .left majorOriginal) cells graph
        occurrence.frame application.view.argument (.ofLocation application.argument.location initialContext)
        ordered commonLeft commonRight ownerInitial argument input := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls normalizationCalls induction
  apply firstFamilyParameterCaptureCapped henv hscoped formed ordered below registered positive levelsWF
    (.left majorOriginal) occurrence generated availableClosed query resources value argumentR domainR prefixCalls
    headerCalls normalizationCalls
  intro selection ledger bound cells
  exact firstParameterCellCalls_ofProjection ordered below registered levelsWF levelCount parameterCount indexCount
    selected fieldWF field majorOriginal closed allowed ownerInitial positive selection ledger bound cells induction

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
