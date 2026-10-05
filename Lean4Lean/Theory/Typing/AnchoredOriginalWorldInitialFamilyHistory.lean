import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyInitialWorldRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteExecutionData
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory

/-! Initialize the actual constant-to-header history with the original
caller generation and its hereditary data. The closed declaration occurrences
are generated here; no consumed family cursor or semantic reply is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private descendant_below same_worldReserve transportWorld_call from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private trans_worldInputs trans_worldReserve sameExpression_worldInputs sameExpression_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- The finite initial history retains each actual occurrence, including all
three uses of the same closed declaration frame. -/
theorem retainedFamilyInitialControlledWorldRoute
    {U : Nat} {queryLevels levels : List VLevel} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (sourceFrame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (sourceWorld : WorldEnvironmentProvenance strata U
      (sourceFrame.realization.frame.dependencyEnvironment controls.ordered))
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (frontier : List (World strata.rules.length))
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw controls)
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (replayable : generated.Replayable) (hereditary : generated.Hereditary frontier)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds sourceWorld.worlds)
    (headerSource : P origin.source) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels controls.ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin controls.ordered).weight ∧
      ∃ seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
        (RetainedHeaderUniverse.display origin queryWF common)
        (sourceFrame.realization.frame.dependencyEnvironment controls.ordered) [],
      ∃ data : route.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
        (route.worldReserve data.inputs).worlds =
          [originalCallWorld controls .assignedComparison node sourceWorld,
           originalCallWorld controls .assignedComparison (.ref (constantPrefix node).reference) sourceWorld,
           originalCallWorld controls .expressionReindex
             (EndpointState.ref (constantPrefix node).reference).typeFormation.node sourceWorld,
           originalCallWorld (controls.atHeader origin) .expressionReindex
             (.ref (origin.familyHeader selection.seedWF).reference) .nil] ++
          ((RetainedHeaderUniverse.route origin origin selection.seedWF queryWF seedEquivalent
            below common registry target commonLeft commonRight).worldReserve
            (RetainedHeaderUniverse.worldInputs controls origin origin selection.seedWF queryWF seedEquivalent
              below common registry target commonLeft commonRight)).worlds ∧
        ∃ boundary : route.WorldBoundary data.inputs controls (controls.atHeader origin) sourceWorld .nil,
          boundary.FrameOccurrenceCoherent data.controls data.frames := by
  obtain ⟨selection, ledger, bound, equivalent, route, sourceGenerated, inputs, worlds, boundary, occurrences⟩ :=
    retainedFamilyInitialWorldRoute initial location graph sourceFrame controls below sourceWorld
      origin queryWF queryEquivalent caps generated.erase headerSource
  let closed := RetainedHeaderUniverse.frame origin queryWF common env registry target commonLeft commonRight
  let closedGeneration : WorldGenerated strata P base caps commonLeft commonRight closed.box.graph
      closed.box.frame.realization.frame.raw (controls.atHeader origin) :=
    .empty common commonLeft commonRight (origin.sourceBelow.trans below) headerSource (controls.atHeader origin)
  let sourceData : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨sourceFrame.box, controls, sourceWorld⟩ :=
    ⟨generated, replayable, ready, compatible, covered, hereditary⟩
  let closedData : WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨closed.box, controls.atHeader origin, .nil⟩ := {
    generation := closedGeneration
    replayable := trivial
    controlled := ⟨.nil, by intro control active; exact Nat.zero_le _, by intro world member; cases member⟩
    compatible := ⟨rfl, rfl⟩
    covered := Covered.refl []
    hereditary := ⟨trivial, .nil, trivial⟩ }
  let execution : boundary.ExecutionFrames P base caps frontier := by
    classical
    intro occurrence member
    rw [occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    by_cases same : occurrence = ⟨sourceFrame.box, controls, sourceWorld⟩
    · exact same.symm ▸ sourceData
    · exact (member.resolve_left same).symm ▸ closedData
  let data := boundary.controlledDataOfExecution sourceGenerated execution
  exact ⟨selection, ledger, bound, equivalent, route, data, worlds, boundary,
    boundary.controlledDataOfExecution_coherent sourceGenerated execution⟩



private noncomputable def closedFrameExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    (left right : Subst) (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length)) (below : sourceEnv ≤ env) (source : P sourceEnv)
    (world : WorldEnvironmentProvenance strata U
      ((closedTypeRouteFrame context common env registry target left right).realization.frame.dependencyEnvironment controls.ordered)) :
    WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨(closedTypeRouteFrame context common env registry target left right).box, controls, world⟩ := by
  cases context
  exact {
    generation := .empty common left right below source controls
    replayable := trivial
    controlled := ⟨.nil, by intro control active; exact Nat.zero_le _, by intro w member; cases member⟩
    compatible := ⟨rfl, rfl⟩
    covered := by intro w member; cases member
    hereditary := ⟨trivial, .nil, trivial⟩ }

private theorem castWorld_worlds
    {strata : EquationStratification env} {first second : List Closure}
    (same : first = second) (world : WorldEnvironmentProvenance strata U first) :
    (same ▸ world : WorldEnvironmentProvenance strata U second).worlds = world.worlds := by
  cases same
  rfl

/-- Start the first actual application history from the literal declaration
Pi, without first consuming the opaque family certificate. Every saved frame
retains its actual hereditary execution data. -/
theorem firstApplicationPiHistoryWorld
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (initial : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (sourceWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    (shape : info.type.instL queryLevels = .forallE C D)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (frontier : List (World strata.rules.length))
    (generation : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls)
    (ready : generation.Controlled frontier)
    (compatible : generation.UsesControlPrefix controls.cutoff controls.fuel)
    (replayable : generation.Replayable) (hereditary : generation.Hereditary frontier)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds sourceWorld.worlds)
    (headerSource : P origin.source) :
    let left := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
    let right := RetainedHeaderUniverse.nativeSide origin queryWF shape common
    ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
      ∃ frameEq : history.sourceFrame = frame,
      ∃ finalWorld : WorldEnvironmentProvenance strata U history.final,
        finalWorld.worlds = [] ∧
        history.headerFrame = RetainedHeaderUniverse.nativeFrame origin queryWF shape common env registry target commonLeft commonRight ∧
        ∃ data : history.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
        ∃ boundary : history.whole.WorldBoundary data.inputs controls (controls.atHeader origin)
          ((congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) frameEq).symm ▸ sourceWorld) finalWorld,
          boundary.FrameOccurrenceCoherent data.controls data.frames ∧
          ∀ {projectedName index displayedMajor outerType}
            (outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType)
            (head : ProjectionHead outer) (rootLocation : Located (.right head.major) (.ref root)),
            Sponsored [originalCallWorld controls .assignedComparison outer sourceWorld]
              (history.whole.worldReserve data.inputs).worlds := by
  let left := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
  let right := RetainedHeaderUniverse.nativeSide origin queryWF shape common
  obtain ⟨selection, ledger, bound, equivalent, initialRoute, initialData, initialWorlds, initialBoundary, initialCoherent⟩ :=
    retainedFamilyInitialControlledWorldRoute initial (.appFunction location) graph frame controls below sourceWorld
      origin queryWF queryEquivalent caps frontier generation ready compatible replayable hereditary covered headerSource
  let first := RawGeneratedTypeRoute.same left.pi.display
    (OriginalNestedDisplay.ofOccurrence initial (.appFunction location) graph).formationDisplay
    controls.ordered controls.ordered (frame.realization.frame.dependencyEnvironment controls.ordered) frame
  have firstGenerated : first.SourceGenerated P base caps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
    · rw [RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨generation.erase.sources.1.source, generation.erase.sources.1.source, trivial⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact generation.erase
  let firstBoundary := RawGeneratedTypeRoute.WorldBoundary.same left.pi.display
    (OriginalNestedDisplay.ofOccurrence initial (.appFunction location) graph).formationDisplay
    controls.ordered controls.ordered frame controls controls sourceWorld sourceWorld ⟨rfl, rfl⟩
  let firstExecution : firstBoundary.ExecutionFrames P base caps frontier := by
    intro occurrence member
    have same := List.mem_singleton.mp member
    exact same.symm ▸ (show WorldBoundaryFrame.ExecutionData P base caps frontier
      ⟨frame.box, controls, sourceWorld⟩ from ⟨generation, replayable, ready, compatible, covered, hereditary⟩)
  let headerFrame := RetainedHeaderUniverse.nativeFrame origin queryWF shape common env registry target commonLeft commonRight
  let headerWorld : WorldEnvironmentProvenance strata U (headerFrame.realization.frame.dependencyEnvironment origin.ordered) :=
    (RetainedHeaderUniverse.nativeFrame_environment origin queryWF shape common env registry target commonLeft commonRight).symm ▸ .nil
  let headerExecution := closedFrameExecution (base := base) (caps := caps)
    (right.location.contextDerivation .nil) common commonLeft commonRight
    (controls.atHeader origin) frontier (origin.sourceBelow.trans below) headerSource headerWorld
  have rightShape : info.type.instL queryLevels = (VExpr.forallE right.A right.B).subst right.raw :=
    shape.trans subst_id.symm
  let last := RawGeneratedTypeRoute.sameExpression (RetainedHeaderUniverse.display origin queryWF common) right.display
    rightShape origin.ordered origin.ordered [] headerFrame
  have lastGenerated : last.SourceGenerated P base caps :=
    RetainedHeaderUniverse.sourceGenerated_same _ _ _ _ _ _ _
      (origin.sourceBelow.trans below) (origin.sourceBelow.trans below)
      headerSource headerSource headerExecution.generation.erase
  let lastBoundary := RawGeneratedTypeRoute.sameExpression_worldBoundary
    (RetainedHeaderUniverse.display origin queryWF common) right.display rightShape
    origin.ordered origin.ordered [] headerFrame
    (controls.atHeader origin) (controls.atHeader origin) .nil headerWorld ⟨rfl, rfl⟩
  let lastExecution : lastBoundary.ExecutionFrames P base caps frontier := by
    intro occurrence member
    rw [RawGeneratedTypeRoute.sameExpression_worldBoundary_frames] at member
    exact (List.mem_singleton.mp member).symm ▸ headerExecution
  let whole := first.trans (initialRoute.trans last)
  have wholeGenerated : whole.SourceGenerated P base caps :=
    RetainedHeaderUniverse.sourceGenerated_trans firstGenerated
      (RetainedHeaderUniverse.sourceGenerated_trans initialData.generated lastGenerated)
  let boundary := firstBoundary.trans (initialBoundary.trans lastBoundary)
  let initialExecution := initialBoundary.executionFramesOfData initialData initialCoherent
  let execution : boundary.ExecutionFrames P base caps frontier := by
    intro occurrence member
    apply Classical.choice
    change occurrence ∈ firstBoundary.frames ++ (initialBoundary.frames ++ lastBoundary.frames) at member
    rcases List.mem_append.mp member with member | member
    · exact ⟨firstExecution occurrence member⟩
    · rcases List.mem_append.mp member with member | member
      · exact ⟨initialExecution occurrence member⟩
      · exact ⟨lastExecution occurrence member⟩
  let selected := piPrefix ((Located.here (root := (origin.familyHeader queryWF).reference)).castExpression shape)
  let rightDomain := Classical.choose selected.view.location.originalDomains.1
  let rightDomainEq := Classical.choose_spec selected.view.location.originalDomains.1
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
    ⟨controls.ordered, origin.ordered, below, rightDomain, rightDomainEq, frame, headerFrame, whole⟩
  let data := boundary.controlledDataOfExecution wholeGenerated execution
  refine ⟨history, rfl, headerWorld, castWorld_worlds _ _, rfl, data, boundary,
    boundary.controlledDataOfExecution_coherent wholeGenerated execution, ?_⟩
  intro projectedName index displayedMajor outerType outer head rootLocation
  change Sponsored _ (whole.worldReserve data.inputs).worlds
  change Sponsored _ ((first.trans (initialRoute.trans last)).worldReserve
    (boundary.controlledDataOfExecution wholeGenerated execution).inputs).worlds
  change Sponsored _ ((first.trans (initialRoute.trans last)).worldReserve
    (trans_worldInputs (controls, controls, sourceWorld, sourceWorld)
      (trans_worldInputs initialData.inputs
        (sameExpression_worldInputs (RetainedHeaderUniverse.display origin queryWF common) right.display rightShape
          origin.ordered origin.ordered [] headerFrame
          (controls.atHeader origin) (controls.atHeader origin) .nil headerWorld)))).worlds
  rw [trans_worldReserve, trans_worldReserve]
  apply Sponsored.merge
  · rw [same_worldReserve]
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_singleton_self _, descendant_below head rootLocation
        (.appPiFormation location) controls sourceWorld _ _⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, descendant_below head rootLocation
        (.assignedFormation (.appFunction location)) controls sourceWorld _ _⟩
  · apply Sponsored.merge
    · rw [initialWorlds]
      apply Sponsored.merge
      · intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_singleton_self _, descendant_below head rootLocation
            (.appFunction location) controls sourceWorld _ _⟩
        · exact ⟨_, List.mem_singleton_self _, descendant_below head rootLocation
            ((constantPrefix function).route.locate (.appFunction location)) controls sourceWorld _ _⟩
        · exact ⟨_, List.mem_singleton_self _, descendant_below head rootLocation
            (.assignedFormation ((constantPrefix function).route.locate (.appFunction location))) controls sourceWorld _ _⟩
        · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls origin
            _ outer sourceWorld _ _⟩
      · exact RetainedHeaderUniverse.worldReserve_sponsored controls origin origin
          selection.seedWF queryWF equivalent below common registry target commonLeft commonRight
          outer sourceWorld .assignedComparison
    · erw [sameExpression_worldReserve]
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls origin
          _ outer sourceWorld _ _⟩
      · cases List.mem_singleton.mp member
        have same : originalCallWorld (controls.atHeader origin) .expressionReindex right.display.node headerWorld =
            originalCallWorld (controls.atHeader origin) .expressionReindex right.display.node .nil := by
          exact transportWorld_call _ _ _ _ _
        rw [same]
        exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls origin
          _ outer sourceWorld _ _⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
