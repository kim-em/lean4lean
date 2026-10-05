import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory

/-! The first retained whole-Pi history carries executable frame data at
its actual annotated occurrences. The caller frame is transported along its
original context equality; declaration frames are constructed as empty. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportRouteFrame transportRouteFrame_environment from
  Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
open private transport_sourceGenerated closed_sourceGenerated from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiHistory
open private RetainedHeaderUniverse.source_trans RetainedHeaderUniverse.source_same from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderUniverseReplay
open private sameExpression_worldInputs sameExpression_worldReserve trans_worldInputs trans_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
open private boundaryFrames_trans append_eq from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyInitialWorldRoute
open private transportWorld transportWorld_call transportWorld_worlds descendant_below same_worldReserve from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private noncomputable def transportGeneration
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls) :
    WorldGenerated strata P base caps commonLeft commonRight (equal ▸ graph)
      (transportRouteFrame equal frame).realization.frame.raw controls := by
  cases equal
  exact generated

private theorem transportGeneration_properties
    {strata : EquationStratification env} {frontier : List (World strata.rules.length)} {base : OriginalCaptureBase env U registry target}
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls)
    (replayable : generated.Replayable) (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (captured : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds captured.worlds) :
    (transportGeneration equal frame generated).Replayable ∧
    Nonempty ((transportGeneration equal frame generated).Controlled frontier) ∧
    (transportGeneration equal frame generated).UsesControlPrefix controls.cutoff controls.fuel ∧
    Covered (@EquationControlMeasure.Less strata.rules.length) (transportGeneration equal frame generated).worlds
      (transportWorld (transportRouteFrame_environment equal frame controls.ordered).symm captured).worlds := by
  cases equal
  exact ⟨replayable, ⟨ready⟩, compatible, covered⟩

private theorem closedOccurrence_eq
    {strata : EquationStratification env}
    (context : ContextDerivation sourceEnv U []) (controls : OriginalWorldControls strata sourceEnv)
    (common : List VExpr) (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (empty : (closedTypeRouteFrame context common env registry target left right).realization.frame.dependencyEnvironment
      controls.ordered = []) :
    (⟨(closedTypeRouteFrame context common env registry target left right).box, controls,
      transportWorld empty.symm .nil⟩ : WorldBoundaryFrame env U registry target common left right strata) =
    ⟨(closedTypeRouteFrame .nil common env registry target left right).box, controls, .nil⟩ := by
  cases context
  rfl

private theorem nativeOccurrence_eq
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (shape : info.type.instL levels = .forallE A B) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (⟨(RetainedHeaderUniverse.nativeFrame origin levelsWF shape common env registry target left right).box,
      controls.atHeader origin,
      transportWorld (RetainedHeaderUniverse.nativeFrame_environment origin levelsWF shape common
        env registry target left right).symm .nil⟩ : WorldBoundaryFrame env U registry target common left right strata) =
    ⟨(RetainedHeaderUniverse.frame origin levelsWF common env registry target left right).box,
      controls.atHeader origin, .nil⟩ := by
  exact closedOccurrence_eq _ (controls.atHeader origin) common registry target left right
    (closedTypeRouteFrame_environment _ common (controls.atHeader origin).ordered)

private theorem sourceHeader_frameCoherent
    {strata : EquationStratification env} {P : VEnv → Prop} {levels : List VLevel}
    {frontier : List (World strata.rules.length)}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {base : OriginalCaptureBase env U registry target}
    (sourceFrame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv)
    (sourceWorld : WorldEnvironmentProvenance strata U (sourceFrame.realization.frame.dependencyEnvironment controls.ordered))
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (below : sourceEnv ≤ env) (headerSource : P origin.source)
    (sourceGenerated : WorldGenerated strata P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw controls)
    (sourceReplayable : sourceGenerated.Replayable)
    (sourceReady : sourceGenerated.Controlled frontier)
    (sourceCompatible : sourceGenerated.UsesControlPrefix controls.cutoff controls.fuel)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) sourceGenerated.worlds sourceWorld.worlds)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {lc : OriginalWorldControls strata left.sourceEnv} {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {rw : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary inputs lc rc lw rw)
    (occurrences : ∀ occurrence ∈ boundary.frames,
      occurrence = ⟨sourceFrame.box, controls, sourceWorld⟩ ∨
      occurrence = ⟨(RetainedHeaderUniverse.frame origin levelsWF common env registry target commonLeft commonRight).box,
        controls.atHeader origin, .nil⟩) :
    ∃ frameControls : ∀ boxed ∈ route.frames, OriginalWorldControls strata boxed.sourceEnv,
    ∃ frameGenerated : ∀ boxed (member : boxed ∈ route.frames),
      WorldGenerated strata P base caps commonLeft commonRight boxed.graph boxed.frame.realization.frame.raw
        (frameControls boxed member),
      boundary.FrameCoherent frameControls frameGenerated ∧
      ∀ boxed member, (frameGenerated boxed member).Replayable ∧
        Nonempty ((frameGenerated boxed member).Controlled frontier) ∧
        (frameGenerated boxed member).UsesControlPrefix controls.cutoff controls.fuel := by
  classical
  let empty := RetainedHeaderUniverse.frame origin levelsWF common env registry target commonLeft commonRight
  let emptyGenerated : WorldGenerated strata P base caps commonLeft commonRight empty.box.graph
      empty.box.frame.realization.frame.raw (controls.atHeader origin) :=
    .empty common commonLeft commonRight (origin.sourceBelow.trans below) headerSource (controls.atHeader origin)
  have emptyReady : emptyGenerated.Controlled frontier :=
    ⟨.nil, by intro control above; exact Nat.zero_le _, by intro world member; cases member⟩
  have emptyCompatible : emptyGenerated.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  have different : empty.box ≠ sourceFrame.box := by
    intro same
    have sourceEq : origin.source = sourceEnv := congrArg OriginalTypeRouteFrameBox.sourceEnv same
    have conflict := origin.fresh
    rw [sourceEq, origin.constant] at conflict
    cases conflict
  dsimp only [empty] at different
  have selectedBox (boxed) (member : boxed ∈ route.frames) : boxed = sourceFrame.box ∨ boxed = empty.box := by
    rw [← boundary.frames_boxes] at member
    obtain ⟨occurrence, present, same⟩ := List.mem_map.mp member
    rcases occurrences occurrence present with rfl | rfl
    · exact .inl same.symm
    · exact .inr same.symm
  let selected := fun boxed (member : boxed ∈ route.frames) =>
    (show Σ control : OriginalWorldControls strata boxed.sourceEnv,
      Σ generated : WorldGenerated strata P base caps commonLeft commonRight boxed.graph
          boxed.frame.realization.frame.raw control,
        PLift generated.Replayable × generated.Controlled frontier ×
          PLift (generated.UsesControlPrefix controls.cutoff controls.fuel) from by
      by_cases same : boxed = sourceFrame.box
      · subst boxed
        exact ⟨controls, sourceGenerated, ⟨sourceReplayable⟩, sourceReady, ⟨sourceCompatible⟩⟩
      · have emptyEq := (selectedBox boxed member).resolve_left same
        subst boxed
        exact ⟨controls.atHeader origin, emptyGenerated, ⟨by trivial⟩, emptyReady, ⟨emptyCompatible⟩⟩)
  have selectedSource (member : sourceFrame.box ∈ route.frames) :
      selected sourceFrame.box member = ⟨controls, sourceGenerated, ⟨sourceReplayable⟩, sourceReady, ⟨sourceCompatible⟩⟩ := by
    dsimp only [selected]
    rw [dif_pos rfl]
  have selectedEmpty (member : empty.box ∈ route.frames) :
      selected empty.box member = ⟨controls.atHeader origin, emptyGenerated, ⟨by trivial⟩, emptyReady, ⟨emptyCompatible⟩⟩ := by
    dsimp only [selected]
    rw [dif_neg different]
  refine ⟨fun boxed member => (selected boxed member).1,
    fun boxed member => (selected boxed member).2.1, ?_, ?_⟩
  · intro occurrence member
    rcases occurrences occurrence member with rfl | rfl
    · change (selected sourceFrame.box _).1 = controls ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) (selected sourceFrame.box _).2.1.worlds sourceWorld.worlds
      rw [selectedSource]
      exact ⟨rfl, sourceCovered⟩
    · change (selected empty.box _).1 = controls.atHeader origin ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) (selected empty.box _).2.1.worlds []
      rw [selectedEmpty]
      exact ⟨rfl, Covered.refl []⟩
  · intro boxed member
    exact ⟨(selected boxed member).2.2.1.down,
      ⟨(selected boxed member).2.2.2.1⟩, (selected boxed member).2.2.2.2.down⟩


theorem retainedFirstFamilyWorldExecution
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env} {frontier : List (World strata.rules.length)}
    {outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType}
    (head : OriginalFactorCut.ProjectionHead outer)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (majorLocation : Located (.right head.major) (.ref major))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U
      (frame.realization.frame.dependencyEnvironment controls.ordered))
    (consumed : RetainedRichFamilyConsumption major env registry target locals σ available
      name levels (argument :: arguments) (n := n+1) (.family demand))
    {base : OriginalCaptureBase env U registry target}
    (worldGenerated : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls)
    (worldReplayable : worldGenerated.Replayable)
    (worldReady : worldGenerated.Controlled frontier)
    (worldCompatible : worldGenerated.UsesControlPrefix controls.cutoff controls.fuel)
    (worldCovered : Covered (@EquationControlMeasure.Less strata.rules.length) worldGenerated.worlds captured.worlds)
    (headerSource : P consumed.seed.origin.source) :
    ∃ A domains, consumed.seed.signature.domains = A :: domains ∧
      ∃ shape : consumed.seed.info.type.instL consumed.seed.seed =
          .forallE A (wrapForalls domains consumed.seed.signature.result),
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := RetainedHeaderUniverse.nativeSide consumed.seed.origin consumed.seed.seedWF shape common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.AmbientGenerated base caps ∧
        history.whole.SourceGenerated P base caps ∧
        SourceCaptureGenerated P base caps commonLeft commonRight right.graph
          history.headerFrame.realization.frame.raw ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.final = [] ∧
        right.sourceEnv ≤ env ∧
        right.A = A ∧ right.B = wrapForalls domains consumed.seed.signature.result ∧
        ∃ inputs : history.whole.WorldInputs strata,
          Sponsored [originalCallWorld controls .assignedComparison outer captured]
            (history.whole.worldReserve inputs).worlds ∧
          ∃ sourceEnvironment : history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered =
              frame.realization.frame.dependencyEnvironment controls.ordered,
          ∃ finalWorld : WorldEnvironmentProvenance strata U history.final,
            finalWorld.worlds = [] ∧
            ∃ boundary : history.whole.WorldBoundary inputs controls (controls.atHeader consumed.seed.origin)
              (transportWorld sourceEnvironment.symm captured) finalWorld,
            ∃ frameControls : ∀ boxed ∈ history.whole.frames, OriginalWorldControls strata boxed.sourceEnv,
            ∃ frameGenerated : ∀ boxed (member : boxed ∈ history.whole.frames),
              WorldGenerated strata P base caps commonLeft commonRight boxed.graph boxed.frame.realization.frame.raw
                (frameControls boxed member),
              boundary.FrameCoherent frameControls frameGenerated ∧
              ∀ boxed member, (frameGenerated boxed member).Replayable ∧
                Nonempty ((frameGenerated boxed member).Controlled frontier) ∧
                (frameGenerated boxed member).UsesControlPrefix controls.cutoff controls.fuel := by
  let generated := worldGenerated.erase
  let ordered := controls.ordered
  have saturated := consumed.cursor.saturated henv hscoped formed
  cases domainsEq : consumed.seed.signature.domains with
  | nil => simp only [domainsEq, List.length_nil, List.length_cons] at saturated; omega
  | cons A domains =>
    have shape : consumed.seed.info.type.instL consumed.seed.seed =
        .forallE A (wrapForalls domains consumed.seed.signature.result) := by
      simpa only [domainsEq, wrapForalls, List.foldr_cons] using consumed.seed.signature.type_eq
    let left := assignedFamilyRouteSide major initial graph 0 rfl
    let sourceFrame := assignedFamilyRouteFrame major initial graph 0 rfl frame
    have sourceGenerated : SourceCaptureGenerated P base caps commonLeft commonRight left.graph
        sourceFrame.realization.frame.raw := transport_sourceGenerated _ frame generated
    let sourceWorld := transportWorld
      (assignedFamilyRouteFrame_environment major initial graph 0 rfl frame ordered).symm captured
    let sourceWorldGenerated : WorldGenerated strata P base caps commonLeft commonRight left.graph
        sourceFrame.realization.frame.raw controls := transportGeneration _ frame worldGenerated
    obtain ⟨sourceReplayable, ⟨sourceReady⟩, sourceCompatible, sourceCovered⟩ :=
      transportGeneration_properties _ frame worldGenerated worldReplayable worldReady worldCompatible captured worldCovered
    obtain ⟨selection, ledger, rootBound, equivalent, initialRoute, initialGenerated, initialInputs, initialWorlds, initialBoundary, initialFrames⟩ :=
      retainedFamilyInitialWorldRoute left.initial (.appFunction left.location) left.graph sourceFrame controls below
        sourceWorld consumed.seed.origin consumed.seed.seedWF consumed.seed.equivalent caps sourceGenerated headerSource
    let right := RetainedHeaderUniverse.nativeSide consumed.seed.origin consumed.seed.seedWF shape common
    let headerFrame := RetainedHeaderUniverse.nativeFrame consumed.seed.origin consumed.seed.seedWF
      shape common env registry target commonLeft commonRight
    have headerGenerated : SourceCaptureGenerated P base caps commonLeft commonRight right.graph
        headerFrame.realization.frame.raw :=
      closed_sourceGenerated _ common caps commonLeft commonRight
        (consumed.seed.origin.sourceBelow.trans below) headerSource
    let first := RawGeneratedTypeRoute.same left.pi.display
      (OriginalNestedDisplay.ofOccurrence left.initial (.appFunction left.location) left.graph).formationDisplay
      ordered ordered (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceFrame
    have firstGenerated : first.SourceGenerated P base caps := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
      · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
      · rw [RawGeneratedTypeRoute.AllSources.eq_def]
        exact ⟨generated.sources.1.source, generated.sources.1.source, trivial⟩
      · intro boxed member
        rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
        subst boxed
        exact sourceGenerated
    have rightShape : consumed.seed.info.type.instL consumed.seed.seed =
        (VExpr.forallE right.A right.B).subst right.raw := shape.trans subst_id.symm
    let last := RawGeneratedTypeRoute.sameExpression
      (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
      consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
    have lastGenerated : last.SourceGenerated P base caps :=
      RetainedHeaderUniverse.source_same _ _ _ _ _ _ _
        (consumed.seed.origin.sourceBelow.trans below) (consumed.seed.origin.sourceBelow.trans below)
        headerSource headerSource headerGenerated
    let selected := piPrefix
      ((Located.here (root := (consumed.seed.origin.familyHeader consumed.seed.seedWF).reference)).castExpression shape)
    let domain := Classical.choose selected.view.location.originalDomains.1
    have domainEq := Classical.choose_spec selected.view.location.originalDomains.1
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
      ⟨ordered, consumed.seed.origin.ordered, below, domain, domainEq, sourceFrame, headerFrame,
        first.trans (initialRoute.trans last)⟩
    have wholeGenerated : history.whole.SourceGenerated P base caps :=
      RetainedHeaderUniverse.source_trans firstGenerated
        (RetainedHeaderUniverse.source_trans initialGenerated lastGenerated)
    let firstInputs : first.WorldInputs strata := (controls, controls, sourceWorld, sourceWorld)
    let headerWorld := transportWorld
      (RetainedHeaderUniverse.nativeFrame_environment consumed.seed.origin consumed.seed.seedWF shape common
        env registry target commonLeft commonRight).symm
      (WorldEnvironmentProvenance.nil (strata := strata) (U := U))
    let lastInputs := sameExpression_worldInputs
      (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
      consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
      (controls.atHeader consumed.seed.origin) (controls.atHeader consumed.seed.origin) .nil headerWorld
    let lastBoundary := RawGeneratedTypeRoute.sameExpression_worldBoundary
      (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
      consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
      (controls.atHeader consumed.seed.origin) (controls.atHeader consumed.seed.origin) .nil headerWorld ⟨rfl, rfl⟩
    let boundary : history.whole.WorldBoundary
        (trans_worldInputs firstInputs (trans_worldInputs initialInputs lastInputs))
        controls (controls.atHeader consumed.seed.origin) sourceWorld headerWorld :=
      .trans (.same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩) (.trans initialBoundary lastBoundary)
    let sourceOccurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
      ⟨sourceFrame.box, controls, sourceWorld⟩
    let emptyOccurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
      ⟨(RetainedHeaderUniverse.frame consumed.seed.origin consumed.seed.seedWF common env registry target commonLeft commonRight).box,
        controls.atHeader consumed.seed.origin, .nil⟩
    have boundaryFrames : boundary.frames = [sourceOccurrence] ++
        ([sourceOccurrence, emptyOccurrence, emptyOccurrence, emptyOccurrence] ++ [emptyOccurrence]) := by
      simp only [boundary, boundaryFrames_trans]
      apply append_eq
      · rfl
      · apply append_eq
        · exact initialFrames
        · calc
            lastBoundary.frames = [⟨headerFrame.box, controls.atHeader consumed.seed.origin, headerWorld⟩] :=
              RawGeneratedTypeRoute.sameExpression_worldBoundary_frames
                (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
                consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
                (controls.atHeader consumed.seed.origin) (controls.atHeader consumed.seed.origin) .nil headerWorld ⟨rfl, rfl⟩
            _ = [emptyOccurrence] := congrArg (fun occurrence => [occurrence])
              (nativeOccurrence_eq controls consumed.seed.origin consumed.seed.seedWF shape common registry target commonLeft commonRight)
    have boundaryOccurrences : ∀ occurrence ∈ boundary.frames,
        occurrence = sourceOccurrence ∨ occurrence = emptyOccurrence := by
      intro occurrence member
      rw [boundaryFrames] at member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      rcases member with same | same
      · exact .inl same
      · rcases same with same | same
        · exact same
        · exact .inr same
    obtain ⟨frameControls, frameGenerated, coherent, properties⟩ :=
      sourceHeader_frameCoherent sourceFrame controls sourceWorld consumed.seed.origin consumed.seed.seedWF
        below headerSource sourceWorldGenerated sourceReplayable sourceReady sourceCompatible sourceCovered
        boundary boundaryOccurrences
    refine ⟨A, domains, rfl, shape, history,
      ⟨sourceGenerated.ambientGenerated, headerGenerated.ambientGenerated, wholeGenerated.ambientGenerated⟩,
      wholeGenerated, headerGenerated, rfl,
      RetainedHeaderUniverse.nativeFrame_environment _ _ _ _ _ _ _ _ _,
      consumed.seed.origin.sourceBelow.trans below, rfl, rfl,
      trans_worldInputs firstInputs (trans_worldInputs initialInputs lastInputs), ?_,
      assignedFamilyRouteFrame_environment major initial graph 0 rfl frame ordered,
      headerWorld, ?_, boundary, frameControls, frameGenerated, coherent, properties⟩
    · rw [trans_worldReserve, trans_worldReserve]
      apply Sponsored.merge
      · rw [same_worldReserve]
        simp only [sourceWorld, transportWorld_call]
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
            (.appPiFormation left.location) controls captured _ _⟩
        · cases List.mem_singleton.mp member
          exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
            (.assignedFormation (.appFunction left.location)) controls captured _ _⟩
      · apply Sponsored.merge
        · rw [initialWorlds]
          apply Sponsored.merge
          · simp only [sourceWorld, transportWorld_call]
            intro child member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                (.appFunction left.location) controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                ((constantPrefix _).route.locate (.appFunction left.location)) controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                (.assignedFormation ((constantPrefix _).route.locate (.appFunction left.location)))
                controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
                _ outer captured _ _⟩
          · exact RetainedHeaderUniverse.worldReserve_sponsored controls consumed.seed.origin consumed.seed.origin
              selection.seedWF consumed.seed.seedWF equivalent below common registry target
              commonLeft commonRight outer captured .assignedComparison
        · erw [sameExpression_worldReserve]
          simp only [headerWorld, transportWorld_call]
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
              _ outer captured _ _⟩
          · cases List.mem_singleton.mp member
            exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
              _ outer captured _ _⟩
    · exact transportWorld_worlds _ _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
