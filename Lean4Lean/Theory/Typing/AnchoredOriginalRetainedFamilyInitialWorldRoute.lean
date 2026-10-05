import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteBoundary
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyInitialRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateParameterWorldCalls

/-! Initial family history retains the caller's actual source ledger and
computes its declaration inputs at the inherited cutoff/fuel. Its phase-aware
reserve is read from the SAME route, rather than reconstructed from costs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private environment_worlds_mpr sameExpression_worldInputs sameExpression_worldReserve
  trans_worldInputs trans_worldReserve from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem append_eq {α : Type} {a b c d : List α}
    (first : a = b) (second : c = d) : a ++ c = b ++ d := by
  cases first
  cases second
  rfl

private theorem boundaryFrames_trans
    {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
    {lc : OriginalWorldControls strata left.sourceEnv} {mc : OriginalWorldControls strata middle.sourceEnv}
    {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial}
    {mw : WorldEnvironmentProvenance strata U intermediate}
    {rw : WorldEnvironmentProvenance strata U final}
    (a : first.WorldBoundary firstInputs lc mc lw mw) (b : second.WorldBoundary secondInputs mc rc mw rw) :
    (RawGeneratedTypeRoute.WorldBoundary.trans a b).frames = a.frames ++ b.frames := rfl

/-- Literal endpoint transport changes no execution annotation. -/
noncomputable def RawGeneratedTypeRoute.sameExpression_worldBoundary
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
    (compatible : leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).WorldBoundary
      (sameExpression_worldInputs left right same lf rf initial frame leftControls rightControls leftWorld rightWorld)
      leftControls rightControls leftWorld rightWorld := by
  cases same
  exact .same _ _ _ _ _ _ _ _ _ compatible

theorem RawGeneratedTypeRoute.sameExpression_worldBoundary_frames
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
    (compatible : leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel) :
    (RawGeneratedTypeRoute.sameExpression_worldBoundary left right same lf rf initial frame leftControls rightControls
      leftWorld rightWorld compatible).frames = [⟨frame.box, rightControls, rightWorld⟩] := by
  cases same
  rfl

/-- The actual universe bridge executes its R/F/R leaves at their retained
empty frames with the caller's unchanged control prefix. -/
noncomputable def RetainedHeaderUniverse.worldBoundary
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (RetainedHeaderUniverse.route leftOrigin rightOrigin leftWF rightWF equivalent below
      common registry target left right).WorldBoundary
      (RetainedHeaderUniverse.worldInputs controls leftOrigin rightOrigin leftWF rightWF equivalent below
        common registry target left right)
      (controls.atHeader leftOrigin) (controls.atHeader rightOrigin) .nil .nil := by
  exact .trans
    (RawGeneratedTypeRoute.sameExpression_worldBoundary _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩)
    (.trans (.equality _ _ _ _ _ _ _)
      (RawGeneratedTypeRoute.sameExpression_worldBoundary _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩))

theorem RetainedHeaderUniverse.worldBoundary_frames
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (RetainedHeaderUniverse.worldBoundary controls leftOrigin rightOrigin leftWF rightWF equivalent below
      common registry target left right).frames =
      [⟨(RetainedHeaderUniverse.frame rightOrigin rightWF common env registry target left right).box,
        controls.atHeader rightOrigin, .nil⟩,
       ⟨(RetainedHeaderUniverse.frame rightOrigin rightWF common env registry target left right).box,
        controls.atHeader rightOrigin, .nil⟩] := by
  let empty : WorldBoundaryFrame env U registry target common left right strata :=
    ⟨(RetainedHeaderUniverse.frame rightOrigin rightWF common env registry target left right).box,
      controls.atHeader rightOrigin, .nil⟩
  simp only [RetainedHeaderUniverse.worldBoundary, boundaryFrames_trans]
  change _ = [empty] ++ ([] ++ [empty])
  apply append_eq
  · exact RawGeneratedTypeRoute.sameExpression_worldBoundary_frames
      (RetainedHeaderUniverse.display leftOrigin leftWF common)
      ((closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common).typeEqualityDisplay
        (RetainedHeaderUniverse.original rightOrigin leftWF rightWF equivalent) true)
      subst_id.symm leftOrigin.ordered rightOrigin.ordered []
      (closedTypeRouteFrame .nil common env registry target left right)
      (controls.atHeader leftOrigin) (controls.atHeader rightOrigin) .nil .nil ⟨rfl, rfl⟩
  · apply append_eq
    · rfl
    · exact RawGeneratedTypeRoute.sameExpression_worldBoundary_frames
        ((closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common).typeEqualityDisplay
          (RetainedHeaderUniverse.original rightOrigin leftWF rightWF equivalent) false)
        (RetainedHeaderUniverse.display rightOrigin rightWF common)
        subst_id rightOrigin.ordered rightOrigin.ordered []
        (RetainedHeaderUniverse.frame rightOrigin rightWF common env registry target left right)
        (controls.atHeader rightOrigin) (controls.atHeader rightOrigin) .nil .nil ⟨rfl, rfl⟩

private theorem assigned_worldReserve
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List OriginalClosureMeasure.Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    ((RawGeneratedTypeRoute.assigned left right lf rf initial frame).worldReserve
      (leftControls, rightControls, leftWorld, rightWorld)).worlds =
      [originalCallWorld leftControls .assignedComparison left.node leftWorld,
       originalCallWorld rightControls .assignedComparison right.node rightWorld] := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.assigned left right lf rf initial frame))]
  rfl

theorem retainedFamilyInitialWorldRoute
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
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw)
    (headerSource : P origin.source) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels controls.ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin controls.ordered).weight ∧
      ∃ seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
        (RetainedHeaderUniverse.display origin queryWF common)
        (sourceFrame.realization.frame.dependencyEnvironment controls.ordered) [],
        route.SourceGenerated P base caps ∧
        ∃ inputs : route.WorldInputs strata,
          (route.worldReserve inputs).worlds =
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
          ∃ boundary : route.WorldBoundary inputs controls (controls.atHeader origin) sourceWorld .nil,
            boundary.frames =
              [⟨sourceFrame.box, controls, sourceWorld⟩,
               ⟨(RetainedHeaderUniverse.frame origin queryWF common env registry target commonLeft commonRight).box,
                 controls.atHeader origin, .nil⟩,
               ⟨(RetainedHeaderUniverse.frame origin queryWF common env registry target commonLeft commonRight).box,
                 controls.atHeader origin, .nil⟩,
               ⟨(RetainedHeaderUniverse.frame origin queryWF common env registry target commonLeft commonRight).box,
                 controls.atHeader origin, .nil⟩] := by
  let packet := constantPrefix node
  obtain ⟨selection, ledger, assignedEq, _nodeBound, rootBound⟩ := locatedHeaderSelection_retained controls.ordered location
  have sameInfo : selection.info = info := Option.some.inj (selection.lookup.symm.trans origin.constant)
  have seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      selection.equivalent (Lean4Lean.List.Forall₂.imp (fun _ _ equivalent => equivalent.symm)
        (Lean4Lean.List.Forall₂.flip queryEquivalent))
  let first := OriginalNestedDisplay.ofOccurrence initial location graph
  let last := originalPrefixDisplay initial location graph packet.route
  let compare := RawGeneratedTypeRoute.assigned first last controls.ordered controls.ordered
    (sourceFrame.realization.frame.dependencyEnvironment controls.ordered) sourceFrame
  have sourceP : P sourceEnv := generated.sources.1.source
  have compareGenerated : compare.SourceGenerated P base caps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
    · rw [RawGeneratedTypeRoute.AllSources.eq_def]; exact ⟨sourceP, sourceP, trivial⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact generated
  let header := RetainedHeaderUniverse.display origin selection.seedWF common
  have typeEq : packet.type.subst raw = info.type.instL selection.seed := by
    rw [assignedEq, sameInfo, (controls.ordered.closedC origin.constant).instL.subst_eq (σ := raw) .zero]
  let reindex := RawGeneratedTypeRoute.sameExpression last.formationDisplay header typeEq
    controls.ordered origin.ordered (sourceFrame.realization.frame.dependencyEnvironment controls.ordered)
    (RetainedHeaderUniverse.frame origin selection.seedWF common env registry target commonLeft commonRight)
  have reindexGenerated : reindex.SourceGenerated P base caps :=
    RetainedHeaderUniverse.sourceGenerated_same _ _ _ _ _ _ _ below (origin.sourceBelow.trans below)
      sourceP headerSource (.empty common commonLeft commonRight (origin.sourceBelow.trans below) headerSource)
  let adjust := RetainedHeaderUniverse.route origin origin selection.seedWF queryWF seedEquivalent
    below common registry target commonLeft commonRight
  have adjustGenerated := RetainedHeaderUniverse.route_sourceGenerated (base := base) origin origin selection.seedWF queryWF
    seedEquivalent below below common caps commonLeft commonRight headerSource headerSource
  let compareInputs : compare.WorldInputs strata := by
    change OriginalWorldControls strata sourceEnv × OriginalWorldControls strata sourceEnv ×
      WorldEnvironmentProvenance strata U (sourceFrame.realization.frame.dependencyEnvironment controls.ordered) ×
      WorldEnvironmentProvenance strata U (sourceFrame.realization.frame.dependencyEnvironment controls.ordered)
    exact ⟨controls, controls, sourceWorld, sourceWorld⟩
  let reindexInputs := sameExpression_worldInputs last.formationDisplay header typeEq
    controls.ordered origin.ordered (sourceFrame.realization.frame.dependencyEnvironment controls.ordered)
    (RetainedHeaderUniverse.frame origin selection.seedWF common env registry target commonLeft commonRight)
    controls (controls.atHeader origin) sourceWorld .nil
  let adjustInputs := RetainedHeaderUniverse.worldInputs controls origin origin selection.seedWF queryWF seedEquivalent
    below common registry target commonLeft commonRight
  refine ⟨selection, ledger, rootBound, seedEquivalent, compare.trans (reindex.trans adjust),
    RetainedHeaderUniverse.sourceGenerated_trans compareGenerated
      (RetainedHeaderUniverse.sourceGenerated_trans reindexGenerated adjustGenerated),
    trans_worldInputs compareInputs (trans_worldInputs reindexInputs adjustInputs), ?_, ?_⟩
  · rw [trans_worldReserve, trans_worldReserve]
    simp only [compareInputs, id_eq]
    erw [assigned_worldReserve, sameExpression_worldReserve]
    rfl
  · let boundary : (compare.trans (reindex.trans adjust)).WorldBoundary
        (trans_worldInputs compareInputs (trans_worldInputs reindexInputs adjustInputs))
        controls (controls.atHeader origin) sourceWorld .nil :=
      .trans (.assigned _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩)
        (.trans (RawGeneratedTypeRoute.sameExpression_worldBoundary _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩)
          (RetainedHeaderUniverse.worldBoundary controls origin origin selection.seedWF queryWF seedEquivalent
            below common registry target commonLeft commonRight))
    refine ⟨boundary, ?_⟩
    let empty : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
      ⟨(RetainedHeaderUniverse.frame origin queryWF common env registry target commonLeft commonRight).box,
        controls.atHeader origin, .nil⟩
    simp only [boundary, boundaryFrames_trans]
    change _ = [⟨sourceFrame.box, controls, sourceWorld⟩] ++ ([empty] ++ [empty, empty])
    apply append_eq
    · rfl
    · apply append_eq
      · exact RawGeneratedTypeRoute.sameExpression_worldBoundary_frames last.formationDisplay header typeEq
          controls.ordered origin.ordered (sourceFrame.realization.frame.dependencyEnvironment controls.ordered)
          (RetainedHeaderUniverse.frame origin selection.seedWF common env registry target commonLeft commonRight)
          controls (controls.atHeader origin) sourceWorld .nil ⟨rfl, rfl⟩
      · exact RetainedHeaderUniverse.worldBoundary_frames controls origin origin selection.seedWF queryWF
          seedEquivalent below common registry target commonLeft commonRight

/-- Initial execution has one caller frame and three uses of the SAME
empty declaration frame. The per-box dictionary is lawful here because the
caller and header sources are distinct and the repeated header annotations
are literally identical. -/
theorem initialWorldBoundary_frameCoherent
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
    (occurrences : boundary.frames =
      [⟨sourceFrame.box, controls, sourceWorld⟩,
       ⟨(RetainedHeaderUniverse.frame origin levelsWF common env registry target commonLeft commonRight).box,
         controls.atHeader origin, .nil⟩,
       ⟨(RetainedHeaderUniverse.frame origin levelsWF common env registry target commonLeft commonRight).box,
         controls.atHeader origin, .nil⟩,
       ⟨(RetainedHeaderUniverse.frame origin levelsWF common env registry target commonLeft commonRight).box,
         controls.atHeader origin, .nil⟩]) :
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
    rw [← boundary.frames_boxes, occurrences] at member
    simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
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
    rw [occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    rcases member with rfl | rfl
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

/-- The complete initial family reserve is paid by its actual outer
projection. Source-prefix calls use proper original descendants; all retained
declaration calls use their actual earlier sources. -/
theorem retainedFamilyInitialWorldRoute_sponsored
    {U : Nat} {queryLevels levels : List VLevel} {P : VEnv → Prop}
    {outer : EndpointState sourceEnv U source (.proj projectedName index majorExpression) outerType}
    (head : ProjectionHead outer)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U source)
    (location : Located (.right head.major) node)
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
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw)
    (headerSource : P origin.source) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels controls.ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ ((EndpointRef.right head.major).dependencyOrigin controls.ordered).weight ∧
      ∃ _seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
        (RetainedHeaderUniverse.display origin queryWF common)
        (sourceFrame.realization.frame.dependencyEnvironment controls.ordered) [],
        route.SourceGenerated P base caps ∧
        ∃ inputs : route.WorldInputs strata,
          Sponsored [originalCallWorld controls .assignedComparison outer sourceWorld]
            (route.worldReserve inputs).worlds ∧
          Nonempty (route.WorldBoundary inputs controls (controls.atHeader origin) sourceWorld .nil) := by
  obtain ⟨selection, ledger, bound, equivalent, route, generatedRoute, inputs, worlds, boundary, _boundaryFrames⟩ :=
    retainedFamilyInitialWorldRoute initial location graph sourceFrame controls below sourceWorld
      origin queryWF queryEquivalent caps generated headerSource
  refine ⟨selection, ledger, bound, equivalent, route, generatedRoute, inputs, ?_, ⟨boundary⟩⟩
  rw [worlds]
  intro child member
  rcases List.mem_append.mp member with member | member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_singleton_self _,
        ProjectionHead.parameter_below head location controls sourceWorld _ _⟩
    · exact ⟨_, List.mem_singleton_self _,
        ProjectionHead.parameter_below head ((constantPrefix node).route.locate location) controls sourceWorld _ _⟩
    · exact ⟨_, List.mem_singleton_self _,
        ProjectionHead.parameter_below head (.assignedFormation ((constantPrefix node).route.locate location))
          controls sourceWorld _ _⟩
    · exact ⟨_, List.mem_singleton_self _,
        originalClosedHeader_below controls origin _ outer sourceWorld _ _⟩
  · exact RetainedHeaderUniverse.worldReserve_sponsored controls origin origin selection.seedWF queryWF
      equivalent below common registry target commonLeft commonRight outer sourceWorld
      .assignedComparison child member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
