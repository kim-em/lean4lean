import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyHeaderSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderSourceGeneration

/-! The actual constant prefix is connected to the header retained by the
incoming native family descriptor. Conversion prefixes and different universe
seeds retain their original proof edges; no normalization packet is selected. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem trans_reserve
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
    (first.trans second).reserve = first.reserve ++ second.reserve := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem assigned_reserve
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
    (RawGeneratedTypeRoute.assigned left right lf rf initial frame).reserve =
      [.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf))] := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

/-- Select the actual constDF seed, retain the caller's source graph, and
produce the complete original history to the incoming family's exact header.
The output retains every R/C/equality root and positive source-generation
evidence, before any requested richer parameter query is replayed. -/
theorem retainedFamilyInitialRouteAt
    {U : Nat} {queryLevels levels : List VLevel} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (sourceFrame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (origin : ConstantHeaderOrigin originEnv name info)
    (originBelow : originEnv ≤ env)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw)
    (headerSource : P origin.source) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin ordered).weight ∧
      ∃ seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
        (RetainedHeaderUniverse.display origin queryWF common)
        (sourceFrame.realization.frame.dependencyEnvironment ordered) [],
        route.SourceGenerated P base caps ∧
        route.reserve =
          [.bundle (.close (node.dependencyOrigin ordered) (sourceFrame.realization.frame.dependencyEnvironment ordered))
            (.close ((constantPrefix node).reference.dependencyOrigin ordered)
              (sourceFrame.realization.frame.dependencyEnvironment ordered)),
           .bundle (.close ((EndpointState.ref (constantPrefix node).reference).typeFormation.node.dependencyOrigin ordered)
              (sourceFrame.realization.frame.dependencyEnvironment ordered))
            (.close ((EndpointState.ref (origin.familyHeader selection.seedWF).reference).dependencyOrigin origin.ordered) [])] ++
          (RetainedHeaderUniverse.route origin origin selection.seedWF queryWF seedEquivalent
            originBelow common registry target commonLeft commonRight).reserve := by
  let packet := constantPrefix node
  obtain ⟨selection, ledger, assignedEq, _nodeBound, rootBound⟩ := locatedHeaderSelection_retained ordered location
  have sameInfo : selection.info = info :=
    Option.some.inj ((below.constants selection.lookup).symm.trans
      (originBelow.constants origin.constant))
  have typeClosed : info.type.Closed := by
    have closed := ordered.closedC selection.lookup
    simpa only [sameInfo] using closed
  have seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      selection.equivalent (Lean4Lean.List.Forall₂.imp (fun _ _ equivalent => equivalent.symm)
        (Lean4Lean.List.Forall₂.flip queryEquivalent))
  let first := OriginalNestedDisplay.ofOccurrence initial location graph
  let last := originalPrefixDisplay initial location graph packet.route
  let compare := RawGeneratedTypeRoute.assigned first last ordered ordered
    (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceFrame
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
    rw [assignedEq, sameInfo, typeClosed.instL.subst_eq (σ := raw) .zero]
  let reindex := RawGeneratedTypeRoute.sameExpression last.formationDisplay header typeEq
    ordered origin.ordered (sourceFrame.realization.frame.dependencyEnvironment ordered)
    (RetainedHeaderUniverse.frame origin selection.seedWF common env registry target commonLeft commonRight)
  have reindexGenerated : reindex.SourceGenerated P base caps :=
    RetainedHeaderUniverse.sourceGenerated_same _ _ _ _ _ _ _ below (origin.sourceBelow.trans originBelow)
      sourceP headerSource (.empty common commonLeft commonRight (origin.sourceBelow.trans originBelow) headerSource)
  let adjust := RetainedHeaderUniverse.route origin origin selection.seedWF queryWF seedEquivalent
    originBelow common registry target commonLeft commonRight
  have adjustGenerated := RetainedHeaderUniverse.route_sourceGenerated (base := base) origin origin selection.seedWF queryWF
    seedEquivalent originBelow originBelow common caps commonLeft commonRight headerSource headerSource
  refine ⟨selection, ledger, rootBound, seedEquivalent, compare.trans (reindex.trans adjust),
    RetainedHeaderUniverse.sourceGenerated_trans compareGenerated
      (RetainedHeaderUniverse.sourceGenerated_trans reindexGenerated adjustGenerated), ?_⟩
  rw [trans_reserve, trans_reserve, assigned_reserve, RawGeneratedTypeRoute.sameExpression_reserve]
  rfl


/-- The original caller-source API is the specialization of the independent
retained-header producer. -/
theorem retainedFamilyInitialRoute
    {U : Nat} {queryLevels levels : List VLevel} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (sourceFrame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph sourceFrame.realization.frame.raw)
    (headerSource : P origin.source) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin ordered).weight ∧
      ∃ seedEquivalent : List.Forall₂ (· ≈ ·) selection.seed queryLevels,
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
        (RetainedHeaderUniverse.display origin queryWF common)
        (sourceFrame.realization.frame.dependencyEnvironment ordered) [],
        route.SourceGenerated P base caps ∧
        route.reserve =
          [.bundle (.close (node.dependencyOrigin ordered) (sourceFrame.realization.frame.dependencyEnvironment ordered))
            (.close ((constantPrefix node).reference.dependencyOrigin ordered)
              (sourceFrame.realization.frame.dependencyEnvironment ordered)),
           .bundle (.close ((EndpointState.ref (constantPrefix node).reference).typeFormation.node.dependencyOrigin ordered)
              (sourceFrame.realization.frame.dependencyEnvironment ordered))
            (.close ((EndpointState.ref (origin.familyHeader selection.seedWF).reference).dependencyOrigin origin.ordered) [])] ++
          (RetainedHeaderUniverse.route origin origin selection.seedWF queryWF seedEquivalent
            below common registry target commonLeft commonRight).reserve := by
  exact retainedFamilyInitialRouteAt initial location graph sourceFrame ordered below origin below
    queryWF queryEquivalent caps generated headerSource

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
