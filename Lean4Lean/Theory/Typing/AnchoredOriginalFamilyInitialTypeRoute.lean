import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyHeaderSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteFrameAmbient

/-! Build the initial finite family history from its actual constant
occurrence. Conversion prefixes retain their original term endpoints;
assigned comparison supplies the type edge to the computed primitive head. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- The two occurrence edges before the retained declaration normalization.
Both use the actual exposed constant, including its assigned formation. -/
noncomputable def constantNormalizationPrefixReserve
    (ordered : sourceEnv.Ordered)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (environment : List Closure) : List Closure :=
  [.bundle (.close (node.dependencyOrigin ordered) environment)
      (.close ((constantPrefix node).reference.dependencyOrigin ordered) environment),
   .bundle (.close ((EndpointState.ref (constantPrefix node).reference).typeFormation.node.dependencyOrigin ordered) environment)
      (.close (selection.header.original.dependencyOrigin selection.header.ordered) [])]

private theorem initial_trans_reserve
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
    (first.trans second).reserve = first.reserve ++ second.reserve := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem initial_assigned_reserve
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
    (RawGeneratedTypeRoute.assigned left right lf rf initial frame).reserve =
      [.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf))] := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

/-- Every actual family constant occurrence produces its initial normalized
header history. The declaration selection, all original endpoints and both
empty declaration baselines are computed here, before the requested query. -/
theorem originalConstantNormalizationRoute_reserve
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : CappedCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
          (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
          (normalizedFamilyRouteSide packet positive common).display
          (frame.realization.frame.dependencyEnvironment ordered)
          ((normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
            packet.origin.baseOrdered),
        route.Generated base caps ∧
        route.Ambient ∧
        (frame.Ambient → route.FramesAmbient) ∧
        route.reserve = constantNormalizationPrefixReserve ordered node selection
          (frame.realization.frame.dependencyEnvironment ordered) ++
          (selection.normalizationRoute registered positive below common registry target commonLeft commonRight).reserve := by
  let packet :=  constantPrefix node
  obtain ⟨selection, ledger, assignedEq, nodeBound, rootBound⟩ := locatedHeaderSelection_retained ordered location
  let first := OriginalNestedDisplay.ofOccurrence initial location graph
  let last := originalPrefixDisplay initial location graph packet.route
  let compare := RawGeneratedTypeRoute.assigned first last ordered ordered
    (frame.realization.frame.dependencyEnvironment ordered) frame
  have compareGenerated : compare.Generated base caps := by
    refine ⟨by rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial, ?_⟩
    intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
    subst boxed
    exact generated
  let header := selection.normalizationDisplay registered common
  have typeEq : packet.type.subst raw =
      ((selectProjectionParameters ordered registered selection.seedWF).origin.family.type.instL selection.seed).subst Subst.id := by
    have same : selection.info =
        (selectProjectionParameters ordered registered selection.seedWF).origin.family.toVConstant :=
      Option.some.inj (selection.lookup.symm.trans
        (selectProjectionParameters ordered registered selection.seedWF).origin.familyPresent)
    rw [assignedEq, (ordered.closedC selection.lookup).instL.subst_eq (σ := raw) .zero, subst_id]
    rw [same]
  let reindex := RawGeneratedTypeRoute.sameExpression last.formationDisplay header typeEq
    ordered selection.header.ordered (frame.realization.frame.dependencyEnvironment ordered)
    (selection.normalizationFrame registered common env registry target commonLeft commonRight)
  have reindexGenerated : reindex.Generated base caps :=
    RawGeneratedTypeRoute.sameExpression_generated _ _ _ _ _ _ _
      (closedTypeRouteFrame_capped .nil common caps commonLeft commonRight)
  let normalize := selection.normalizationRoute registered positive below common registry target commonLeft commonRight
  have normalizeGenerated := selection.normalizationRoute_generated (base := base) registered positive below common caps commonLeft commonRight
  refine ⟨selection, ledger, rootBound, .trans compare (.trans reindex normalize), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      refine ⟨compareGenerated.wellFormed, ?_⟩
      rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      exact ⟨reindexGenerated.wellFormed, normalizeGenerated.wellFormed⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      rcases List.mem_append.mp member with firstMember | restMember
      · exact compareGenerated.frames boxed firstMember
      · rw [RawGeneratedTypeRoute.frames.eq_def] at restMember
        rcases List.mem_append.mp restMember with middleMember | lastMember
        · exact reindexGenerated.frames boxed middleMember
        · exact normalizeGenerated.frames boxed lastMember
  · change (compare.trans (reindex.trans normalize)).Ambient
    rw [RawGeneratedTypeRoute.Ambient.eq_def]
    constructor
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]
      exact ⟨below, below⟩
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]
      constructor
      · exact RawGeneratedTypeRoute.sameExpression_ambient _ _ _ _ _ _ _ below
          (selection.headerBelow.trans below)
      · exact selection.normalizationRoute_ambient registered positive below common registry target
          commonLeft commonRight
  · intro ambient
    apply RawGeneratedTypeRoute.FramesAmbient.trans
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact ambient
    · apply RawGeneratedTypeRoute.FramesAmbient.trans
      · apply RawGeneratedTypeRoute.sameExpression_framesAmbient
        exact closedTypeRouteFrame_ambient .nil common (selection.headerBelow.trans below)
          registry target commonLeft commonRight
      · exact selection.normalizationRoute_framesAmbient registered positive below common registry target
          commonLeft commonRight
  · change (compare.trans (reindex.trans normalize)).reserve = _
    rw [initial_trans_reserve, initial_trans_reserve, initial_assigned_reserve,
      RawGeneratedTypeRoute.sameExpression_reserve]
    rfl

theorem originalConstantNormalizationRoute
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : CappedCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (root.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
          (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
          (normalizedFamilyRouteSide packet positive common).display
          (frame.realization.frame.dependencyEnvironment ordered)
          ((normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
            packet.origin.baseOrdered),
        route.Generated base caps := by
  obtain ⟨selection, ledger, retained, route, generated, _ambient, _framesAmbient, reserveEq⟩ :=
    originalConstantNormalizationRoute_reserve initial location graph frame ordered below registered positive caps generated
  exact ⟨selection, ledger, retained, route, generated⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
