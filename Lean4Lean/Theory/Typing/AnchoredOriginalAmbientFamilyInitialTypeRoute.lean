import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyNormalizationRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyInitialTypeRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private initial_trans_reserve initial_assigned_reserve from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyInitialTypeRoute
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem originalConstantNormalizationRouteAmbient_reserve
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw) :
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
        route.AmbientGenerated base caps ∧
        route.reserve = constantNormalizationPrefixReserve ordered node selection
          (frame.realization.frame.dependencyEnvironment ordered) ++
          (selection.normalizationRoute registered positive below common registry target commonLeft commonRight).reserve := by
  let packet :=  constantPrefix node
  obtain ⟨selection, ledger, assignedEq, nodeBound, rootBound⟩ := locatedHeaderSelection_retained ordered location
  let first := OriginalNestedDisplay.ofOccurrence initial location graph
  let last := originalPrefixDisplay initial location graph packet.route
  let compare := RawGeneratedTypeRoute.assigned first last ordered ordered
    (frame.realization.frame.dependencyEnvironment ordered) frame
  have compareGenerated : compare.AmbientGenerated base caps := by
    refine ⟨by rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
    · intro boxed member
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
  have reindexGenerated : reindex.AmbientGenerated base caps :=
    RawGeneratedTypeRoute.sameExpression_ambientGenerated _ _ _ _ _ _ _ below
      (closedTypeRouteFrame_ambientGenerated .nil common caps commonLeft commonRight (selection.headerBelow.trans below))
  let normalize := selection.normalizationRoute registered positive below common registry target commonLeft commonRight
  have normalizeGenerated := selection.normalizationRoute_ambientGenerated (base := base) registered positive below common caps commonLeft commonRight
  refine ⟨selection, ledger, rootBound, .trans compare (.trans reindex normalize),
    compareGenerated.trans (reindexGenerated.trans normalizeGenerated), ?_⟩
  change (compare.trans (reindex.trans normalize)).reserve = _
  rw [initial_trans_reserve, initial_trans_reserve, initial_assigned_reserve,
      RawGeneratedTypeRoute.sameExpression_reserve]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
