import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyInitialTypeRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- The first whole-Pi history starts at the actual first application in the
major's assigned family. The constant occurrence, original declaration seed,
normalization and native domain reference are all selected internally. -/
theorem firstFamilyApplyPiHistory
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    {base : OriginalCaptureBase env U registry target}
    (generated : CappedCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := normalizedFamilyRouteSide packet positive common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.Generated base caps ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        right.sourceEnv ≤ env ∧
        (.forallE right.A right.B) = packet.shape.normalized.instL selection.seed := by
  let left := assignedFamilyRouteSide major initial graph 0 rfl
  let sourceFrame := assignedFamilyRouteFrame major initial graph 0 rfl frame
  have sourceGenerated := assignedFamilyRouteFrame_generated major initial graph 0 rfl frame generated
  obtain ⟨selection, ledger, headerBound, route, routeGenerated, _ambient, _framesAmbient, _⟩ :=
    originalConstantNormalizationRoute_reserve left.initial (.appFunction left.location) left.graph sourceFrame
      ordered below registered positive caps sourceGenerated
  let packet := selectProjectionParameters ordered registered selection.seedWF
  let right := normalizedFamilyRouteSide packet positive common
  let headerFrame := normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight
  let first := RawGeneratedTypeRoute.same left.pi.display
    (OriginalNestedDisplay.ofOccurrence left.initial (.appFunction left.location) left.graph).formationDisplay
      ordered ordered (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceFrame
  have firstGenerated : first.Generated base caps := by
    refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact sourceGenerated
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
    ⟨ordered, packet.origin.baseOrdered, below, (normalizedFamilyPrefix packet positive).domainOriginal,
      normalizedFamilyRouteSide_domain packet positive common, sourceFrame, headerFrame, first.trans route⟩
  refine ⟨selection, ledger, headerBound, history, ⟨sourceGenerated,
      normalizedFamilyRouteFrame_capped packet positive common caps commonLeft commonRight, ?_⟩, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      exact ⟨firstGenerated.wellFormed, routeGenerated.wellFormed⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (routeGenerated.frames boxed)
  · exact packet.origin.baseBelow.trans below
  · exact (normalizedFamilyPrefix packet positive).shape.symm

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
