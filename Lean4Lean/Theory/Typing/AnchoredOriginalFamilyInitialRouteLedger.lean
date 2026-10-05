import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyInitialTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRouteLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOccurrenceTraversal
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteCharges

/-! The initial family history is charged at its actual occurrence in the
projection major. The same selected header and parameter ledger pay both
its occurrence edges and the retained declaration normalization. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- The source-to-primitive comparison and the primitive-formation-to-header
reindex retain actual major locations. Exposing the constant prefix adds no
source binders or hidden environment charge. -/
noncomputable def constantNormalizationPrefixReserve_charges
    (ordered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (field : EndpointRef sourceEnv U rootSource fieldExpression fieldType)
    (major : EndpointRef sourceEnv U rootSource majorExpression majorType)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located major node)
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (ledger : FamilyParameterLedger selection)
    (initial environment : List Closure)
    (bounded : environmentCost environment ≤ environmentCost (location.dependencyEnvironment ordered initial)) :
    ParameterRouteCharges
      (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader) initial 0
      (constantNormalizationPrefixReserve ordered node selection environment) := by
  let sources := projectionRouteSources ordered registered levelsWF field major ledger.routeHeader
  let packet := constantPrefix node
  let last := packet.route.locate location
  have lastBound : environmentCost environment ≤ environmentCost (last.dependencyEnvironment ordered initial) := by
    simpa only [last, PrefixRoute.locate_dependencyEnvironment] using bounded
  let firstOccurrence : ParameterRouteOwnerOccurrence sources node := .major location
  let lastOccurrence : ParameterRouteOwnerOccurrence sources (.ref packet.reference) := .major last
  let formationOccurrence : ParameterRouteOwnerOccurrence sources
      (EndpointState.ref packet.reference).typeFormation.node := .major (.assignedFormation last)
  let headerOccurrence : ParameterRouteOccurrence sources selection.header.ordered
      (.ref (.left selection.header.original)) := .seed (.headerOrigin .here)
  exact .cons (.ownerPair firstOccurrence lastOccurrence environment environment bounded lastBound)
    (.cons (.ownerReindex formationOccurrence environment lastBound headerOccurrence .empty) .nil)

/-- A counted initial history for a real projection. Its exact generated
route, empty declaration baseline, and every finite call reserve are returned
together; the caller supplies no selected header or numerical header weight. -/
theorem originalConstantNormalizationRoute_projection
    (ordered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U rootSource fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U rootSource sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (initial : ContextDerivation sourceEnv U rootSource)
    (location : Located (.left major) node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (below : sourceEnv ≤ env)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (generated : CappedCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (ownerInitial : List Closure)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial)) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      let sources := projectionRouteSources ordered registered levelsWF field (.left major) ledger.routeHeader
      ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
          (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
          (normalizedFamilyRouteSide packet positive common).display
          (frame.realization.frame.dependencyEnvironment ordered)
          ((normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
            packet.origin.baseOrdered),
        route.Generated base caps ∧
        route.Ambient ∧
        Nonempty (route.Charged sources ownerInitial 0) ∧
        Nonempty (ParameterRouteLedger sources ownerInitial 0
          ((normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
            packet.origin.baseOrdered)) ∧
        route.schedule < richSchedule .fundamental
          (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
            selected fieldWF (.ref field) major closed allowed).dependencyOrigin ordered) ownerInitial).cost := by
  obtain ⟨selection, ledger, retained, route, routeGenerated, routeAmbient, _framesAmbient, reserveEq⟩ :=
    originalConstantNormalizationRoute_reserve initial location graph frame ordered below registered positive caps generated
  let sources := projectionRouteSources ordered registered levelsWF field (.left major) ledger.routeHeader
  have prefixCharges := constantNormalizationPrefixReserve_charges ordered registered levelsWF
    field (.left major) location selection ledger ownerInitial
    (frame.realization.frame.dependencyEnvironment ordered) frameBound
  have normalizationCharges := (selection.normalizationRoute registered positive below common registry target
    commonLeft commonRight).chargedReserve
    (ledger.normalizationRoute_charged registered positive levelsWF below common registry target
      commonLeft commonRight field (.left major) ownerInitial)
  have charges : ParameterRouteCharges sources ownerInitial 0 route.reserve := by
    rw [reserveEq]
    exact prefixCharges.append normalizationCharges
  refine ⟨selection, ledger, retained, route, routeGenerated, routeAmbient, ⟨route.chargedOfReserve charges⟩, ?_, ?_⟩
  · exact ⟨ledger.normalizationRoute_initialLedger registered positive levelsWF common env registry target
      commonLeft commonRight field (.left major) ownerInitial⟩
  · exact Nat.lt_of_le_of_lt route.schedule_le
      (projection_route_charges_schedule ordered registered levelsWF levelCount parameterCount indexCount
        selected fieldWF field major closed allowed ledger.routeHeader
        (Nat.le_trans ledger.routeHeader_weight_le_pairWeight retained) ownerInitial charges (Nat.zero_le _))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
