import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyInitialRouteLedger

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

open private transportRouteFrame from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide

private theorem transportRouteFrame_ambient
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ambient : frame.Ambient) : (transportRouteFrame equal frame).Ambient := by
  cases equal
  exact ambient

/-- The first whole-Pi history starts at the actual first application in the
major's assigned family. The constant occurrence, original declaration seed,
normalization and native domain reference are all selected internally. -/
theorem firstFamilyApplyPiHistory_counted
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (ownerInitial : List Closure)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost ownerInitial)
    {base : OriginalCaptureBase env U registry target}
    (generated : CappedCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      let sources := projectionRouteSources ordered registered levelsWF field major ledger.routeHeader
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := normalizedFamilyRouteSide packet positive common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.Generated base caps ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.whole.Ambient ∧
        (frame.Ambient → history.whole.FramesAmbient) ∧
        Nonempty (history.whole.Charged sources ownerInitial 0) ∧
        Nonempty (ParameterRouteLedger sources ownerInitial 0 history.final) ∧
        Nonempty (ParameterRouteOccurrence sources history.rightOrdered right.display.node) ∧
        right.sourceEnv ≤ env ∧
        (.forallE right.A right.B) = packet.shape.normalized.instL selection.seed := by
  let left := assignedFamilyRouteSide major initial graph 0 rfl
  let sourceFrame := assignedFamilyRouteFrame major initial graph 0 rfl frame
  have sourceGenerated := assignedFamilyRouteFrame_generated major initial graph 0 rfl frame generated
  obtain ⟨selection, ledger, headerBound, route, routeGenerated, routeAmbient, routeFramesAmbient, reserveEq⟩ :=
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
  let sources := projectionRouteSources ordered registered levelsWF field major ledger.routeHeader
  have sourceBound : environmentCost (sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (left.location.dependencyEnvironment ordered ownerInitial) := by
    rw [Located.dependencyEnvironment_of_prefix_nil ordered left.location
      (assignedFamilyRouteSide_prefix major initial graph 0 rfl) ownerInitial]
    rw [assignedFamilyRouteFrame_environment]
    exact frameBound
  have firstCharged : first.Charged sources ownerInitial 0 := by
    rw [RawGeneratedTypeRoute.Charged.eq_def]
    let leftOccurrence : ParameterRouteOwnerOccurrence sources left.pi.display.node :=
      .major (.appPiFormation left.location)
    let rightOccurrence : ParameterRouteOwnerOccurrence sources
        (OriginalNestedDisplay.ofOccurrence left.initial (.appFunction left.location) left.graph).formationDisplay.node :=
      .major (.assignedFormation (.appFunction left.location))
    exact .ownerPair leftOccurrence rightOccurrence _ _ sourceBound sourceBound
  have prefixCharges := constantNormalizationPrefixReserve_charges ordered registered levelsWF
    field major (.appFunction left.location) selection ledger ownerInitial
    (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceBound
  have normalizationCharges := (selection.normalizationRoute registered positive below common registry target
    commonLeft commonRight).chargedReserve
      (ledger.normalizationRoute_charged registered positive levelsWF below common registry target
        commonLeft commonRight field major ownerInitial)
  have routeCharged : route.Charged sources ownerInitial 0 := by
    apply route.chargedOfReserve
    rw [reserveEq]
    exact prefixCharges.append normalizationCharges
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
    ⟨ordered, packet.origin.baseOrdered, below, (normalizedFamilyPrefix packet positive).domainOriginal,
      normalizedFamilyRouteSide_domain packet positive common, sourceFrame, headerFrame, first.trans route⟩
  refine ⟨selection, ledger, headerBound, history, ⟨sourceGenerated,
      normalizedFamilyRouteFrame_capped packet positive common caps commonLeft commonRight, ?_⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      exact ⟨firstGenerated.wellFormed, routeGenerated.wellFormed⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (routeGenerated.frames boxed)
  · change (first.trans route).Ambient
    rw [RawGeneratedTypeRoute.Ambient.eq_def]
    refine ⟨?_, routeAmbient⟩
    rw [RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨below, below⟩
  · intro ambient
    have sourceAmbient : sourceFrame.Ambient := transportRouteFrame_ambient _ frame ambient
    apply RawGeneratedTypeRoute.FramesAmbient.trans
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases List.mem_singleton.mp member
      exact sourceAmbient
    · exact routeFramesAmbient sourceAmbient
  · change Nonempty ((first.trans route).Charged sources ownerInitial 0)
    rw [RawGeneratedTypeRoute.Charged.eq_def]
    exact ⟨firstCharged, routeCharged⟩
  · exact ⟨ledger.normalizationRoute_initialLedger registered positive levelsWF common env registry target
      commonLeft commonRight field major ownerInitial⟩
  · let root : ParameterEqualityRoot packet.origin.base U :=
      ⟨[], .nil, _, _, _, packet.instantiated.normalization⟩
    have member : packet.baseDependency root ∈ ledger.dependencies :=
      ledger.seedBase_mem registered root (List.mem_cons_self)
    exact ⟨.seed (.equalityRight (packet.baseDependency root) member
      (normalizedFamilyPrefix packet positive).selected.view.location)⟩
  · exact packet.origin.baseBelow.trans below
  · exact (normalizedFamilyPrefix packet positive).shape.symm

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
