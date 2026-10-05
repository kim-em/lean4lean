import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalFirstParameterCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRouteSchedule

/-! The initial family normalization is paid by the actual selected header
and the retained installation normalization root, at prefix count zero. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

noncomputable def FamilyParameterLedger.routeHeader
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : ParameterRouteHeader sourceEnv U where
  sourceEnv := selection.header.source
  ordered := selection.header.ordered
  source := []
  expression := _
  assigned := _
  header := .left selection.header.original
  roots := ledger.dependencies

theorem FamilyParameterLedger.routeHeader_weight
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : ledger.routeHeader.weight = ledger.weight := rfl

theorem FamilyParameterLedger.routeHeader_weight_le_pairWeight
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) : ledger.routeHeader.weight ≤ ledger.pairWeight :=
  ledger.weight_le_pairWeight

private theorem normalizedRouteFrame_empty
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (normalizedFamilyRouteFrame packet positive common env registry target left right).realization.frame.dependencyEnvironment
      packet.origin.baseOrdered = [] :=
  closedTypeRouteFrame_environment
    ((normalizedFamilyPrefix packet positive).selected.view.location.contextDerivation .nil)
    common packet.origin.baseOrdered

private noncomputable def sameExpressionCharged
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (charge : ParameterRouteCharge sources ownerInitial count
      (.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)))) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).Charged sources ownerInitial count := by
  cases same
  rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.Charged.eq_def]
  exact charge

/-- No root-membership or numerical charge is supplied: the normalization
is the first retained base root, and its native Pi is an actual right-child
occurrence of that very proof. -/
noncomputable def FamilyParameterLedger.normalizationRoute_charged
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (initial : List Closure) :
    (selection.normalizationRoute registered positive below common registry target left right).Charged
      (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader) initial 0 := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  let sources := projectionRouteSources ordered registered levelsWF field major ledger.routeHeader
  let root : ParameterEqualityRoot packet.origin.base U :=
    ⟨[], .nil, _, _, _, packet.instantiated.normalization⟩
  have member : packet.baseDependency root ∈ ledger.dependencies :=
    ledger.seedBase_mem registered root (List.mem_cons_self)
  let headerOccurrence : ParameterRouteOccurrence sources selection.header.ordered
      (.ref (.left selection.header.original)) := .seed (.headerOrigin .here)
  let leftOccurrence : ParameterRouteOccurrence sources packet.origin.baseOrdered
      (.ref (.left packet.instantiated.normalization)) :=
    .seed (.equalityLeft (packet.baseDependency root) member .here)
  let rightOccurrence : ParameterRouteOccurrence sources packet.origin.baseOrdered
      (.ref (.right packet.instantiated.normalization)) :=
    .seed (.equalityRight (packet.baseDependency root) member .here)
  let nativeOccurrence : ParameterRouteOccurrence sources packet.origin.baseOrdered
      (normalizedFamilyRouteSide packet positive common).display.node :=
    .seed (.equalityRight (packet.baseDependency root) member
      (normalizedFamilyPrefix packet positive).selected.view.location)
  unfold RichHeaderSelection.normalizationRoute
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  refine ⟨?_, ?_⟩
  · rw [RawGeneratedTypeRoute.Charged.eq_def]
    refine ⟨?_, ?_⟩
    · exact .reindex headerOccurrence leftOccurrence .empty .empty
    · exact .equality ⟨_, packet.origin.baseOrdered, [], _, _, _,
        packet.instantiated.normalization, leftOccurrence⟩ .empty
  · apply sameExpressionCharged
    exact .reindex rightOccurrence nativeOccurrence .empty
      (by
        exact (normalizedRouteFrame_empty packet positive common env registry target left right).symm ▸
          ParameterRouteLedger.empty)

/-- The normalization leaves the header prefix genuinely empty; later
applyPi captures start at count zero and advance this exact ledger. -/
noncomputable def FamilyParameterLedger.normalizationRoute_initialLedger
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (common : List VExpr) (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr) (left right : Subst)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (initial : List Closure) :
    ParameterRouteLedger
      (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader) initial 0
      ((normalizedFamilyRouteFrame (selectProjectionParameters ordered registered selection.seedWF) positive
        common env registry target left right).realization.frame.dependencyEnvironment
          (selectProjectionParameters ordered registered selection.seedWF).origin.baseOrdered) := by
  exact (normalizedRouteFrame_empty (selectProjectionParameters ordered registered selection.seedWF)
    positive common env registry target left right).symm ▸ ParameterRouteLedger.empty

/-- The actual seed selected from the major pays this initial route under
the production projection reserve, before any capture slot is introduced. -/
theorem FamilyParameterLedger.normalizationRoute_projection_schedule
    (ordered : sourceEnv.Ordered)
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (retained : ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (initial : List Closure) :
    (selection.normalizationRoute registered positive below common registry target left right).schedule <
      richSchedule .fundamental
        (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
          selected fieldWF (.ref field) major closed allowed).dependencyOrigin ordered) initial).cost := by
  exact projection_type_route_schedule ordered registered levelsWF levelCount parameterCount indexCount
    selected fieldWF field major closed allowed ledger.routeHeader
    (Nat.le_trans ledger.routeHeader_weight_le_pairWeight retained) initial _
    (ledger.normalizationRoute_charged registered positive levelsWF below common registry target left right
      field (.left major) initial) (Nat.zero_le _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
