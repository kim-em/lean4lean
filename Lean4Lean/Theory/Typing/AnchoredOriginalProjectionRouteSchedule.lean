import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteLedger

/-! The stored parameter route ledger is paid by the production projection
origin. Its seed packet comes from the actual original major; the requested
packet is the actual registered constructor header and parameter roots. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure OriginalRecordSource
set_option backward.isDefEq.respectTransparency false

noncomputable def projectionRouteSources
    {levels : List VLevel}
    (formed : env.Ordered) (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (field : EndpointRef env U source fieldExpression fieldType)
    (major : EndpointRef env U source majorExpression majorType)
    (seed : ParameterRouteHeader env U) : ParameterRouteSources env U :=
  let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
  { ordered := formed
    source := source
    fieldExpression := fieldExpression
    fieldType := fieldType
    majorExpression := majorExpression
    majorType := majorType
    field := field
    major := major
    seed := seed
    requested :=
      { sourceEnv := header.source
        ordered := header.ordered
        source := []
        expression := _
        assigned := _
        header := .left header.original
        roots := projectionParameterDependencies formed registered levelsWF } }

theorem projection_route_charges_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seed : ParameterRouteHeader env U)
    (seedBound : seed.weight ≤ (major.dependencyOrigin formed).weight)
    (initial : List Closure)
    (charges : ParameterRouteCharges
      (projectionRouteSources formed registered levelsWF field (.left major) seed) initial count reserve)
    (countBound : count ≤ info.nparams + max info.nindices index) :
    richSchedule .expressionReindex (environmentCost reserve) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
          selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  have bound := charges.projection_reserve_bound seedBound countBound
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt bound
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [projectionRouteSources, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin,
    Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    reserveOrigin_weight, parameterWeights]
  omega

/-- All finite R, assigned-C and original equality-F edges in the actual
route are strictly smaller than the original projection fundamental call.
The bound includes all routes retained by earlier captured slots. -/
theorem projection_type_route_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seed : ParameterRouteHeader env U)
    (seedBound : seed.weight ≤ (major.dependencyOrigin formed).weight)
    (initial : List Closure)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute targetEnv registry target commonLeft commonRight left right first last)
    (charged : route.Charged
      (projectionRouteSources formed registered levelsWF field (.left major) seed) initial count)
    (countBound : count ≤ info.nparams + max info.nindices index) :
    route.schedule < richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  exact Nat.lt_of_le_of_lt route.schedule_le
    (projection_route_charges_schedule formed registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed allowed seed seedBound initial (route.chargedReserve charged) countBound)

/-- An actual occurrence path lifts the route bound to its original root;
no independent upper bound on that parent is supplied. -/
theorem projection_type_route_located_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seed : ParameterRouteHeader env U)
    (seedBound : seed.weight ≤ (major.dependencyOrigin formed).weight)
    {root : EndpointRef env U rootSource rootExpression rootType}
    (location : Located root (EndpointState.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF (.ref field) major closed allowed))
    (initial : List Closure)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute targetEnv registry target commonLeft commonRight left right first last)
    (charged : route.Charged
      (projectionRouteSources formed registered levelsWF field (.left major) seed)
      (location.dependencyEnvironment formed initial) count)
    (countBound : count ≤ info.nparams + max info.nindices index) :
    route.schedule < richSchedule .fundamental (Closure.close (root.dependencyOrigin formed) initial).cost := by
  have localBound := projection_type_route_schedule formed registered levelsWF levelCount parameterCount
    indexCount selected fieldWF field major closed allowed seed seedBound
    (location.dependencyEnvironment formed initial) route charged countBound
  apply Nat.lt_of_lt_of_le localBound
  change 3 * _ + 0 ≤ 3 * _ + 0
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (location.dependency_cost_le formed initial)) 0

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
