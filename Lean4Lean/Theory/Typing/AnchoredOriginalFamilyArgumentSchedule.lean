import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-! The actual same-value assigned-type comparison fits below the original
projection before constructing any declared-domain alignment or group. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem PendingRichCapture.projection_argument_coherence_schedule
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
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
    (pending : PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (initialContext : ContextDerivation sourceEnv U source)
    (argumentIndex : Nat) (argumentSelected : (params ++ indices)[argumentIndex]? = some argumentExpression)
    (argumentFrame : OriginalRichOccurrenceFrame
      (assignedFamilyApplication (.left major) argumentIndex argumentSelected).argument.location
      initialContext env registry target argumentLocals argumentLeft argumentRight argumentAvailable
      sourceOrdered ownerInitial) :
    richSchedule .assignedComparison
      ((Closure.close (pending.owner.node.dependencyOrigin sourceOrdered)
        (pending.frame.dependencyEnvironment sourceOrdered)).cost +
       (Closure.close ((assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.argument.dependencyOrigin sourceOrdered)
        (argumentFrame.frame.dependencyEnvironment sourceOrdered)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost := by
  apply richSchedule_strict
  have ownerBound := Nat.le_trans (pending.owner_cost_le sourceOrdered)
    (Dependency.groupedOwner_bound (pending.measureOwner sourceOrdered) ownerInitial)
  have argumentBound := argumentFrame.cost_le
  have pairBound := Nat.add_le_add ownerBound argumentBound
  apply Nat.lt_of_le_of_lt pairBound
  change ((field.dependencyOrigin sourceOrdered).weight + (major.dependencyOrigin sourceOrdered).weight) *
      (1 + environmentCost ownerInitial) + (major.dependencyOrigin sourceOrdered).weight *
      (1 + environmentCost ownerInitial) < _
  rw [← Nat.add_mul]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    projectionDependencyReserve]
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
