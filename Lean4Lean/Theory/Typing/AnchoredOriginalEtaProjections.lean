import Lean4Lean.Theory.Typing.AnchoredOriginalFamilySpine

/-! Structure eta already retains an original typing of the constructor
applied to the projections. Its actual argument endpoints provide projection
origins; no typing derivation for a newly synthesized projection is needed.
Their assigned types remain the original inferred types, to be aligned with
the declaration header by the finite query replay.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- Select the actual projected-field argument in the original constructor
premise of structure eta. The endpoint includes its original conversions. -/
noncomputable def etaProjectionArgument
    {info : VProjectionInfo}
    (constructor : Derivation env U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j major))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j major))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields) :
    SpineArgument (.left constructor) source [] (.proj name index major) := by
  let view := spineView
    (parameters ++ (List.range info.numFields).map fun j => .proj name j major)
    (Located.here (root := .left constructor))
  apply view.arguments.get (parameters.length + index)
  simp [bound]

/-- Every queried projection is paid for by the retained constructor child
of the actual eta rule, independently of the observation query's size. -/
theorem etaProjectionArgument_schedule
    (registered : env.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation env U source expression expression
      (mkApps (.const name levels) parameters))
    (constructor : Derivation env U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => .proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields) (initial : List Closure) :
    schedule .fundamental
      (Closure.close (etaProjectionArgument constructor index bound).node.origin initial).cost <
      schedule .fundamental
        (Closure.close (Derivation.structEta registered parameterCount noIndices
          major constructor).origin initial).cost := by
  apply schedule_strict
  exact Nat.lt_of_le_of_lt ((etaProjectionArgument constructor index bound).cost_le initial)
    (original_child_same_environment (Origin.rule_child (by simp [EndpointRef.origin])) initial)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
