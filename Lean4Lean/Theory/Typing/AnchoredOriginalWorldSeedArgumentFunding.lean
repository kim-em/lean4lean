import Lean4Lean.Theory.Typing.AnchoredOriginalSeedArgumentProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerReplayFunding

/-! Seed reindexing spends a strictly larger original application ancestor,
not a same-key copy of the seed owner. Captures may be reorganized and
repeated: their hereditary coverage is used independently of strict cost. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem argument_below_root
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.app hu hv domain body function argument result))
    (controls : OriginalWorldControls strata sourceEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (capacity : environmentCost selectedEnvironment ≤
      environmentCost (location.dependencyEnvironment controls.ordered ownerInitial))
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selected.worlds (initial.located controls (.appArgument location)).worlds) :
    WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex argument selected)
      (originalCallWorld controls .expressionReindex (.ref root) initial) := by
  have selectedCost : (Closure.close (argument.dependencyOrigin controls.ordered) selectedEnvironment).cost ≤
      (Closure.close (argument.dependencyOrigin controls.ordered)
        (location.dependencyEnvironment controls.ordered ownerInitial)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)
  have proper : (Closure.close (argument.dependencyOrigin controls.ordered)
      (location.dependencyEnvironment controls.ordered ownerInitial)).cost <
      (Closure.close (root.dependencyOrigin controls.ordered) ownerInitial).cost :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _)
      (application_cost_le_captured _ _ _ _ _ _))
      (location.dependency_cost_le controls.ordered ownerInitial)
  exact .root (EquationControlMeasure.scheduleDecrease
    (richSchedule_strict (Nat.lt_of_le_of_lt selectedCost proper) .expressionReindex .expressionReindex) _ _ _ _)
    (covered.below EquationControlMeasure.less_trans
      (initial.located_captures_belowAt controls (.appArgument location) .expressionReindex))

/-- The exact seed R call is strictly below one of the retained field/major
R roots. No equal-key world monotonicity is used. -/
theorem HeaderOwner.Argument.reindex_below_root
    {strata : EquationStratification env} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {owner : HeaderOwner field major}
    (argument : owner.Argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (capacity : environmentCost selectedEnvironment ≤
      environmentCost (owner.dependencyEnvironment controls.ordered ownerInitial))
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selected.worlds (owner.worldEnvironment controls initial).worlds) :
    ∃ root ∈ [originalCallWorld controls .expressionReindex (.ref field) initial,
      originalCallWorld controls .expressionReindex (.ref major) initial],
      WorldBelow strata.rules.length (originalCallWorld controls .expressionReindex owner.node selected) root := by
  cases argument with
  | inl location =>
    exact ⟨_, List.mem_cons_self, argument_below_root location controls initial selected capacity covered⟩
  | inr location =>
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      argument_below_root location controls initial selected capacity covered⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
