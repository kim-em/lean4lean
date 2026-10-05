import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! Actual original-path coverage. Binder captures carry their real original
domain worlds. A path with no binders can retain the root itself, so coverage
is non-strict; any outer sponsor remains strict by transitivity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem location_binder_cost_lt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (ordered : sourceEnv.Ordered) (location : Located root node) (initial : List OriginalClosureMeasure.Closure)
    (nonempty : location.binderPrefix ≠ []) :
    (OriginalClosureMeasure.Closure.close (node.dependencyOrigin ordered)
      (location.dependencyEnvironment ordered initial)).cost <
      (OriginalClosureMeasure.Closure.close (root.dependencyOrigin ordered) initial).cost := by
  induction location with
  | here => exact (nonempty rfl).elim
  | expose parent ih =>
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right (1 + environmentCost (parent.dependencyEnvironment ordered initial))
        (EndpointRef.expose_dependency_weight_le ordered _)) (ih nonempty)
  | assignedFormation parent ih =>
    exact Nat.lt_of_le_of_lt (EndpointState.typeFormation_dependency_cost_le ordered _ _) (ih nonempty)
  | appPiFormation parent ih =>
    exact Nat.lt_of_lt_of_le
      (EndpointState.appPiFormation_dependency_cost_lt ordered _ _ _ _ _ _ _ _)
      (parent.dependency_cost_le ordered initial)
  | convertTerm parent ih | projField parent ih | projMajor parent ih =>
    exact Nat.lt_of_lt_of_le (original_child_same_environment
      (Origin.rule_child (by simp [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin])) _)
      (parent.dependency_cost_le ordered initial)
  | appFunction parent ih | appArgument parent ih | appResult parent ih =>
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _)
      (application_cost_le_captured _ _ _ _ _ _)) (parent.dependency_cost_le ordered initial)
  | appDomain parent ih =>
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _)
      (application_cost_le_captured _ _ _ _ _ _)) (parent.dependency_cost_le ordered initial)
  | appCodomain parent ih =>
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_body_cost (by simp) _)
      (application_cost_le_captured _ _ _ _ _ _)) (parent.dependency_cost_le ordered initial)
  | lamDomain parent ih | piDomain parent ih =>
    exact Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _) (parent.dependency_cost_le ordered initial)
  | lamBody parent ih | lamCodomain parent ih | piBody parent ih =>
    exact Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) (parent.dependency_cost_le ordered initial)

private theorem located_worlds_nil
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (controls : OriginalWorldControls strata sourceEnv) (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured)
    (empty : location.binderPrefix = []) :
    (initial.located controls location).worlds = initial.worlds := by
  induction location with
  | here => rfl
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih
  | appDomain parent ih | appResult parent ih | appPiFormation parent ih
  | lamDomain parent ih | piDomain parent ih | projField parent ih | projMajor parent ih
  | assignedFormation parent ih => exact ih empty
  | lamBody parent ih | lamCodomain parent ih | appCodomain parent ih | piBody parent ih =>
    cases empty

theorem WorldEnvironmentProvenance.located_captures_belowAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (controls : OriginalWorldControls strata sourceEnv) (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured) (phase : RichPhase) :
    ∀ world ∈ (initial.located controls location).worlds,
      WorldBelow strata.rules.length world (originalCallWorld controls phase (.ref root) initial) := by
  induction location with
  | here => exact fun _ member => .child member
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih
  | appDomain parent ih | appResult parent ih | appPiFormation parent ih
  | lamDomain parent ih | piDomain parent ih | projField parent ih | projMajor parent ih
  | assignedFormation parent ih => exact ih
  | lamBody parent ih | lamCodomain parent ih | piBody parent ih =>
    intro world member
    simp only [WorldEnvironmentProvenance.located, WorldEnvironmentProvenance.worlds,
      WorldClosureProvenance.worlds, List.singleton_append, List.mem_cons] at member
    rcases member with rfl | member
    · apply Below.root
        (EquationControlMeasure.scheduleDecrease (richSchedule_strict
          (Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _) (parent.dependency_cost_le controls.ordered captured))
          .fundamental phase) _ _ _ _)
      exact ih
    · exact ih _ member
  | appCodomain parent ih =>
    intro world member
    simp only [WorldEnvironmentProvenance.located, WorldEnvironmentProvenance.worlds,
      WorldClosureProvenance.worlds, List.singleton_append, List.mem_cons] at member
    rcases member with rfl | member
    · apply Below.root
        (EquationControlMeasure.scheduleDecrease (richSchedule_strict
          (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _)
            (application_cost_le_captured _ _ _ _ _ _)) (parent.dependency_cost_le controls.ordered captured))
          .fundamental phase) _ _ _ _)
      exact ih
    · exact ih _ member

theorem WorldEnvironmentProvenance.located_captures_below
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (controls : OriginalWorldControls strata sourceEnv) (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured) :
    ∀ world ∈ (initial.located controls location).worlds,
      WorldBelow strata.rules.length world (originalCallWorld controls .fundamental (.ref root) initial) :=
  initial.located_captures_belowAt controls location .fundamental

/-- The selected original call is covered by the actual root call. Equality
is retained when no lambda is peeled, including an empty native telescope. -/
theorem WorldEnvironmentProvenance.located_call_coveredAt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (controls : OriginalWorldControls strata sourceEnv) (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured) (phase : RichPhase) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      [originalCallWorld controls phase node (initial.located controls location)]
      [originalCallWorld controls phase (.ref root) initial] := by
  intro world member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have bounded := location.dependency_cost_le controls.ordered captured
  rcases Nat.lt_or_eq_of_le bounded with smaller | equal
  · right
    exact .root (EquationControlMeasure.scheduleDecrease
      (richSchedule_strict smaller phase phase) _ _ _ _)
      (initial.located_captures_belowAt controls location phase)
  · left
    have empty : location.binderPrefix = [] := by
      by_cases nonempty : location.binderPrefix = []
      · exact nonempty
      · have strict := location_binder_cost_lt controls.ordered location captured nonempty
        omega
    unfold originalCallWorld
    rw [equal, located_worlds_nil controls location initial empty]
    rfl

theorem WorldEnvironmentProvenance.located_call_covered
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (controls : OriginalWorldControls strata sourceEnv) (location : Located root node)
    (initial : WorldEnvironmentProvenance strata U captured) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      [originalCallWorld controls .fundamental node (initial.located controls location)]
      [originalCallWorld controls .fundamental (.ref root) initial] :=
  initial.located_call_coveredAt controls location .fundamental

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
