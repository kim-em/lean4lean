import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateParameterWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldStaticCallBounds

/-! Fund the actual parameter-hole requery from its retained nominal argument
to the independent right field original. Both endpoints use the SAME selected
frame ledger. Its capacity and hereditary coverage admit the selected frame
under the fixed outer projection budget; no same-key strict edge is claimed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalFactorCut OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private field_cost_lt from_right from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- This is the concrete R pair used after extracting a richer parameter
request from the actual major descriptor. The field may be any original
endpoint, including a computed endpoint rather than a derivation reference. -/
theorem ProjectionHead.parameterFieldSelectedFunding
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {argument : EndpointState sourceEnv U source expression argumentType}
    (location : Located (.right head.major) argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost selectedEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selected.worlds baseline.worlds)
    (other : World strata.rules.length)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier
      [other, originalCallWorld controls .assignedComparison outer baseline]) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .expressionReindex argument selected,
        originalCallWorld controls .expressionReindex head.field selected])
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]) ∧
    Sponsored frontier [originalCallWorld controls .expressionReindex argument selected,
      originalCallWorld controls .expressionReindex head.field selected] := by
  have admitted := originalCallWorld_boundedNode controls .assignedComparison outer
    selected baseline capacity covered
  have argumentLower := BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans admitted
    (ProjectionHead.parameter_below head location controls selected .expressionReindex .assignedComparison)
  have fieldLower : WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex head.field selected)
      (originalCallWorld controls .assignedComparison outer baseline) := by
    apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans admitted
    exact original_child (richSchedule_strict
      (field_cost_lt head controls.ordered selectedEnvironment) _ _) _ _ _ _ _
  have lower : ∀ world ∈ [originalCallWorld controls .expressionReindex argument selected,
      originalCallWorld controls .expressionReindex head.field selected],
      WorldBelow strata.rules.length world
        (originalCallWorld controls .assignedComparison outer baseline) := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact argumentLower
    · cases List.mem_singleton.mp member
      exact fieldLower
  constructor
  · have decrease : CallBelow strata.rules.length
        [originalCallWorld controls .expressionReindex argument selected,
          originalCallWorld controls .expressionReindex head.field selected]
        [other, originalCallWorld controls .assignedComparison outer baseline] :=
      from_right lower
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length
          (inherited ++ [originalCallWorld controls .expressionReindex argument selected,
            originalCallWorld controls .expressionReindex head.field selected])
          (inherited ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
      intro inherited
      induction inherited with
      | nil => exact decrease
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  · obtain ⟨sponsor, member, outerBelow⟩ := paid _
      (List.mem_cons_of_mem other (List.mem_singleton_self _))
    intro world present
    exact ⟨sponsor, member,
      EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans (lower world present) outerBelow⟩

/-- The assigned seed travels from the actual field occurrence to its nominal
parameter occurrence. Both proper originals remain funded even after query-selected
frame reorganization. -/
theorem ProjectionHead.parameterAssignedSelectedFunding
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {argument : EndpointState sourceEnv U source expression argumentType}
    (location : Located (.right head.major) argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost selectedEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      selected.worlds baseline.worlds)
    (other : World strata.rules.length)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier
      [other, originalCallWorld controls .assignedComparison outer baseline]) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .assignedComparison head.field selected,
        originalCallWorld controls .assignedComparison argument selected])
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]) ∧
    Sponsored frontier [originalCallWorld controls .assignedComparison head.field selected,
      originalCallWorld controls .assignedComparison argument selected] := by
  have admitted := originalCallWorld_boundedNode controls .assignedComparison outer
    selected baseline capacity covered
  have argumentLower := BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans admitted
    (ProjectionHead.parameter_below head location controls selected .assignedComparison .assignedComparison)
  have fieldLower : WorldBelow strata.rules.length
      (originalCallWorld controls .assignedComparison head.field selected)
      (originalCallWorld controls .assignedComparison outer baseline) := by
    apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans admitted
    exact original_child (richSchedule_strict
      (field_cost_lt head controls.ordered selectedEnvironment) _ _) _ _ _ _ _
  have lower : ∀ world ∈ [originalCallWorld controls .assignedComparison head.field selected,
      originalCallWorld controls .assignedComparison argument selected],
      WorldBelow strata.rules.length world
        (originalCallWorld controls .assignedComparison outer baseline) := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact fieldLower
    · cases List.mem_singleton.mp member
      exact argumentLower
  constructor
  · have decrease : CallBelow strata.rules.length
        [originalCallWorld controls .assignedComparison head.field selected,
          originalCallWorld controls .assignedComparison argument selected]
        [other, originalCallWorld controls .assignedComparison outer baseline] :=
      from_right lower
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length
          (inherited ++ [originalCallWorld controls .assignedComparison head.field selected,
            originalCallWorld controls .assignedComparison argument selected])
          (inherited ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
      intro inherited
      induction inherited with
      | nil => exact decrease
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  · obtain ⟨sponsor, member, outerBelow⟩ := paid _
      (List.mem_cons_of_mem other (List.mem_singleton_self _))
    intro world present
    exact ⟨sponsor, member,
      EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans (lower world present) outerBelow⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
