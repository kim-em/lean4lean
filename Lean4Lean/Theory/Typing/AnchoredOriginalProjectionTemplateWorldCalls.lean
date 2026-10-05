import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex

/-! The five actual calls needed by a prior-field projection hole. Two
same-side major endpoints can exceed the old sum budget. Each is instead a
proper child of its own outer projection world. No new sponsor is retained
in a recursive call: that parent is replaced by the actual smaller calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalFactorCut
open EquationWorldClosureOrder
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem major_below
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length
      (originalCallWorld controls phase (.ref (.right head.major)) captured)
      (originalCallWorld controls parentPhase node captured) :=
  original_child (richSchedule_strict
    (projectionMajor_cost_lt head controls.ordered environment) phase parentPhase)
    _ _ _ _ _

private theorem field_cost_lt
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (ordered : sourceEnv.Ordered) (captured : List OriginalClosureMeasure.Closure) :
    (OriginalClosureMeasure.Closure.close (head.field.dependencyOrigin ordered) captured).cost <
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin ordered) captured).cost := by
  have child : (head.field.dependencyOrigin ordered).weight <
      ((projectionNatural head).dependencyOrigin ordered).weight := by
    apply Origin.rule_child
    simp
  exact Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_right child (show 0 < 1 + environmentCost captured by omega))
    (head.route.dependency_cost_le ordered captured)

private theorem inner_major_below
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (outer : ProjectionHead node)
    (display : outer.fieldType = .proj innerName innerIndex innerMajor)
    (inner : ProjectionHead (outer.field.cast display rfl))
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length
      (originalCallWorld controls phase (.ref (.right inner.major)) captured)
      (originalCallWorld controls parentPhase node captured) := by
  have innerCost := projectionMajor_cost_lt inner controls.ordered environment
  simp only [EndpointState.dependencyOrigin_cast] at innerCost
  exact original_child (richSchedule_strict
    (Nat.lt_trans innerCost (field_cost_lt outer controls.ordered environment)) phase parentPhase)
    _ _ _ _ _

private theorem from_left
    {parent other : World count} {calls : List (World count)}
    (lower : ∀ call ∈ calls, WorldBelow count call parent) :
    CallBelow count calls [parent, other] :=
  (split_call lower).trans
    ((EquationWorldPolynomial.lower_mass (mass := []) (world := other) (by simp)).cons parent)

private theorem from_right
    {parent other : World count} {calls : List (World count)}
    (lower : ∀ call ∈ calls, WorldBelow count call other) :
    CallBelow count calls [parent, other] :=
  (split_call lower).trans (.single (.head (replacement := []) (by simp)))

private theorem from_both
    {left right parent other : World count}
    (hl : WorldBelow count left parent) (hr : WorldBelow count right other) :
    CallBelow count [left, right] [parent, other] := by
  have first : CallBelow count [left, right] [parent, right] :=
    .single (.head (replacement := [left]) (by simpa using hl))
  exact first.trans ((split_call (calls := [right]) (by simpa using hr)).cons parent)

/-- Funding for R, forward equality, R, backward equality, R through the
two outer majors. The inner heads are extracted from the actual outer field
formations, whose displayed syntax is a prior projection. Equalities of the
displayed expressions belong to the semantic bridge, not this cost theorem.
Both orientations of an original equality have definitionally the same world. -/
theorem projectionTemplateBridgeFunding
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (leftDisplay : leftHead.fieldType = .proj priorName priorIndex leftValue)
    (rightDisplay : rightHead.fieldType = .proj priorName priorIndex rightValue)
    (leftInner : ProjectionHead (leftHead.field.cast leftDisplay rfl))
    (rightInner : ProjectionHead (rightHead.field.cast rightDisplay rfl))
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (leftCaptured : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightCaptured : WorldEnvironmentProvenance strata U rightEnvironment) :
    let parent := [originalCallWorld leftControls .assignedComparison left leftCaptured,
      originalCallWorld rightControls .assignedComparison right rightCaptured]
    CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex (.ref (.right leftInner.major)) leftCaptured,
       originalCallWorld leftControls .expressionReindex (.ref (.left leftHead.major)) leftCaptured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld leftControls .fundamental (.ref (.left leftHead.major)) leftCaptured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex (.ref (.right leftHead.major)) leftCaptured,
       originalCallWorld rightControls .expressionReindex (.ref (.right rightHead.major)) rightCaptured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld rightControls .fundamental (.ref (.right rightHead.major)) rightCaptured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld rightControls .expressionReindex (.ref (.left rightHead.major)) rightCaptured,
       originalCallWorld rightControls .expressionReindex (.ref (.right rightInner.major)) rightCaptured] parent := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply from_left
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact inner_major_below leftHead leftDisplay leftInner leftControls leftCaptured _ _
    · cases List.mem_singleton.mp member
      exact major_below leftHead leftControls leftCaptured _ _
  · apply from_left
    intro call member
    cases List.mem_singleton.mp member
    exact major_below leftHead leftControls leftCaptured _ _
  · exact from_both (major_below leftHead leftControls leftCaptured _ _)
      (major_below rightHead rightControls rightCaptured _ _)
  · apply from_right
    intro call member
    cases List.mem_singleton.mp member
    exact major_below rightHead rightControls rightCaptured _ _
  · apply from_right
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact major_below rightHead rightControls rightCaptured _ _
    · cases List.mem_singleton.mp member
      exact inner_major_below rightHead rightDisplay rightInner rightControls rightCaptured _ _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
