import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration

/-! Composition keeps the actual position of every annotated frame. Equal raw
boxes on opposite sides of a join need not have equal execution annotations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace RawGeneratedTypeRoute.WorldBoundary
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target common : List VExpr} {commonLeft commonRight : Subst}
    {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {middleControls : OriginalWorldControls strata middle.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {middleWorld : WorldEnvironmentProvenance strata U intermediate}
    {rightWorld : WorldEnvironmentProvenance strata U final}

noncomputable def transLeftIndex (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final)
    (index : Fin first.frames.length) : Fin (first.trans second).frames.length :=
  ⟨index.val, by
    have lengths : (first.trans second).frames.length = first.frames.length + second.frames.length := by
      rw [RawGeneratedTypeRoute.frames.eq_def (first.trans second), List.length_append]
    have bound := index.isLt
    omega⟩

noncomputable def transRightIndex (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final)
    (index : Fin second.frames.length) : Fin (first.trans second).frames.length :=
  ⟨first.frames.length + index.val, by
    have lengths : (first.trans second).frames.length = first.frames.length + second.frames.length := by
      rw [RawGeneratedTypeRoute.frames.eq_def (first.trans second), List.length_append]
    have bound := index.isLt
    omega⟩

theorem frameAt_trans_left
    (before : first.WorldBoundary firstInputs leftControls middleControls leftWorld middleWorld)
    (after : second.WorldBoundary secondInputs middleControls rightControls middleWorld rightWorld)
    (index : Fin first.frames.length) :
    (before.trans after).frameAt (transLeftIndex first second index) = before.frameAt index := by
  change (before.frames ++ after.frames)[index.val]'_ = before.frames[index.val]'_
  exact List.getElem_append_left (by simpa only [before.frames_length] using index.isLt)

theorem frameAt_trans_right
    (before : first.WorldBoundary firstInputs leftControls middleControls leftWorld middleWorld)
    (after : second.WorldBoundary secondInputs middleControls rightControls middleWorld rightWorld)
    (index : Fin second.frames.length) :
    (before.trans after).frameAt (transRightIndex first second index) = after.frameAt index := by
  change (before.frames ++ after.frames)[first.frames.length + index.val]'_ = after.frames[index.val]'_
  have bound : before.frames.length ≤ first.frames.length + index.val := by
    rw [before.frames_length]; omega
  rw [List.getElem_append_right bound]
  simp only [before.frames_length, Nat.add_sub_cancel_left]

/-- Every combined position belongs to exactly one original side. -/
theorem transIndex_cases (index : Fin (first.trans second).frames.length) :
    (∃ previous, index = transLeftIndex first second previous) ∨
    (∃ next, index = transRightIndex first second next) := by
  have bound := index.isLt
  have lengths : (first.trans second).frames.length = first.frames.length + second.frames.length := by
    rw [RawGeneratedTypeRoute.frames.eq_def (first.trans second), List.length_append]
  by_cases previous : index.val < first.frames.length
  · exact Or.inl ⟨⟨index.val, previous⟩, rfl⟩
  · refine Or.inr ⟨⟨index.val - first.frames.length, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [transRightIndex]
    omega

/-- Indexed coherence composes by the two actual positional ranges. The
chosen generation at a repeated raw box is never borrowed from the other side. -/
theorem FrameOccurrenceCoherent.trans
    {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target}
    (before : first.WorldBoundary firstInputs leftControls middleControls leftWorld middleWorld)
    (after : second.WorldBoundary secondInputs middleControls rightControls middleWorld rightWorld)
    (controls : ∀ index : Fin (first.trans second).frames.length,
      OriginalWorldControls strata ((first.trans second).frames[index]).sourceEnv)
    (generated : ∀ index : Fin (first.trans second).frames.length,
      WorldGenerated strata P base caps commonLeft commonRight ((first.trans second).frames[index]).graph
        ((first.trans second).frames[index]).frame.realization.frame.raw (controls index))
    (previous : ∀ index : Fin first.frames.length,
      HEq (controls (transLeftIndex first second index)) (before.frameAt index).controls ∧
      Covered (@EquationControlMeasure.Less strata.rules.length)
        (generated (transLeftIndex first second index)).worlds (before.frameAt index).world.worlds)
    (next : ∀ index : Fin second.frames.length,
      HEq (controls (transRightIndex first second index)) (after.frameAt index).controls ∧
      Covered (@EquationControlMeasure.Less strata.rules.length)
        (generated (transRightIndex first second index)).worlds (after.frameAt index).world.worlds) :
    (before.trans after).FrameOccurrenceCoherent controls generated := by
  intro index
  obtain ⟨previousIndex, rfl⟩ | ⟨nextIndex, rfl⟩ := transIndex_cases index
  · let predicate := fun occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata =>
      HEq (controls (transLeftIndex first second previousIndex)) occurrence.controls ∧
      Covered (@EquationControlMeasure.Less strata.rules.length)
        (generated (transLeftIndex first second previousIndex)).worlds occurrence.world.worlds
    exact (congrArg predicate (frameAt_trans_left before after previousIndex)).mpr (previous previousIndex)
  · let predicate := fun occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata =>
      HEq (controls (transRightIndex first second nextIndex)) occurrence.controls ∧
      Covered (@EquationControlMeasure.Less strata.rules.length)
        (generated (transRightIndex first second nextIndex)).worlds occurrence.world.worlds
    exact (congrArg predicate (frameAt_trans_right before after nextIndex)).mpr (next nextIndex)

end RawGeneratedTypeRoute.WorldBoundary
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
