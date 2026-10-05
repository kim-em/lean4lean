import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderFrameTransportMeasure

/-! Left diagonalization of actual generic frames traverses every retained
grouped owner frame. Original queries, aligned certificates, and the computed
source environment remain unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

mutual
noncomputable def RawOriginalRichFrame.leftDiagonal
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    RawOriginalRichFrame sourceEnv env U registry target context locals σ σ available :=
  match frame with
  | .nil => .nil
  | .reserve frame closures => .reserve frame.leftDiagonal closures
  | .merge left right => .merge left.leftDiagonal right.leftDiagonal
  | .header ordered initial frame => .header ordered initial frame.leftDiagonal
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    .bind tail.leftDiagonal domain certificate resources typed arguments.left_diagonal needs bounded covered
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    .capture tail.leftDiagonal domain initialContext argument argumentLocation argumentLineage argumentQuery
      argumentAvailable certificate resources typed arguments.left_diagonal needs bounded covered
  | .group tail domain ordered initial entries =>
    .group tail.leftDiagonal domain ordered initial entries.leftDiagonal
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntry.leftDiagonal
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue leftValue n input :=
  match entry with
  | .mk owner locals left right available initial frame substitutions depth sourcePrefix sourceEq depthEq expressionEq
      leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query resources answer =>
    .mk owner locals left left available initial frame.leftDiagonal substitutions.left depth sourcePrefix sourceEq depthEq
      expressionEq leftEq leftEq queryRank queryInput queryBound queryAdapter footprint query resources answer.leftDiagonal
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.leftDiagonal
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue leftValue needs :=
  match entries with
  | .nil => .nil
  | .cons entry tail => .cons entry.leftDiagonal tail.leftDiagonal
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

theorem RawRichGroupEntries.ownerClosures_leftDiagonal
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (ordered : sourceEnv.Ordered) (declared : Closure)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    entries.leftDiagonal.ownerClosures ordered declared = entries.ownerClosures ordered declared := by
  match entries with
  | .nil => simp only [leftDiagonal, ownerClosures]
  | .cons entry tail =>
    cases entry
    simp only [leftDiagonal, RawRichGroupEntry.leftDiagonal, ownerClosures, RawRichGroupEntry.owner,
      tail.ownerClosures_leftDiagonal ordered declared]
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega

theorem RawOriginalRichFrame.dependencyEnvironment_leftDiagonal
    (ordered : sourceEnv.Ordered)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    frame.leftDiagonal.dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  match frame with
  | .nil => simp only [leftDiagonal, dependencyEnvironment]
  | .reserve frame closures =>
    simp only [leftDiagonal, dependencyEnvironment, frame.dependencyEnvironment_leftDiagonal ordered]
  | .merge left right =>
    simp only [leftDiagonal, dependencyEnvironment, left.dependencyEnvironment_leftDiagonal ordered,
      right.dependencyEnvironment_leftDiagonal ordered]
  | .header capturedOrdered initial frame =>
    simpa only [leftDiagonal, dependencyEnvironment] using
      frame.dependencyEnvironment_leftDiagonal ordered capturedOrdered initial
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [leftDiagonal, dependencyEnvironment, tail.dependencyEnvironment_leftDiagonal ordered]
  | .capture tail .. =>
    simp only [leftDiagonal, dependencyEnvironment, tail.dependencyEnvironment_leftDiagonal ordered]
  | .group tail domain capturedOrdered initial entries =>
    simp only [leftDiagonal, dependencyEnvironment, tail.dependencyEnvironment_leftDiagonal ordered,
      RawRichGroupEntries.ownerClosures_leftDiagonal]
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

mutual
theorem RawOriginalRichFrame.valid_leftDiagonal
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (valid : frame.Valid) : frame.leftDiagonal.Valid := by
  match frame with
  | .nil | .header .. => simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Valid]
  | .merge left right =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Valid] at valid ⊢
    exact ⟨left.valid_leftDiagonal valid.1, right.valid_leftDiagonal valid.2⟩
  | .bind tail .. | .capture tail .. | .reserve tail _ =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Valid] at valid ⊢
    exact tail.valid_leftDiagonal valid
  | .group tail _ _ _ entries =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Valid] at valid ⊢
    exact ⟨tail.valid_leftDiagonal valid.1, entries.valid_leftDiagonal valid.2⟩
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.valid_leftDiagonal
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (valid : entry.frame.Valid)
    (bound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (entry.frame.dependencyEnvironment ordered) ≤
        environmentCost (entry.owner.dependencyEnvironment ordered ownerInitial)) :
    entry.leftDiagonal.frame.Valid ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (entry.leftDiagonal.frame.dependencyEnvironment ordered) ≤
          environmentCost (entry.leftDiagonal.owner.dependencyEnvironment ordered ownerInitial)) := by
  match entry with
  | .mk owner locals left right available initial frame substitutions depth sourcePrefix sourceEq depthEq expressionEq
      leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query resources answer =>
    rw [RawRichGroupEntry.leftDiagonal]
    simp only [RawRichGroupEntry.frame, RawRichGroupEntry.owner] at valid bound ⊢
    exact ⟨frame.valid_leftDiagonal valid, fun ordered => by
      simpa only [RawOriginalRichFrame.dependencyEnvironment_leftDiagonal] using bound ordered⟩
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.valid_leftDiagonal
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (valid : entries.Valid) : entries.leftDiagonal.Valid := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.Valid]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.Valid] at valid ⊢
    have transformed := entry.valid_leftDiagonal valid.1 valid.2.1
    exact ⟨transformed.1, transformed.2, tail.valid_leftDiagonal valid.2.2⟩
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega

end

noncomputable def OriginalRichFrame.leftDiagonal
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry target context locals σ σ available :=
  ⟨frame.raw.leftDiagonal, frame.raw.valid_leftDiagonal frame.valid⟩

theorem OriginalRichFrame.dependencyEnvironment_leftDiagonal
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    frame.leftDiagonal.dependencyEnvironment ordered = frame.dependencyEnvironment ordered :=
  frame.raw.dependencyEnvironment_leftDiagonal ordered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
