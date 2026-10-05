import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

mutual
 theorem RawOriginalRichFrame.Ambient.leftDiagonal
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ambient : frame.Ambient) : frame.leftDiagonal.Ambient := by
  match frame, ambient with
  | .nil, ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ambient
  | .reserve frame closures, ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.1, RawOriginalRichFrame.Ambient.leftDiagonal frame ambient.2⟩
  | .merge left right, ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.1, RawOriginalRichFrame.Ambient.leftDiagonal left ambient.2.1, RawOriginalRichFrame.Ambient.leftDiagonal right ambient.2.2⟩
  | .header .., ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ambient
  | .bind tail .., ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.1, RawOriginalRichFrame.Ambient.leftDiagonal tail ambient.2⟩
  | .capture tail .., ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.1, RawOriginalRichFrame.Ambient.leftDiagonal tail ambient.2⟩
  | .group tail domain ordered initial entries, ambient =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.1, RawOriginalRichFrame.Ambient.leftDiagonal tail ambient.2.1, ambient.2.2.1,
      entriesAmbientDiagonal entries ambient.2.2.2⟩
 termination_by sizeOf frame
 decreasing_by all_goals simp_wf <;> omega

 theorem entryAmbientDiagonal
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (ambient : entry.Ambient) : entry.leftDiagonal.Ambient := by
  match entry, ambient with
  | .mk owner locals left right available initial frame substitutions depth sourcePrefix sourceEq depthEq expressionEq
      leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query resources answer, ambient =>
    rw [RawRichGroupEntry.leftDiagonal, RawRichGroupEntry.Ambient.eq_def]
    apply RawOriginalRichFrame.Ambient.leftDiagonal frame
    simpa only [RawRichGroupEntry.Ambient.eq_def] using ambient
 termination_by sizeOf entry
 decreasing_by all_goals simp_wf <;> omega

 theorem entriesAmbientDiagonal
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (ambient : entries.Ambient) : entries.leftDiagonal.Ambient := by
  match entries, ambient with
  | .nil, ambient => simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.Ambient.eq_def]
  | .cons entry rest, ambient =>
    rw [RawRichGroupEntries.Ambient.eq_def] at ambient
    rw [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.Ambient.eq_def]
    exact ⟨entryAmbientDiagonal entry ambient.1, entriesAmbientDiagonal rest ambient.2⟩
 termination_by sizeOf entries
 decreasing_by all_goals simp_wf <;> omega
end

theorem OriginalRichFrame.Ambient.leftDiagonal
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ambient : frame.Ambient) : frame.leftDiagonal.Ambient :=
  RawOriginalRichFrame.Ambient.leftDiagonal frame.raw ambient

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
