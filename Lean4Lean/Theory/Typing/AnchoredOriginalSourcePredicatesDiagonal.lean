import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicates
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

mutual
 theorem RawOriginalRichFrame.AllSources.leftDiagonal
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (sources : frame.AllSources P) : frame.leftDiagonal.AllSources P := by
  match frame, sources with
  | .nil, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact sources
  | .reserve frame closures, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.leftDiagonal frame sources.2⟩
  | .merge left right, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.leftDiagonal left sources.2.1, RawOriginalRichFrame.AllSources.leftDiagonal right sources.2.2⟩
  | .header .., sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact sources
  | .bind tail .., sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.leftDiagonal tail sources.2⟩
  | .capture tail .., sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.leftDiagonal tail sources.2⟩
  | .group tail domain ordered initial entries, sources =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources
    rw [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.leftDiagonal tail sources.2.1, sources.2.2.1,
      RawRichGroupEntries.AllSources.leftDiagonal entries sources.2.2.2⟩
 termination_by sizeOf frame
 decreasing_by all_goals simp_wf <;> omega

 theorem RawRichGroupEntry.AllSources.leftDiagonal
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (sources : entry.AllSources P) : entry.leftDiagonal.AllSources P := by
  match entry, sources with
  | .mk owner locals left right available initial frame substitutions depth sourcePrefix sourceEq depthEq expressionEq
      leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query resources answer, sources =>
    rw [RawRichGroupEntry.leftDiagonal, RawRichGroupEntry.AllSources.eq_def]
    apply RawOriginalRichFrame.AllSources.leftDiagonal frame
    simpa only [RawRichGroupEntry.AllSources.eq_def] using sources
 termination_by sizeOf entry
 decreasing_by all_goals simp_wf <;> omega

 theorem RawRichGroupEntries.AllSources.leftDiagonal
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals
      declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (sources : entries.AllSources P) : entries.leftDiagonal.AllSources P := by
  match entries, sources with
  | .nil, sources => simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.AllSources.eq_def]
  | .cons entry rest, sources =>
    rw [RawRichGroupEntries.AllSources.eq_def] at sources
    rw [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.AllSources.eq_def]
    exact ⟨RawRichGroupEntry.AllSources.leftDiagonal entry sources.1, RawRichGroupEntries.AllSources.leftDiagonal rest sources.2⟩
 termination_by sizeOf entries
 decreasing_by all_goals simp_wf <;> omega
end

theorem OriginalRichFrame.AllSources.leftDiagonal
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (sources : frame.AllSources P) : frame.leftDiagonal.AllSources P :=
  RawOriginalRichFrame.AllSources.leftDiagonal frame.raw sources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
