import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame

/-! Ambient inclusion is hereditary original-source provenance, independent
of resource validity or semantic relatedness. Empty tables do not establish
that an original source environment belongs to the target environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1000000

mutual
def RawOriginalRichFrame.Ambient
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  sourceEnv ≤ env ∧ match frame with
  | .nil => True
  | .reserve previous _ => previous.Ambient
  | .merge left right => left.Ambient ∧ right.Ambient
  | .header (capturedEnv := capturedEnv) .. => capturedEnv ≤ env
  | .bind previous .. => previous.Ambient
  | .capture previous .. => previous.Ambient
  | .group (capturedEnv := capturedEnv) previous _ _ _ entries =>
      previous.Ambient ∧ capturedEnv ≤ env ∧ entries.Ambient
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

def RawRichGroupEntry.Ambient
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) : Prop :=
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ _query _resources _answer => frame.Ambient
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

def RawRichGroupEntries.Ambient
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Prop :=
  match entries with
  | .nil => True
  | .cons entry rest => entry.Ambient ∧ rest.Ambient
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

def OriginalRichFrame.Ambient
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  frame.raw.Ambient

theorem RawOriginalRichFrame.Ambient.below
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.Ambient) : sourceEnv ≤ env := by
  rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
  exact ambient.1

theorem OriginalRichFrame.Ambient.below
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.Ambient) : sourceEnv ≤ env := RawOriginalRichFrame.Ambient.below ambient

theorem RawRichGroupEntry.Ambient.ownerFrame
    {entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input}
    (ambient : entry.Ambient) : entry.frame.Ambient := by
  cases entry
  simpa only [RawRichGroupEntry.Ambient.eq_def, RawRichGroupEntry.frame] using ambient

theorem OriginalRichFrame.Ambient.merge
    {left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : left.Ambient) (second : right.Ambient) : (left.merge right).Ambient := by
  change (RawOriginalRichFrame.merge left.raw right.raw).Ambient
  rw [RawOriginalRichFrame.Ambient.eq_def]
  exact ⟨first.below, first, second⟩

theorem OriginalRichFrame.Ambient.reserve
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.Ambient) (closures : List Closure) : (frame.reserve closures).Ambient := by
  change (RawOriginalRichFrame.reserve frame.raw closures).Ambient
  rw [RawOriginalRichFrame.Ambient.eq_def]
  exact ⟨ambient.below, ambient⟩

/-- Query-selected entries preserve their actual owner frame, so its ambient
inclusion is recoverable without inspecting semantic certificates. -/
theorem RawRichGroupEntries.Ambient.cons
    {entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input}
    {rest : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs}
    (head : entry.Ambient) (tail : rest.Ambient) : (RawRichGroupEntries.cons entry rest).Ambient := by
  rw [RawRichGroupEntries.Ambient.eq_def]
  exact ⟨head, tail⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
