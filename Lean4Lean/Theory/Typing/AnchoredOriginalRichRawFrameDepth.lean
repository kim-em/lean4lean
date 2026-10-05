import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameRaw
import Lean4Lean.Theory.Typing.AnchoredOriginalRichNativeDepthFuture

/-! The recursive declaration bound counts every retained owner frame,
whole query, and both alignment certificates. Repeated demands combine by
maximum and use the same finite raw capture spine. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def HeaderValueAlignment.nativeDepth (current : Name → Bool)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) : Nat :=
  max (answer.value.certificate.nativeDepth current) (answer.aligned.certificate.nativeDepth current)

noncomputable def HeaderRichTail.nativeDepth (current : Name → Bool)
    (tail : HeaderRichTail header field major env registry target context locals σ τ available) : Nat :=
  match tail with
  | .nil => 0
  | .skip tail .. => tail.nativeDepth current
  | .push tail _ _ _ _ answer .. => max (answer.nativeDepth current) (tail.nativeDepth current)

noncomputable def HeaderBinderFrame.nativeDepth (current : Name → Bool)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) : Nat :=
  match frame with
  | .captured tail => tail.nativeDepth current
  | .bind tail _ _ _ certificate .. => max (certificate.nativeDepth current) (tail.nativeDepth current)

mutual
noncomputable def RawOriginalRichFrame.nativeDepth (current : Name → Bool)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Nat :=
  match frame with
  | .nil => 0
  | .header _ _ frame => frame.nativeDepth current
  | .bind tail _ certificate .. => max (certificate.nativeDepth current) (tail.nativeDepth current)
  | .capture tail _ _ _ _ _ query _ certificate .. =>
      max (query.nativeDepth current) (max (certificate.nativeDepth current) (tail.nativeDepth current))
  | .group tail _ _ _ entries => max (entries.nativeDepth current) (tail.nativeDepth current)
  | .reserve frame _ => frame.nativeDepth current
  | .merge left right => max (left.nativeDepth current) (right.nativeDepth current)
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntry.nativeDepth (current : Name → Bool)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) : Nat :=
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ query _ answer =>
    max (frame.nativeDepth current) (max (query.nativeDepth current) (answer.nativeDepth current))
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.nativeDepth (current : Name → Bool)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Nat :=
  match entries with
  | .nil => 0
  | .cons entry tail => max (entry.nativeDepth current) (tail.nativeDepth current)
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

@[simp] theorem RawRichGroupEntry.nativeDepth_eq (current : Name → Bool)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.nativeDepth current = max (entry.frame.nativeDepth current)
      (max (entry.query.nativeDepth current) (entry.answer.nativeDepth current)) := by
  cases entry
  simp only [RawRichGroupEntry.nativeDepth, RawRichGroupEntry.frame,
    RawRichGroupEntry.query, RawRichGroupEntry.answer]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
