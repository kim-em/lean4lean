import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameRaw
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame

/-! The recursive declaration bound counts every retained owner frame,
whole query, and both alignment certificates. Repeated demands combine by
maximum and use the same finite raw capture spine. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

noncomputable def HeaderValueAlignment.headDepth (policy : Name → Nat → Nat)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) : Nat :=
  max (answer.value.certificate.headDepth policy) (answer.aligned.certificate.headDepth policy)

noncomputable def HeaderRichTail.headDepth (policy : Name → Nat → Nat)
    (tail : HeaderRichTail header field major env registry target context locals σ τ available) : Nat :=
  match tail with
  | .nil => 0
  | .skip tail .. => tail.headDepth policy
  | .push tail _ _ _ _ answer .. => max (answer.headDepth policy) (tail.headDepth policy)

noncomputable def HeaderBinderFrame.headDepth (policy : Name → Nat → Nat)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) : Nat :=
  match frame with
  | .captured tail => tail.headDepth policy
  | .bind tail _ _ _ certificate .. => max (certificate.headDepth policy) (tail.headDepth policy)

mutual
noncomputable def RawOriginalRichFrame.headDepth (policy : Name → Nat → Nat)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Nat :=
  match frame with
  | .nil => 0
  | .header _ _ frame => frame.headDepth policy
  | .bind tail _ certificate .. => max (certificate.headDepth policy) (tail.headDepth policy)
  | .capture tail _ _ _ _ _ query _ certificate .. =>
      max (query.headDepth policy) (max (certificate.headDepth policy) (tail.headDepth policy))
  | .group tail _ _ _ entries => max (entries.headDepth policy) (tail.headDepth policy)
  | .reserve frame _ => frame.headDepth policy
  | .merge left right => max (left.headDepth policy) (right.headDepth policy)
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntry.headDepth (policy : Name → Nat → Nat)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) : Nat :=
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ query _ answer =>
    max (frame.headDepth policy) (max (query.headDepth policy) (answer.headDepth policy))
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.headDepth (policy : Name → Nat → Nat)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) : Nat :=
  match entries with
  | .nil => 0
  | .cons entry tail => max (entry.headDepth policy) (tail.headDepth policy)
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

@[simp] theorem RawRichGroupEntry.headDepth_eq (policy : Name → Nat → Nat)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.headDepth policy = max (entry.frame.headDepth policy)
      (max (entry.query.headDepth policy) (entry.answer.headDepth policy)) := by
  cases entry
  simp only [RawRichGroupEntry.headDepth, RawRichGroupEntry.frame,
    RawRichGroupEntry.query, RawRichGroupEntry.answer]

noncomputable def OriginalRichFrame.headDepth (policy : Name → Nat → Nat)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Nat :=
  frame.raw.headDepth policy

@[simp] theorem OriginalRichFrame.headDepth_merge (policy : Name → Nat → Nat)
    (left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
    (right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
    (left.merge right).headDepth policy = max (left.headDepth policy) (right.headDepth policy) := by
  simp only [OriginalRichFrame.headDepth, OriginalRichFrame.merge, RawOriginalRichFrame.headDepth]

@[simp] theorem OriginalRichFrame.headDepth_reserve (policy : Name → Nat → Nat)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closures : List Closure) : (frame.reserve closures).headDepth policy = frame.headDepth policy := by
  simp only [OriginalRichFrame.headDepth, OriginalRichFrame.reserve, RawOriginalRichFrame.headDepth]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
