import Lean4Lean.Theory.Typing.CanonicalDataHeadRenaming

/-! Canonical traces for the ordinary-data machine. Terminal comparison and
renaming retain the proof telescope generated inside recursive major paths. -/

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature.NativeRecursorData

inductive Trace (registry : Registry) : VExpr → List VExpr → VExpr → Prop where
  | refl : Trace registry expression [] expression
  | next : step registry expression = some out →
      Trace registry out.result added result →
      Trace registry expression (added ++ out.added) result

theorem Trace.terminal_unique
    (first : Trace registry expression firstAdded firstResult)
    (second : Trace registry expression secondAdded secondResult)
    (firstTerminal : step registry firstResult = none)
    (secondTerminal : step registry secondResult = none) :
    firstAdded = secondAdded ∧ firstResult = secondResult := by
  induction first generalizing secondAdded secondResult with
  | refl =>
    cases second with
    | refl => exact ⟨rfl, rfl⟩
    | next reduction tail => rw [firstTerminal] at reduction; contradiction
  | @next expression out added result reduction tail ih =>
    cases second with
    | refl => rw [secondTerminal] at reduction; contradiction
    | @next _ other otherAdded otherResult otherReduction otherTail =>
      have same : out = other := Option.some.inj (reduction.symm.trans otherReduction)
      cases same
      obtain ⟨sameAdded, sameResult⟩ := ih otherTail firstTerminal secondTerminal
      exact ⟨congrArg (· ++ out.added) sameAdded, sameResult⟩

theorem Trace.rename (hscope : registry.Scoped)
    (trace : Trace registry expression added result) (ρ : Lift) :
    Trace registry (expression.lift' ρ) (renameAdded ρ added)
      (result.lift' (ρ.consN added.length)) := by
  induction trace generalizing ρ with
  | @refl expression =>
    simpa [renameAdded] using Trace.refl (registry := registry) (expression := expression.lift' ρ)
  | @next expression out added result reduction tail ih =>
    have reduction' : step registry (expression.lift' ρ) = some (out.rename ρ) := by
      rw [step_rename registry hscope, reduction]
      rfl
    have future := Trace.next reduction' (ih (ρ.consN out.added.length))
    simpa only [CanonicalHead.Output.rename, CanonicalHead.renameAdded_append,
      List.length_append, Lift.consN_consN, Nat.add_comm out.added.length added.length] using future

/-- Source renamings cannot create hidden ordinary iota branches. This
reflection property is needed when cutting a whole observed variable. -/
theorem Trace.unrename (hscope : registry.Scoped)
    (trace : Trace registry (expression.lift' ρ) added result) :
    ∃ originalAdded originalResult,
      Trace registry expression originalAdded originalResult ∧
      added = renameAdded ρ originalAdded ∧
      result = originalResult.lift' (ρ.consN originalAdded.length) := by
  generalize sameSource : expression.lift' ρ = source at trace
  induction trace generalizing expression ρ with
  | refl => exact ⟨[], expression, .refl, rfl, sameSource.symm⟩
  | @next source out added result reduction tail ih =>
    rw [← sameSource, step_rename registry hscope] at reduction
    obtain ⟨original, stepOriginal, sameOut⟩ := Option.map_eq_some_iff.mp reduction
    subst out
    obtain ⟨originalAdded, originalResult, tailOriginal, sameAdded, sameResult⟩ :=
      ih (expression := original.result) (ρ := ρ.consN original.added.length) rfl
    refine ⟨originalAdded ++ original.added, originalResult, .next stepOriginal tailOriginal, ?_, ?_⟩
    · simp only [CanonicalHead.Output.rename]
      rw [sameAdded, CanonicalHead.renameAdded_append]
    · simpa only [List.length_append, Lift.consN_consN,
        Nat.add_comm original.added.length originalAdded.length] using sameResult

end Lean4Lean.CanonicalDataHead
