import Lean4Lean.Theory.Typing.CanonicalHeadTrace

/-! Reflect a canonical trace through an initial context renaming. Total
step naturality recovers each original step, including its fresh telescope;
new proof slots remain fixed under the successively extended renaming. -/

namespace Lean4Lean.CanonicalHead
open VExpr InductiveSignature NativeRecursorData

theorem Trace.unrename {registry : Registry} (hc : registry.Scoped)
    {expression result : VExpr} {added : List VExpr} {ρ : Lift}
    (h : Trace registry (expression.lift' ρ) added result) :
    ∃ baseAdded baseResult,
      Trace registry expression baseAdded baseResult ∧
      added = renameAdded ρ baseAdded ∧
      result = baseResult.lift' (ρ.consN baseAdded.length) := by
  generalize hs : expression.lift' ρ = source at h
  induction h generalizing expression ρ with
  | refl => exact ⟨[], expression, .refl, rfl, hs.symm⟩
  | @next source out added result hstep htrace ih =>
    rw [← hs, step_rename hc] at hstep
    obtain ⟨baseOut, hbase, heq⟩ := Option.map_eq_some_iff.mp hstep
    subst out
    obtain ⟨baseAdded, baseResult, htraceBase, ha, hr⟩ :=
      ih (expression := baseOut.result) (ρ := ρ.consN baseOut.added.length) rfl
    refine ⟨baseAdded ++ baseOut.added, baseResult, .next hbase htraceBase, ?_, ?_⟩
    · simp only [Output.rename]
      rw [ha, renameAdded_append]
    · simpa only [List.length_append, Lift.consN_consN,
        Nat.add_comm baseOut.added.length baseAdded.length] using hr

end Lean4Lean.CanonicalHead
