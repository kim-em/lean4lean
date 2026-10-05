import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules

/-! Separate motives for paired-original interpretation, assigned-type
comparison, and expression-query reindexing. Same-original paired body calls
remain unary fundamental calls; they do not double the original closure. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

inductive RichPhase where
  | fundamental
  | assignedComparison
  | expressionReindex

def RichPhase.code : RichPhase → Nat
  | .fundamental => 0
  | .assignedComparison => 1
  | .expressionReindex => 2

def richSchedule (phase : RichPhase) (cost : Nat) : Nat := 3 * cost + phase.code

theorem richSchedule_strict (decrease : small < large) (first second : RichPhase) :
    richSchedule first small < richSchedule second large := by
  cases first <;> cases second <;> simp only [richSchedule, RichPhase.code] <;> omega

theorem richReindex_to_assignedComparison (cost : Nat) :
    richSchedule .assignedComparison cost < richSchedule .expressionReindex cost := by
  simp [richSchedule, RichPhase.code]

theorem richComparison_to_fundamental (cost : Nat) :
    richSchedule .fundamental cost < richSchedule .assignedComparison cost := by
  simp [richSchedule, RichPhase.code]

/-- The reverse same-cost edge is deliberately unavailable: comparison must
pay for any expression reindex using a strict original closure decrease. -/
theorem richComparison_no_sameCost_reindex (cost : Nat) :
    ¬ richSchedule .expressionReindex cost < richSchedule .assignedComparison cost := by
  simp [richSchedule, RichPhase.code]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
