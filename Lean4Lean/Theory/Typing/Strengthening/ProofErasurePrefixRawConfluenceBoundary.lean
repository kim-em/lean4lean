import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGuardBetaBoundary

/-! # Raw prefix computation is not confluent

A proof-marker eta guard permits a prefix contraction before beta changes one
endpoint. After beta the guard is impossible, leaving a fixed prefix. The other
branch reaches a fixed lambda. These are raw shapes, not jointly typed erasures.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.PrefixRawConfluenceBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open GuardBetaBoundary
variable [Params]

/-- One prefix stage over pure beta comparison. -/
abbrev Step := RawCheckedPrefixKPrimitive (fun _ _ => False)

/-- A raw prefix whose first endpoint contains the unchecked marker eta guard. -/
def source : ProofShape :=
  eqRecBeforeMajor .zero .zero (.sort .zero) expanded (.sort .zero) (.sort .zero) ident
/-- Computing that endpoint first destroys its guard. -/
def stuck : ProofShape :=
  eqRecBeforeMajor .zero .zero (.sort .zero) reduced (.sort .zero) (.sort .zero) ident
/-- Contracting the prefix first retains a lambda after the same endpoint beta. -/
def done : ProofShape := .lam (eqProofType .zero (.sort .zero) reduced ident) (.sort .zero)

/-- The beta-first branch is a literal fixed point of the whole raw fragment. -/
theorem stuck_normal : NormalSyntax Step stuck := by
  simp only [stuck, eqRecBeforeMajor, reduced, ident, NormalSyntax]
  repeat' constructor
  all_goals solve
    | (intro out H; cases H <;> exact GuardBetaBoundary.not_compare (Step := fun _ _ => False) (fun H => H.elim) ‹_›)
    | (intro A b H; cases H)

/-- The prefix-first branch is also a literal fixed point. -/
theorem done_normal : NormalSyntax Step done := by
  simp only [done, eqProofType, reduced, ident, NormalSyntax]
  repeat' constructor
  all_goals solve
    | (intro out H; cases H)
    | (intro A b H; cases H)

/-- Beta can reduce the guarded endpoint without contracting the prefix. -/
theorem source_stuck : Compute Step source stuck :=
  .app (.app (.app (.app (.app .refl .refl) (.beta GuardBetaBoundary.beta)) .refl) .refl) .refl

/-- Prefix contraction followed by annotation beta reaches the fixed lambda. -/
theorem source_done : Compute Step source done := by
  apply Compute.trans (.base (.intro GuardBetaBoundary.guard))
  exact .lam (.app (.app (.app .refl .refl) (.beta GuardBetaBoundary.beta)) .refl) .refl

/-- The two raw branches have no common computational endpoint. -/
theorem no_join : ¬ ∃ d, Compute Step stuck d ∧ Compute Step done d := by
  rintro ⟨d, HS, HD⟩
  have E := (stuck_normal.fixed HS).symm.trans (done_normal.fixed HD)
  cases E

/-- Even beta plus a single checked prefix stage is not confluent on arbitrary
raw syntax. Any confluence proof must preserve the typed-source restriction. -/
theorem not_confluent :
    ¬ (∀ {a b c}, Compute Step a b → Compute Step a c →
      ∃ d, Compute Step b d ∧ Compute Step c d) := by
  intro H
  exact no_join (H source_stuck source_done)

end Lean4Lean.VEnv.Strengthening.ProofShape.PrefixRawConfluenceBoundary
