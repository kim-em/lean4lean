import Lean

-- Run: lake env lean docs/inductives/history/BudgetStratificationObstruction.lean

/-!
A termination obstruction for one proposed foundation, not for inductive
verification or for all step-indexed logical relations.

The proposal indexes a relation by (ambient budget, observed profile depth).
Native capture guards may inspect any profile at a smaller budget. To combine
function exposure with an argument observed at a larger budget, the proposed
arrow clause tests arbitrary future budgets at a smaller profile depth.
These two specific recursive-call permissions form a cycle.
-/

namespace Lean4Lean.FoundationBudgetObstruction

abbrev State := Nat × Nat

/-- The child is the first argument, and the parent the second. -/
inductive Call : State → State → Prop where
  | capture {budget resultDepth captureDepth : Nat} :
      Call (budget, captureDepth) (budget + 1, resultDepth)
  | futureArgument {budget futureBudget depth : Nat} :
      budget ≤ futureBudget → Call (futureBudget, depth) (budget, depth + 1)

/-- Every well-founded relation excludes even a two-edge cycle. -/
theorem no_back_edge {α : Sort u} {r : α → α → Prop} (W : WellFounded r)
    {x y : α} (hxy : r x y) (hyx : r y x) : False := by
  have step : ∀ a b, r b a → ¬r a b := by
    intro a
    induction a using W.induction with
    | h a ih =>
      intro b hba hab
      exact ih b hba a hab hba
  exact step y x hxy hyx

/-- Raising the profile in a capture and raising the budget in its arrow
returns to the original state. -/
theorem two_cycle (budget depth : Nat) :
    Call (budget, depth + 1) (budget + 1, depth) ∧
      Call (budget + 1, depth) (budget, depth + 1) :=
  ⟨.capture, .futureArgument (Nat.le_succ _)⟩

theorem not_wellFounded : ¬WellFounded Call := by
  intro W
  have h := two_cycle 0 0
  exact no_back_edge W h.1 h.2

/-- No ordinal, lexicographic tuple, or other well-founded target can assign
strictly decreasing measures to all these proposed calls. -/
theorem no_decreasing_measure {α : Sort u} {r : α → α → Prop}
    (W : WellFounded r) :
    ¬∃ measure : State → α,
      ∀ child parent, Call child parent → r (measure child) (measure parent) := by
  rintro ⟨measure, decrease⟩
  have h := two_cycle 0 0
  exact no_back_edge W (decrease _ _ h.1) (decrease _ _ h.2)

#print axioms not_wellFounded
#print axioms no_decreasing_measure

end Lean4Lean.FoundationBudgetObstruction

/-!
A pressure family for *proposed consuming-budget observations*.
The definitions and kernel conversion checks below have no budget semantics.
The `autoPromoteIndices` option is disabled to keep X as a constructor data
field. With default promotion, Lean instead produces one parameter, no
indices, no constructor fields, and an isK recursor. That different declaration
can reduce its opaque singleton major without the proposed data-capture guard.

For the declaration below, `wrap_eq` explicitly checks that `rfl` fails and
then proves propositional equality using proof irrelevance, congruence, and
constructor iota. The recursor has isK=false. Thus this file does not claim
that native kernel reduction traverses the tower as guarded observations do.

Conditional budget argument only: suppose exact-sort observations satisfy
  O_(b+1)(wrap X, sort) iff O_b(X, sort),
  O_b(Prop, sort), and no O_0(wrap X, sort),
and offer no extra observation rule bypassing that guard. Then induction
gives O_b(tower k, sort) iff k <= b. This lower bound follows from THOSE
proposed observation rules; no such observation relation is defined here.
Consequently even one fixed input profile (sort) can have syntactic realizers
requiring arbitrarily large observation budgets. It is not a lower bound on
native Lean reduction and is not a counterexample to all budget semantics.
-/
namespace Lean4Lean.FoundationBudgetObstruction.SourcePressure

set_option inductive.autoPromoteIndices false in
inductive Box : Type → Prop where
  | mk (X : Type) : Box X

variable (q : (X : Type) → Box X)

def wrap (X : Type) : Type :=
  Box.rec (motive := fun _ _ => Type) (fun X => X) (q X)

theorem wrap_eq (X : Type) : wrap q X = X := by
  fail_if_success exact rfl
  have h : q X = Box.mk X := rfl
  exact congrArg
    (fun p : Box X => Box.rec (motive := fun _ _ => Type) (fun X => X) p) h

def tower : Nat → Type
  | 0 => Prop
  | n + 1 => wrap q (tower n)

theorem tower_step (n : Nat) : tower q (n + 1) = tower q n :=
  wrap_eq q (tower q n)

theorem tower_eq (n : Nat) : tower q n = Prop := by
  induction n with
  | zero => rfl
  | succ n ih => exact (tower_step q n).trans ih

#print Box.rec
#print axioms wrap_eq
#print axioms tower_step
#print axioms tower_eq

run_cmd do
  let .recInfo info ← Lean.getConstInfo ``Box.rec
    | throwError "Box.rec did not have recursor metadata"
  if info.k || info.numParams != 0 || info.numIndices != 1 then
    throwError "Expected an unpromoted one-index recursor with isK=false"
  Lean.logInfo m!"Box.rec isK={info.k}, numParams={info.numParams}, numIndices={info.numIndices}, numMotives={info.numMotives}, numMinors={info.numMinors}"

end Lean4Lean.FoundationBudgetObstruction.SourcePressure
