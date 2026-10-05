import Lean4Lean.Theory.Typing.Basic

/-!
Run: lake env lean docs/inductives/OneSidedBudgetObstruction.lean

This checks a limitation of the proposed raw, finite-index simulation:
charge the left evaluation, allow arbitrarily many right steps, and compare
the resulting heads. Such a relation is not transitive at a fixed index.

The expressions are actual VExprs, typable at the same type using only the
production Basic rules. Evaluation below is the pure weak-head beta fragment;
no normalization, uniqueness, injectivity, or environment theorem is imported.
The counterexample uses only literal heads and one beta step. It survives
extensions whose application rules cost at least one step and whose literal
Sort/Pi heads retain their tags.

This does NOT refute a relation additionally requiring an object-language
equality proof: no equality between the delayed sort and the Pi is supplied.
It refutes deriving the necessary transitivity law from this raw finite-index
observation clause alone. In a proof by outer budget induction, transitivity
still needs a justified way to inspect the first comparison's middle trace,
whose cost can exceed the available budget.
-/

namespace Lean4Lean.FoundationOneSidedBudgetObstruction
open VExpr VEnv

def sortType : VExpr := .sort (.succ .zero)
def atom : VExpr := .sort .zero
def product : VExpr := .forallE atom atom
def delayed : VExpr := .app (.lam sortType (.bvar 0)) atom

inductive Eval : Nat → VExpr → VExpr → Prop where
  | sort : Eval 0 (.sort u) (.sort u)
  | pi : Eval 0 (.forallE A B) (.forallE A B)
  | lam : Eval 0 (.lam A body) (.lam A body)
  | app : Eval fnCost fn (.lam A body) → Eval bodyCost (body.inst arg) value →
      Eval (fnCost + bodyCost + 1) (.app fn arg) value

def SameHead : VExpr → VExpr → Prop
  | .sort u, .sort v => u ≈ v
  | .forallE .., .forallE .. => True
  | .lam .., .lam .. => True
  | _, _ => False

def Sim (budget : Nat) (left right : VExpr) : Prop :=
  ∀ cost value, cost ≤ budget → Eval cost left value →
    ∃ rightCost rightValue, Eval rightCost right rightValue ∧ SameHead value rightValue

theorem delayed_eval : Eval 1 delayed atom :=
  .app (fnCost := 0) (bodyCost := 0) (A := sortType)
    (body := .bvar 0) (arg := atom) .lam .sort

theorem atom_sim_delayed : Sim 0 atom delayed := by
  intro cost value _ he
  cases he
  exact ⟨1, atom, delayed_eval, rfl⟩

theorem delayed_sim_product : Sim 0 delayed product := by
  intro cost value hc he
  have hzero : cost = 0 := Nat.eq_zero_of_le_zero hc
  subst cost
  cases he

theorem atom_not_sim_product : ¬Sim 0 atom product := by
  intro h
  obtain ⟨_, _, he, hh⟩ := h 0 atom (Nat.le_refl _) .sort
  cases he
  exact hh

theorem not_transitive :
    ¬∀ x y z, Sim 0 x y → Sim 0 y z → Sim 0 x z := by
  intro h
  exact atom_not_sim_product
    (h atom delayed product atom_sim_delayed delayed_sim_product)

theorem atom_typed (env : VEnv) : env.HasType 0 [] atom sortType :=
  .sortDF trivial trivial rfl

theorem product_typed (env : VEnv) : env.HasType 0 [] product sortType := by
  have hp : env.HasType 0 [] product
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)
  have hc : env.IsDefEq 0 [] (.sort (.imax (.succ .zero) (.succ .zero)))
      sortType (.sort (.succ (.imax (.succ .zero) (.succ .zero)))) :=
    .sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_self
  exact .defeqDF hc hp

theorem delayed_eq_atom (env : VEnv) : env.IsDefEq 0 [] delayed atom sortType :=
  .beta (.bvar .zero) (atom_typed env)

theorem same_type_counterexample (env : VEnv) :
    env.HasType 0 [] atom sortType ∧
    env.HasType 0 [] delayed sortType ∧
    env.HasType 0 [] product sortType ∧
    Sim 0 atom delayed ∧ Sim 0 delayed product ∧ ¬Sim 0 atom product := by
  have hd := delayed_eq_atom env
  exact ⟨atom_typed env, .trans hd hd.symm, product_typed env,
    atom_sim_delayed, delayed_sim_product, atom_not_sim_product⟩

/-- Delaying more than the budget shows the failure is not a choice of base index. -/
def delayN : Nat → VExpr
  | 0 => atom
  | n + 1 => .app (.lam sortType (.bvar 0)) (delayN n)

theorem delayN_eval (n : Nat) : Eval n (delayN n) atom := by
  induction n with
  | zero => exact .sort
  | succ n ih =>
    have hb : Eval n ((VExpr.bvar 0).inst (delayN n)) atom := by
      simpa only [inst, instVar_zero] using ih
    simpa only [delayN, Nat.zero_add] using
      (Eval.app (fnCost := 0) (bodyCost := n) (A := sortType)
        (body := .bvar 0) (arg := delayN n) .lam hb)

theorem delayN_eval_unique (he : Eval cost (delayN n) value) :
    cost = n ∧ value = atom := by
  induction n generalizing cost value with
  | zero => cases he; exact ⟨rfl, rfl⟩
  | succ n ih =>
    cases he with
    | app hf hb =>
      cases hf
      simp only [inst, instVar_zero] at hb
      obtain ⟨hc, hv⟩ := ih hb
      exact ⟨by omega, hv⟩

theorem delayN_eq_atom (env : VEnv) (n : Nat) :
    env.IsDefEq 0 [] (delayN n) atom sortType := by
  induction n with
  | zero => exact atom_typed env
  | succ n ih =>
    have hx : env.HasType 0 [] (delayN n) sortType := .trans ih ih.symm
    have hb : env.IsDefEq 0 [] (delayN (n + 1)) (delayN n) sortType := by
      simpa only [delayN, sortType, lift, liftN, inst, instVar_zero] using
        (IsDefEq.beta (IsDefEq.bvar (Γ := [sortType]) Lookup.zero) hx)
    exact hb.trans ih

theorem every_budget_counterexample (budget : Nat) (env : VEnv) :
    env.HasType 0 [] atom sortType ∧
    env.HasType 0 [] (delayN (budget + 1)) sortType ∧
    env.HasType 0 [] product sortType ∧
    Sim budget atom (delayN (budget + 1)) ∧
    Sim budget (delayN (budget + 1)) product ∧ ¬Sim budget atom product := by
  have hd := delayN_eq_atom env (budget + 1)
  refine ⟨atom_typed env, .trans hd hd.symm, product_typed env, ?_, ?_, ?_⟩
  · intro cost value _ he
    cases he
    exact ⟨budget + 1, atom, delayN_eval _, rfl⟩
  · intro cost value hc he
    have hcost := (delayN_eval_unique he).1
    omega
  · intro h
    obtain ⟨_, _, he, hh⟩ := h 0 atom (Nat.zero_le _) .sort
    cases he
    exact hh

#print axioms not_transitive
#print axioms same_type_counterexample
#print axioms every_budget_counterexample

end Lean4Lean.FoundationOneSidedBudgetObstruction
