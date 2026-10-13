import Lean4Lean.Theory.Typing.Strengthening.MarkedDevelopments

/-! # Created redexes can require arbitrarily many marking rounds

The family `chain n k` is typed in every environment and context. It consists only of
identities at successively higher simple types. For positive `n`, exactly one link is
removed by a complete development of all currently present beta redexes. Thus no
fixed number of marking rounds eliminates all created redexes, even in this
normalizing fragment. This refutes a uniform bound, not standardisation or a bound
depending on the input derivation.
-/

namespace Lean4Lean.VEnv.Strengthening.Developments
open VExpr

/-- A closed simple type tower, starting at `Prop`. -/
def tower : Nat → VExpr
  | 0 => .sort .zero
  | n + 1 => .forallE (tower n) (tower n)

theorem tower_liftN (n m k : Nat) : (tower n).liftN m k = tower n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [tower, liftN, ih]

theorem tower_inst (n : Nat) (a : VExpr) (k : Nat) : (tower n).inst a k = tower n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [tower, VExpr.inst, ih]

theorem tower_typed (env : VEnv) (U : Nat) (Γ : List VExpr) (n : Nat) :
    env.HasType U Γ (tower n) (.sort (.succ .zero)) := by
  induction n generalizing Γ with
  | zero => exact .sort trivial
  | succ n ih =>
    have h := HasType.forallE (ih Γ) (ih (tower n :: Γ))
    exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl).defeq h

def ident (k : Nat) : VExpr := .lam (tower k) (.bvar 0)

theorem ident_typed (env : VEnv) (U : Nat) (Γ : List VExpr) (k : Nat) :
    env.HasType U Γ (ident k) (tower (k + 1)) := by
  have h := HasType.lam (tower_typed env U Γ k) (IsDefEq.bvar (Lookup.zero (ty := tower k)))
  simpa only [ident, tower, lift, tower_liftN] using h

/-- A left-associated spine of identities. The only initial beta redex is the
innermost application; each contraction exposes the next one. -/
def chain : Nat → Nat → VExpr
  | 0, k => ident k
  | n + 1, k => .app (chain n (k + 1)) (ident k)

theorem chain_typed (env : VEnv) (U : Nat) (Γ : List VExpr) (n k : Nat) :
    env.HasType U Γ (chain n k) (tower (k + 1)) := by
  induction n generalizing k with
  | zero => exact ident_typed env U Γ k
  | succ n ih =>
    have hf : env.HasType U Γ (chain n (k + 1))
        (.forallE (tower (k + 1)) (tower (k + 1))) := ih (k + 1)
    simpa only [tower_inst, chain] using hf.app (ident_typed env U Γ k)

theorem round_tower (n : Nat) : Term.round (tower n) = tower n := by
  induction n with
  | zero => rfl
  | succ n ih => change VExpr.forallE (Term.round (tower n)) (Term.round (tower n)) = _; rw [ih]; rfl

theorem round_ident (k : Nat) : Term.round (ident k) = ident k := by
  change VExpr.lam (Term.round (tower k)) (.bvar 0) = _
  rw [round_tower]; rfl

/-- Developing all marks leaves the rest of the spine as newly created redexes. -/
theorem round_chain_succ (n k : Nat) : Term.round (chain (n + 1) k) = chain n k := by
  induction n generalizing k with
  | zero =>
    change Term.round (.app (.lam (tower (k + 1)) (.bvar 0)) (ident k)) = ident k
    rw [Term.round_app_lam, round_ident]
    simp [Term.round, Term.markAll, Term.develop, VExpr.inst, instVar]
  | succ n ih =>
    change Term.round (.app (.app (chain n (k + 2)) (ident (k + 1))) (ident k)) = _
    rw [Term.round_app_app]
    change VExpr.app (Term.round (chain (n + 1) (k + 1))) (Term.round (ident k)) = _
    rw [ih, round_ident]
    rfl

/-- Perform a specified number of complete-development rounds. -/
def rounds : Nat → VExpr → VExpr
  | 0, e => e
  | n + 1, e => rounds n (Term.round e)

theorem rounds_chain (r n k : Nat) : rounds r (chain (r + n) k) = chain n k := by
  induction r with
  | zero => simp [rounds]
  | succ r ih =>
    rw [show r + 1 + n = (r + n) + 1 by omega, rounds, round_chain_succ]
    exact ih

/-- A beta redex occurs somewhere in an expression, including under binders. -/
def HasBeta : VExpr → Prop
  | .bvar _ | .sort _ | .const .. => False
  | .lam A b | .forallE A b => HasBeta A ∨ HasBeta b
  | .proj _ _ m => HasBeta m
  | .app f a => (∃ A b, f = .lam A b) ∨ HasBeta f ∨ HasBeta a

theorem chain_succ_hasBeta (n k : Nat) : HasBeta (chain (n + 1) k) := by
  induction n generalizing k with
  | zero => exact .inl ⟨_, _, rfl⟩
  | succ n ih => exact .inr (.inl (ih (k + 1)))

/-- No fixed number of rounds suffices, even for terms typed at `Prop → Prop`.
In particular this rules out a universal two-marking repair. -/
theorem no_uniform_round_bound (env : VEnv) (U : Nat) (Γ : List VExpr) (r : Nat) :
    ∃ e, env.HasType U Γ e (tower 1) ∧ HasBeta (rounds r e) := by
  refine ⟨chain (r + 1) 0, chain_typed env U Γ (r + 1) 0, ?_⟩
  rw [rounds_chain]
  exact chain_succ_hasBeta 0 0

end Lean4Lean.VEnv.Strengthening.Developments
