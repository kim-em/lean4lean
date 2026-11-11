import Lean4Lean.Theory.Typing.Strengthening.KlopCounterexample

/-! # Weak head reduction for the term model of the Klop environment

First brick of the term model planned in `FIRST_PRINCIPLES.md` §9, which is to prove
`KlopEnv.Separated`. `Red` is one step of weak head reduction on raw terms: β, unfolding of
`Fix`, and ι for `Eq.rec` at a syntactic `Eq.refl`, with the major premise reduced first.
`C` is not unfolded: the model gives `C t` the successor of the value of `t` directly.

The relation is deterministic (`Red.deterministic`). It is defined before the model so that
the model may refer to its negation ("the proof does not reduce to `Eq.refl`").
-/

namespace Lean4Lean
open VExpr

namespace VEnv.Strengthening.KlopModel

/-- One step of weak head reduction. -/
inductive Red : VExpr → VExpr → Prop where
  | beta : Red (.app (.lam A b) a) (b.inst a)
  | fix : Red klopFix klopFixBody
  | appL : Red f f' → Red (.app f a) (.app f' a)
  | major : Red h h' →
      Red (VExpr.eqRecApp v w α a M m b h) (VExpr.eqRecApp v w α a M m b h')
  | iota : Red (VExpr.eqRecApp v w α a M m b (VExpr.eqReflApp w' α' a')) m

/-- Weak head reduction. -/
inductive Reds : VExpr → VExpr → Prop where
  | rfl : Reds e e
  | head : Red e e' → Reds e' e'' → Reds e e''

/-- The head of an application spine. -/
def hd : VExpr → VExpr
  | .app f _ => hd f
  | e => e

/-- The number of arguments of an application spine. -/
def nargs : VExpr → Nat
  | .app f _ => nargs f + 1
  | _ => 0

/-- A weak head redex is headed by a λ, by `Fix`, or by `Eq.rec` applied to at least six
arguments. -/
theorem Red.head (H : Red e e') :
    (∃ A b, hd e = .lam A b) ∨ hd e = klopFix ∨ (∃ ls, hd e = .const ``Eq.rec ls ∧ 6 ≤ nargs e) := by
  induction H with
  | beta => exact .inl ⟨_, _, rfl⟩
  | fix => exact .inr (.inl rfl)
  | appL _ ih =>
    rcases ih with h | h | ⟨ls, h, hn⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨ls, h, Nat.le_succ_of_le hn⟩)
  | major _ _ => exact .inr (.inr ⟨_, rfl, Nat.le_refl _⟩)
  | iota => exact .inr (.inr ⟨_, rfl, Nat.le_refl _⟩)

/-- `Eq.refl α a` does not reduce. -/
theorem eqRefl_not_red : ¬ Red (VExpr.eqReflApp w α a) e := by
  intro h
  rcases h.head with ⟨_, _, h⟩ | h | ⟨_, h, _⟩ <;> simp [hd, VExpr.eqReflApp] at h

/-- `Eq.rec` applied to five arguments does not reduce. -/
theorem eqRec5_not_red :
    ¬ Red (.app (.app (.app (.app (.app (.const ``Eq.rec ls) α) a) M) m) b) e := by
  intro h
  rcases h.head with ⟨_, _, h⟩ | h | ⟨_, _, h⟩
  · simp [hd] at h
  · simp [hd] at h
  · simp [nargs] at h

/-- Weak head reduction is deterministic. -/
theorem Red.deterministic (h1 : Red e e₁) (h2 : Red e e₂) : e₁ = e₂ := by
  induction h1 generalizing e₂ with
  | beta =>
    generalize he : VExpr.app (.lam _ _) _ = x at h2
    cases h2 with
    | beta => cases he; rfl
    | fix => cases he
    | appL h => cases he; cases h
    | major => simp [VExpr.eqRecApp] at he
    | iota => simp [VExpr.eqRecApp] at he
  | fix =>
    generalize he : klopFix = x at h2
    cases h2 <;> first | rfl | cases he | simp [VExpr.eqRecApp] at he
  | @appL f f' a h ih =>
    generalize he : VExpr.app f a = x at h2
    cases h2 with
    | beta => cases he; cases h
    | fix => cases he
    | appL h' => cases he; rw [ih h']
    | major =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h eqRec5_not_red
    | iota =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h eqRec5_not_red
  | @major h h' v w α a M m b hh ih =>
    generalize he : VExpr.eqRecApp v w α a M m b h = x at h2
    cases h2 with
    | beta => simp [VExpr.eqRecApp] at he
    | fix => simp [VExpr.eqRecApp] at he
    | appL h'' =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h'' eqRec5_not_red
    | major h'' =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq, VExpr.const.injEq, List.cons.injEq] at he
      obtain ⟨⟨⟨⟨⟨⟨⟨-, rfl, rfl, -⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := he
      rw [ih h'']
    | iota =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact absurd hh eqRefl_not_red
  | @iota v w α a M m b w' α' a' =>
    generalize he : VExpr.eqRecApp v w α a M m b (VExpr.eqReflApp w' α' a') = x at h2
    cases h2 with
    | beta => simp [VExpr.eqRecApp] at he
    | fix => simp [VExpr.eqRecApp] at he
    | appL h'' =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h'' eqRec5_not_red
    | major h'' =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact absurd h'' eqRefl_not_red
    | iota =>
      simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
      obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := he
      rfl

end VEnv.Strengthening.KlopModel
end Lean4Lean
