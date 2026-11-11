import Lean4Lean.Theory.Typing.Strengthening.KlopModel.Red

/-! # Values of terms of type `T` in the term model of the Klop environment

`Val t i`: the raw term `t` has the value `i : ℤ/3`. `E` has value `0`; `C t` has the
successor of the value of `t`; values are closed under weak head expansion; and an `Eq.rec`
over `T` with endpoints of values `i`, `j` has the value of its minor premise when `i = j`,
and `i + 1` when `i ≠ j` and its major premise does not reduce to an `Eq.refl`. A redex with
distinct endpoints whose major premise reduces to `Eq.refl` has no value.

Values are unique (`Val.functional`) and `C E`, `E` have the distinct values `1`, `0`
(`val_CE`, `val_E`). What is still missing for `KlopEnv.Separated` is the semantic type
system and its soundness (`FIRST_PRINCIPLES.md` §9): that definitionally equal closed terms of
type `T` have the same value.
-/

namespace Lean4Lean
open VExpr

namespace VEnv.Strengthening.KlopModel

/-- The major premise does not reduce to a reflexivity proof. -/
def NoRefl (h : VExpr) : Prop := ∀ w α a, ¬ Reds h (VExpr.eqReflApp w α a)

inductive Val : VExpr → Fin 3 → Prop where
  | E : Val klopE 0
  | C : Val t i → Val (.app klopC t) (i + 1)
  | red : Red t t' → Val t' i → Val t i
  | recEq : Reds α klopT → Val a i → Val b i → Val m k →
      Val (VExpr.eqRecApp v w α a M m b h) k
  | recNe : Reds α klopT → Val a i → Val b j → i ≠ j → NoRefl h →
      Val (VExpr.eqRecApp v w α a M m b h) (i + 1)

theorem Reds.trans (h1 : Reds a b) (h2 : Reds b c) : Reds a c := by
  induction h1 with
  | rfl => exact h2
  | head h _ ih => exact .head h (ih h2)

/-- A reduction to a reflexivity proof factors through the first step. -/
theorem reds_refl_of_red (h : Red e e') (H : Reds e (VExpr.eqReflApp w α a)) :
    Reds e' (VExpr.eqReflApp w α a) := by
  cases H with
  | rfl => exact absurd h eqRefl_not_red
  | head h' H => cases h.deterministic h'; exact H

theorem NoRefl.red (h : Red e e') (H : NoRefl e) : NoRefl e' :=
  fun w α a R => H w α a (.head h R)

theorem NoRefl.of_red (h : Red e e') (H : NoRefl e') : NoRefl e :=
  fun w α a R => H w α a (reds_refl_of_red h R)

/-- The three ways an `Eq.rec` application has a value. -/
def RecCases (α a m b h : VExpr) (k : Fin 3) : Prop :=
  (Reds α klopT ∧ ∃ i, Val a i ∧ Val b i ∧ Val m k) ∨
  (Reds α klopT ∧ ∃ i j, Val a i ∧ Val b j ∧ i ≠ j ∧ NoRefl h ∧ k = i + 1) ∨
  ((∃ w' α' a', Reds h (VExpr.eqReflApp w' α' a')) ∧ Val m k)

theorem red_eqRecApp (H : Red (VExpr.eqRecApp v w α a M m b h) x) :
    (∃ h', Red h h' ∧ x = VExpr.eqRecApp v w α a M m b h') ∨
    ((∃ w' α' a', h = VExpr.eqReflApp w' α' a') ∧ x = m) := by
  generalize he : VExpr.eqRecApp v w α a M m b h = y at H
  cases H with
  | beta => simp [VExpr.eqRecApp] at he
  | fix => simp [VExpr.eqRecApp] at he
  | appL h'' =>
    simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact absurd h'' eqRec5_not_red
  | major h'' =>
    simp only [VExpr.eqRecApp, VExpr.app.injEq, VExpr.const.injEq, List.cons.injEq] at he
    obtain ⟨⟨⟨⟨⟨⟨⟨-, rfl, rfl, -⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := he
    exact .inl ⟨_, h'', rfl⟩
  | iota =>
    simp only [VExpr.eqRecApp, VExpr.app.injEq] at he
    obtain ⟨⟨⟨-, rfl⟩, -⟩, rfl⟩ := he
    exact .inr ⟨⟨_, _, _, rfl⟩, rfl⟩

theorem Val.eqRecApp_inv (H : Val t k) (ht : t = VExpr.eqRecApp v w α a M m b h) :
    RecCases α a m b h k := by
  induction H generalizing h with
  | E => simp [VExpr.eqRecApp] at ht
  | C => simp [VExpr.eqRecApp] at ht
  | red r _ ih =>
    subst ht
    rcases red_eqRecApp r with ⟨h', rh, rfl⟩ | ⟨⟨w', α', a', rfl⟩, rfl⟩
    · rcases ih rfl with ⟨hα, i, ha, hb, hm⟩ | ⟨hα, i, j, ha, hb, hne, hn, rfl⟩ |
        ⟨⟨w', α', a', R⟩, hm⟩
      · exact .inl ⟨hα, i, ha, hb, hm⟩
      · exact .inr (.inl ⟨hα, i, j, ha, hb, hne, hn.of_red rh, rfl⟩)
      · exact .inr (.inr ⟨⟨w', α', a', .head rh R⟩, hm⟩)
    · exact .inr (.inr ⟨⟨_, _, _, .rfl⟩, by assumption⟩)
  | recEq hα ha hb hm =>
    simp only [VExpr.eqRecApp, VExpr.app.injEq, VExpr.const.injEq] at ht
    obtain ⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, -⟩, rfl⟩, rfl⟩, rfl⟩ := ht
    exact .inl ⟨hα, _, ha, hb, hm⟩
  | recNe hα ha hb hne hn =>
    simp only [VExpr.eqRecApp, VExpr.app.injEq, VExpr.const.injEq] at ht
    obtain ⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, -⟩, rfl⟩, rfl⟩, rfl⟩ := ht
    exact .inr (.inl ⟨hα, _, _, ha, hb, hne, hn, rfl⟩)

theorem klopE_not_red : ¬ Red klopE e := by
  intro h
  rcases h.head with ⟨_, _, h⟩ | h | ⟨_, h, _⟩ <;> simp [hd] at h

theorem klopC_app_not_red : ¬ Red (.app klopC t) e := by
  intro h
  rcases h.head with ⟨_, _, h⟩ | h | ⟨_, h, _⟩ <;> simp [hd] at h

theorem Val.E_inv (H : Val klopE k) : k = 0 := by
  generalize he : klopE = t at H
  cases H with
  | E => rfl
  | C => cases he
  | red r => subst he; exact absurd r klopE_not_red
  | recEq => simp [VExpr.eqRecApp] at he
  | recNe => simp [VExpr.eqRecApp] at he

theorem Val.C_inv (H : Val (.app klopC t) k) : ∃ i, Val t i ∧ k = i + 1 := by
  generalize he : VExpr.app klopC t = s at H
  cases H with
  | E => cases he
  | C h => cases he; exact ⟨_, h, rfl⟩
  | red r => subst he; exact absurd r klopC_app_not_red
  | recEq => simp [VExpr.eqRecApp] at he
  | recNe => simp [VExpr.eqRecApp] at he

/-- Values are preserved by weak head reduction. -/
theorem Val.red_inv (H : Val t k) (r : Red t t') : Val t' k := by
  induction H generalizing t' with
  | E => exact absurd r klopE_not_red
  | C => exact absurd r klopC_app_not_red
  | red r' h _ => cases r.deterministic r'; exact h
  | recEq hα ha hb hm =>
    rcases red_eqRecApp r with ⟨h', _, rfl⟩ | ⟨_, rfl⟩
    · exact .recEq hα ha hb hm
    · exact hm
  | recNe hα ha hb hne hn =>
    rcases red_eqRecApp r with ⟨h', rh, rfl⟩ | ⟨⟨w', α', a', rfl⟩, rfl⟩
    · exact .recNe hα ha hb hne (hn.red rh)
    · exact absurd .rfl (hn _ _ _)

/-- **Values are unique.** -/
theorem Val.functional (H1 : Val t i) (H2 : Val t j) : i = j := by
  induction H1 generalizing j with
  | E => exact H2.E_inv.symm
  | C _ ih =>
    obtain ⟨_, h, rfl⟩ := H2.C_inv
    rw [ih h]
  | red r _ ih => exact ih (H2.red_inv r)
  | recEq _ _ _ _ iha ihb ihm =>
    rcases H2.eqRecApp_inv rfl with ⟨-, _, _, _, hm⟩ | ⟨-, i', j', ha, hb, hne, -, rfl⟩ | ⟨-, hm⟩
    · exact ihm hm
    · exact absurd ((iha ha).symm.trans (ihb hb)) hne
    · exact ihm hm
  | recNe _ _ _ hne hn iha ihb =>
    rcases H2.eqRecApp_inv rfl with ⟨-, i', ha, hb, -⟩ | ⟨-, i', j', ha, -, -, -, rfl⟩ |
      ⟨⟨w', α', a', R⟩, -⟩
    · exact absurd ((iha ha).trans (ihb hb).symm) hne
    · rw [iha ha]
    · exact absurd R (hn _ _ _)

theorem val_E : Val klopE 0 := .E
theorem val_CE : Val (.app klopC klopE) 1 := .C .E

/-- `C E` and `E` have distinct values. -/
theorem val_CE_ne_E (h1 : Val (.app klopC klopE) i) (h2 : Val klopE i) : False := by
  have a := h1.functional val_CE
  have b := h2.functional val_E
  exact absurd (a.symm.trans b) (by decide)

end VEnv.Strengthening.KlopModel
end Lean4Lean
