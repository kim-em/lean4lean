import Lean4Lean.Theory.Typing.EquationControlMeasure

/-! Order laws for comparing separately retained equation worlds. The
relation is the existing fixed-length control order, including the actual
original closure schedule. No common source cutoff is imposed. -/
namespace Lean4Lean.VEnv.EquationControlMeasure
set_option Elab.async false

private theorem lex_trans {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    (st : ∀ {a b c}, s a b → s b c → s a c)
    {a b c : α × β} (ab : Prod.Lex r s a b) (bc : Prod.Lex r s b c) :
    Prod.Lex r s a c := by
  cases ab with
  | left _ _ h =>
    cases bc with
    | left _ _ h' => exact .left _ _ (rt h h')
    | right _ _ => exact .left _ _ h
  | right _ h =>
    cases bc with
    | left _ _ h' => exact .left _ _ h'
    | right _ h' => exact .right _ (st h h')

private theorem lex_trichotomy {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    (rt : ∀ a b, r a b ∨ a = b ∨ r b a)
    (st : ∀ a b, s a b ∨ a = b ∨ s b a) (a b : α × β) :
    Prod.Lex r s a b ∨ a = b ∨ Prod.Lex r s b a := by
  obtain ⟨a, x⟩ := a
  obtain ⟨b, y⟩ := b
  rcases rt a b with h | rfl | h
  · exact .inl (.left _ _ h)
  · rcases st x y with h | rfl | h
    · exact .inl (.right _ h)
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.right _ h))
  · exact .inr (.inr (.left _ _ h))

theorem less_trans {count : Nat} {a b c : Key count}
    (ab : Less a b) (bc : Less b c) : Less a c := by
  induction count with
  | zero => exact lex_trans (r := Nat.lt) (s := Nat.lt) Nat.lt_trans Nat.lt_trans ab bc
  | succ count ih =>
    exact lex_trans (r := Nat.lt) (s := Prod.Lex Nat.lt (@Less count)) Nat.lt_trans
      (lex_trans (r := Nat.lt) (s := @Less count) Nat.lt_trans ih) ab bc

theorem less_trichotomy {count : Nat} (a b : Key count) :
    Less a b ∨ a = b ∨ Less b a := by
  induction count with
  | zero => exact lex_trichotomy Nat.lt_trichotomy Nat.lt_trichotomy a b
  | succ count ih => exact lex_trichotomy Nat.lt_trichotomy (lex_trichotomy Nat.lt_trichotomy ih) a b

theorem less_irrefl {count : Nat} (a : Key count) : ¬ Less a a := by
  induction a using (wellFounded count).induction with
  | h a ih => exact fun self => ih a self self

theorem less_asymm {count : Nat} {a b : Key count} (ab : Less a b) : ¬ Less b a :=
  fun ba => less_irrefl a (less_trans ab ba)

end Lean4Lean.VEnv.EquationControlMeasure
