/-! # Set models

`SetModel` is the set theory in which the model of the Klop environment is built: function
abstraction and application, dependent products, separation, replacement, pairing, unions
and an embedding of every Lean type of the lowest universe. No universe of sets is asked for.

`ZFSet.{0}` is one: `lam A f` is the graph of `f` on `A`, `app` is application of a graph
(with any value outside its domain), `pi A B` is the set of dependent functions, and `enc` is
an injection of the elements of a type into sets.

The interface is stated at the level the model uses, an applicative set theory, and not as
raw membership axioms.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

universe u

/-- An applicative set theory with dependent products, separation, replacement, pairing,
unions and an embedding of the Lean types of the lowest universe. -/
structure SetModel where
  /-- The sets. -/
  S : Type (u + 1)
  mem : S → S → Prop
  /-- Extensionality. -/
  ext : ∀ {x y}, (∀ z, mem z x ↔ mem z y) → x = y
  /-- `lam A f`: the function `f` restricted to the set `A`. -/
  lam : S → (S → S) → S
  /-- Application of a function to an argument. -/
  app : S → S → S
  app_lam : ∀ {A f x}, mem x A → app (lam A f) x = f x
  lam_ext : ∀ {A f g}, (∀ x, mem x A → f x = g x) → lam A f = lam A g
  /-- `pi A B`: the dependent functions on `A` with values in `B x`. -/
  pi : S → (S → S) → S
  mem_pi : ∀ {A B f}, mem f (pi A B) ↔ f = lam A (app f) ∧ ∀ x, mem x A → mem (app f x) (B x)
  /-- Separation. -/
  sep : S → (S → Prop) → S
  mem_sep : ∀ {A p x}, mem x (sep A p) ↔ mem x A ∧ p x
  /-- Replacement: the image of a set under a function. -/
  image : S → (S → S) → S
  mem_image : ∀ {A f y}, mem y (image A f) ↔ ∃ x, mem x A ∧ y = f x
  /-- Ordered pairs. -/
  pair : S → S → S
  pair_inj : ∀ {a b a' b'}, pair a b = pair a' b' → a = a' ∧ b = b'
  /-- Every type of the lowest Lean universe is a set. -/
  enc : {α : Type} → α → S
  enc_inj : ∀ {α : Type} {a b : α}, enc a = enc b → a = b
  set : Type → S
  mem_set : ∀ {α : Type} {x}, mem x (set α) ↔ ∃ a : α, x = enc a
  /-- Union of a set of sets. -/
  sUnion : S → S
  mem_sUnion : ∀ {A x}, mem x (sUnion A) ↔ ∃ y, mem y A ∧ mem x y

end VEnv.Strengthening
end Lean4Lean
