/-! # Universe towers

`UniverseTower` is the hypothesis of `not_weakN_iff_of_tower`: a set-theoretic universe with
function abstraction and application, dependent products, separation, pairing, an embedding
of every small Lean type, and a tower of universes `U 0 ∈ U 1 ∈ …`, each closed under these
operations.

Any sequence of inaccessible cardinals `κ₀ < κ₁ < …` gives one: `S` is the type of sets,
`U n = V_κₙ`, `lam A f` is the graph of `f` on `A`, `app` is application of a graph (anything
outside the domain), `pi A B` is the set of dependent functions, `enc` is any injection of the
elements of a small type into sets. Only the types of cardinality at most the continuum
(`ContinuumSized`) are required to lie in `U 0`. Lean proves the existence of `n` inaccessible
cardinals for every numeral `n` and not of a sequence of them, which is why the tower is a
hypothesis.

The interface is stated at the level the model uses (applicative set theory) and not as raw
membership axioms.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

universe u

/-- `α` has at most the cardinality of the continuum: it injects into the sets of natural
numbers. -/
class ContinuumSized (α : Type) : Prop where
  out : ∃ f : α → Nat → Prop, ∀ a b, f a = f b → a = b

theorem ContinuumSized.of_injective {α β : Type} [h : ContinuumSized β] (g : α → β)
    (hg : ∀ a b, g a = g b → a = b) : ContinuumSized α := by
  obtain ⟨f, hf⟩ := h.out
  exact ⟨fun a => f (g a), fun a b e => hg _ _ (hf _ _ e)⟩

instance : ContinuumSized Nat := ⟨fun n m => n = m, fun a b e => by
  have := congrFun e a; simp at this; exact this.symm⟩

structure UniverseTower where
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
