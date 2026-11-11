/-! # Universe towers

`UniverseTower` is the hypothesis of `not_weakN_iff_of_tower`: a set-theoretic universe with
function abstraction and application, dependent products, separation, pairing, an embedding
of every small Lean type, and a tower of universes `U 0 ∈ U 1 ∈ …`, each closed under these
operations.

Any model of ZFC with countably many inaccessible cardinals `κ₀ < κ₁ < …` above the size of
Lean's `Type` gives one: `S` is the class of sets, `U n = V_κₙ`, `lam A f` is the graph of `f`
on `A`, `app` is application of a graph (anything outside the domain), `pi A B` is the set of
dependent functions, `enc` is any injection of the elements of a small type into sets. Lean
cannot construct such a structure for all `n` at once, which is why it is a hypothesis.

The interface is stated at the level the model uses (applicative set theory) and not as raw
membership axioms; deriving it from the membership axioms is routine and not done here.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

structure UniverseTower where
  /-- The sets. -/
  S : Type 1
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
  /-- Every small Lean type is a set. -/
  enc : {α : Type} → α → S
  enc_inj : ∀ {α : Type} {a b : α}, enc a = enc b → a = b
  set : Type → S
  mem_set : ∀ {α : Type} {x}, mem x (set α) ↔ ∃ a : α, x = enc a
  /-- The universes. -/
  U : Nat → S
  U_mem_U : ∀ n, mem (U n) (U (n + 1))
  U_mono : ∀ {n x}, mem x (U n) → mem x (U (n + 1))
  U_trans : ∀ {n x y}, mem x (U n) → mem y x → mem y (U n)
  set_mem_U : ∀ (α : Type), mem (set α) (U 0)
  sep_mem_U : ∀ {n A p}, mem A (U n) → mem (sep A p) (U n)
  image_mem_U : ∀ {n A f}, mem A (U n) → (∀ x, mem x A → mem (f x) (U n)) →
    mem (image A f) (U n)
  pair_mem_U : ∀ {n a b}, mem a (U n) → mem b (U n) → mem (pair a b) (U n)
  lam_mem_U : ∀ {n A f}, mem A (U n) → (∀ x, mem x A → mem (f x) (U n)) → mem (lam A f) (U n)
  pi_mem_U : ∀ {n A B}, mem A (U n) → (∀ x, mem x A → mem (B x) (U n)) → mem (pi A B) (U n)

end VEnv.Strengthening
end Lean4Lean
