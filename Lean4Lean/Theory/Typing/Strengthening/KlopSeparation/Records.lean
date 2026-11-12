import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SetModel
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Values

/-! # Semantic types of the Klop model

Second layer of the model for `KlopInventory.separated` (`FIRST_PRINCIPLES.md` §28, §29),
inside a `SetModel`.

Every object of the model is a pair whose first component is the encoding of a natural
number tag, so objects of different kinds are distinct: `•` (tag 100), the elements of `T`
(101), functions (104), and semantic types (tags 0 to 5). A semantic type is a record that
carries its own data: the constructor's arguments, its set of elements, its coarse relation
(as the function sending an element to its class) and its *skeleton*, the type with every
candidate replaced by its emptiness bit. Two types are coarsely related (`~`, `TyRel`) when
their skeletons are equal. Storing these components avoids recursion on sets.

This file gives the encodings, the constructors (`cand`, `tT`, `tProp`, `tU`, `tPi`, `tPiP`)
and the uniform Π formation `mkPi` with its collapse rule. Validity by level, the lemmas
about these types and the interpretation of terms are still to be written.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕋 : SetModel)

local infix:50 " ∈ₛ " => 𝕋.mem

/-- First projection of a pair (junk on non-pairs). -/
noncomputable def fst (p : 𝕋.S) : 𝕋.S :=
  if h : ∃ a b, p = 𝕋.pair a b then h.choose else p

/-- Second projection of a pair (junk on non-pairs). -/
noncomputable def snd (p : 𝕋.S) : 𝕋.S :=
  if h : ∃ a b, p = 𝕋.pair a b then h.choose_spec.choose else p

@[simp] theorem fst_pair (a b : 𝕋.S) : 𝕋.fst (𝕋.pair a b) = a := by
  have h : ∃ a' b', 𝕋.pair a b = 𝕋.pair a' b' := ⟨a, b, rfl⟩
  rw [fst, dif_pos h]
  exact (𝕋.pair_inj h.choose_spec.choose_spec).1.symm

@[simp] theorem snd_pair (a b : 𝕋.S) : 𝕋.snd (𝕋.pair a b) = b := by
  have h : ∃ a' b', 𝕋.pair a b = 𝕋.pair a' b' := ⟨a, b, rfl⟩
  rw [snd, dif_pos h]
  exact (𝕋.pair_inj h.choose_spec.choose_spec).2.symm

/-- Tags. -/
def tagN (n : Nat) : 𝕋.S := 𝕋.enc n

theorem tagN_inj {m n : Nat} (h : 𝕋.tagN m = 𝕋.tagN n) : m = n := 𝕋.enc_inj h

/-- The kind (tag) of an object. -/
noncomputable def kind (x : 𝕋.S) : 𝕋.S := 𝕋.fst x

/-- The element of every inhabited proposition. -/
def star : 𝕋.S := 𝕋.pair (𝕋.tagN 100) (𝕋.tagN 100)

/-- The elements of `T`: the three values `0`, `1`, `2`. -/
def tval (i : Fin 3) : 𝕋.S := 𝕋.pair (𝕋.tagN 101) (𝕋.enc i)

theorem tval_inj {i j : Fin 3} (h : 𝕋.tval i = 𝕋.tval j) : i = j :=
  𝕋.enc_inj (𝕋.pair_inj h).2

/-- A function on the set `A`, as an object of the model. -/
def fn (A : 𝕋.S) (f : 𝕋.S → 𝕋.S) : 𝕋.S := 𝕋.pair (𝕋.tagN 104) (𝕋.lam A f)

/-- Application of a function object. -/
noncomputable def ap (g x : 𝕋.S) : 𝕋.S := 𝕋.app (𝕋.snd g) x

theorem ap_fn {A : 𝕋.S} {f : 𝕋.S → 𝕋.S} {x : 𝕋.S} (hx : x ∈ₛ A) : 𝕋.ap (𝕋.fn A f) x = f x := by
  simp [ap, fn, 𝕋.app_lam hx]

theorem fn_ext {A : 𝕋.S} {f g : 𝕋.S → 𝕋.S} (h : ∀ x, x ∈ₛ A → f x = g x) :
    𝕋.fn A f = 𝕋.fn A g := by
  simp [fn, 𝕋.lam_ext h]

/-- The one-point set `{•}`. -/
def one : 𝕋.S := 𝕋.image (𝕋.set Unit) fun _ => 𝕋.star

/-- The empty set. -/
def emptySet : 𝕋.S := 𝕋.set Empty

theorem mem_one {x : 𝕋.S} : x ∈ₛ 𝕋.one ↔ x = 𝕋.star := by
  rw [one, 𝕋.mem_image]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨𝕋.enc (), 𝕋.mem_set.2 ⟨(), rfl⟩, h⟩⟩

theorem not_mem_emptySet {x : 𝕋.S} : ¬ x ∈ₛ 𝕋.emptySet := by
  rw [emptySet, 𝕋.mem_set]; exact fun ⟨a, _⟩ => a.elim

/-- The set of the three elements of `T`. -/
noncomputable def tSet : 𝕋.S :=
  𝕋.image (𝕋.set (Fin 3)) fun x => 𝕋.pair (𝕋.tagN 101) x

theorem mem_tSet {x : 𝕋.S} : x ∈ₛ 𝕋.tSet ↔ ∃ i, x = 𝕋.tval i := by
  rw [tSet, 𝕋.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := 𝕋.mem_set.1 hy
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, 𝕋.mem_set.2 ⟨i, rfl⟩, rfl⟩

/-! ### Records -/

/-- A semantic type record: kind, constructor arguments, elements, relation, skeleton. -/
def rec5 (k : Nat) (args elts rel skel : 𝕋.S) : 𝕋.S :=
  𝕋.pair (𝕋.tagN k) (𝕋.pair args (𝕋.pair elts (𝕋.pair rel skel)))

/-- The constructor arguments. -/
noncomputable def argsOf (A : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.snd A)
/-- The set of elements. -/
noncomputable def El (A : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.snd (𝕋.snd A))
/-- The coarse relation, as the function sending an element to its class. -/
noncomputable def relOf (A : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.snd (𝕋.snd (𝕋.snd A)))
/-- The skeleton. -/
noncomputable def skel (A : 𝕋.S) : 𝕋.S := 𝕋.snd (𝕋.snd (𝕋.snd (𝕋.snd A)))

@[simp] theorem kind_rec5 (k : Nat) (a e r s : 𝕋.S) : 𝕋.kind (𝕋.rec5 k a e r s) = 𝕋.tagN k := by
  simp [kind, rec5]
@[simp] theorem argsOf_rec5 (k : Nat) (a e r s : 𝕋.S) : 𝕋.argsOf (𝕋.rec5 k a e r s) = a := by
  simp [argsOf, rec5]
@[simp] theorem El_rec5 (k : Nat) (a e r s : 𝕋.S) : 𝕋.El (𝕋.rec5 k a e r s) = e := by
  simp [El, rec5]
@[simp] theorem relOf_rec5 (k : Nat) (a e r s : 𝕋.S) : 𝕋.relOf (𝕋.rec5 k a e r s) = r := by
  simp [relOf, rec5]
@[simp] theorem skel_rec5 (k : Nat) (a e r s : 𝕋.S) : 𝕋.skel (𝕋.rec5 k a e r s) = s := by
  simp [skel, rec5]

/-- Coarse relatedness of two elements of a semantic type. -/
def Rel (A x y : 𝕋.S) : Prop := y ∈ₛ 𝕋.app (𝕋.relOf A) x

/-- Coarse relatedness of two semantic types. -/
def TyRel (A B : 𝕋.S) : Prop := 𝕋.skel A = 𝕋.skel B

/-- The relation function of a set with a given relation. -/
def relFn (elts : 𝕋.S) (R : 𝕋.S → 𝕋.S → Prop) : 𝕋.S :=
  𝕋.lam elts fun x => 𝕋.sep elts (R x)

theorem mem_relFn {elts : 𝕋.S} {R : 𝕋.S → 𝕋.S → Prop} {x y : 𝕋.S} (hx : x ∈ₛ elts) :
    y ∈ₛ 𝕋.app (𝕋.relFn elts R) x ↔ y ∈ₛ elts ∧ R x y := by
  rw [relFn, 𝕋.app_lam hx, 𝕋.mem_sep]

end SetModel

end VEnv.Strengthening
end Lean4Lean
