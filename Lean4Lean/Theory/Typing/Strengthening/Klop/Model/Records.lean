import Lean4Lean.Theory.Typing.Strengthening.Klop.SetModel
import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Values

/-! # Records for semantic types

Every object of the model is a pair whose first component is the encoding of a natural
number tag, so objects of different kinds are distinct: `•` (tag 100), the elements of `T`
(101), functions (104), and semantic types (tags 0 to 5). A semantic type is a record that
carries its own data: the constructor's arguments, its set of elements, its coarse relation
(as the function sending an element to its class) and its *skeleton*, the type with every
candidate replaced by its emptiness bit. Two types are coarsely related (`TyRel`) when their
skeletons are equal. Storing these components avoids recursion on sets.

This file gives the encodings and the accessors of a record (`kind`, `argsOf`, `El`, `Rel`,
`skel`). The constructors are in `SemType.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕊 : SetModel)

local infix:50 " ∈ₛ " => 𝕊.mem

/-- First projection of a pair (junk on non-pairs). -/
noncomputable def fst (p : 𝕊.S) : 𝕊.S :=
  if h : ∃ a b, p = 𝕊.pair a b then h.choose else p

/-- Second projection of a pair (junk on non-pairs). -/
noncomputable def snd (p : 𝕊.S) : 𝕊.S :=
  if h : ∃ a b, p = 𝕊.pair a b then h.choose_spec.choose else p

@[simp] theorem fst_pair (a b : 𝕊.S) : 𝕊.fst (𝕊.pair a b) = a := by
  have h : ∃ a' b', 𝕊.pair a b = 𝕊.pair a' b' := ⟨a, b, rfl⟩
  rw [fst, dif_pos h]
  exact (𝕊.pair_inj h.choose_spec.choose_spec).1.symm

@[simp] theorem snd_pair (a b : 𝕊.S) : 𝕊.snd (𝕊.pair a b) = b := by
  have h : ∃ a' b', 𝕊.pair a b = 𝕊.pair a' b' := ⟨a, b, rfl⟩
  rw [snd, dif_pos h]
  exact (𝕊.pair_inj h.choose_spec.choose_spec).2.symm

/-- Tags. -/
def tagN (n : Nat) : 𝕊.S := 𝕊.enc n

theorem tagN_inj {m n : Nat} (h : 𝕊.tagN m = 𝕊.tagN n) : m = n := 𝕊.enc_inj h

/-- The kind (tag) of an object. -/
noncomputable def kind (x : 𝕊.S) : 𝕊.S := 𝕊.fst x

/-- The element of every inhabited proposition. -/
def star : 𝕊.S := 𝕊.pair (𝕊.tagN 100) (𝕊.tagN 100)

/-- The elements of `T`: the three values `0`, `1`, `2`. -/
def tval (i : Fin 3) : 𝕊.S := 𝕊.pair (𝕊.tagN 101) (𝕊.enc i)

theorem tval_inj {i j : Fin 3} (h : 𝕊.tval i = 𝕊.tval j) : i = j :=
  𝕊.enc_inj (𝕊.pair_inj h).2

/-- A function on the set `A`, as an object of the model. -/
def fn (A : 𝕊.S) (f : 𝕊.S → 𝕊.S) : 𝕊.S := 𝕊.pair (𝕊.tagN 104) (𝕊.lam A f)

/-- Application of a function object. -/
noncomputable def ap (g x : 𝕊.S) : 𝕊.S := 𝕊.app (𝕊.snd g) x

theorem ap_fn {A : 𝕊.S} {f : 𝕊.S → 𝕊.S} {x : 𝕊.S} (hx : x ∈ₛ A) : 𝕊.ap (𝕊.fn A f) x = f x := by
  simp [ap, fn, 𝕊.app_lam hx]

theorem fn_ext {A : 𝕊.S} {f g : 𝕊.S → 𝕊.S} (h : ∀ x, x ∈ₛ A → f x = g x) :
    𝕊.fn A f = 𝕊.fn A g := by
  simp [fn, 𝕊.lam_ext h]

/-- The one-point set `{•}`. -/
def one : 𝕊.S := 𝕊.image (𝕊.set Unit) fun _ => 𝕊.star

/-- The empty set. -/
def emptySet : 𝕊.S := 𝕊.set Empty

theorem mem_one {x : 𝕊.S} : x ∈ₛ 𝕊.one ↔ x = 𝕊.star := by
  rw [one, 𝕊.mem_image]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨𝕊.enc (), 𝕊.mem_set.2 ⟨(), rfl⟩, h⟩⟩

theorem not_mem_emptySet {x : 𝕊.S} : ¬ x ∈ₛ 𝕊.emptySet := by
  rw [emptySet, 𝕊.mem_set]; exact fun ⟨a, _⟩ => a.elim

/-- The set of the three elements of `T`. -/
noncomputable def tSet : 𝕊.S :=
  𝕊.image (𝕊.set (Fin 3)) fun x => 𝕊.pair (𝕊.tagN 101) x

theorem mem_tSet {x : 𝕊.S} : x ∈ₛ 𝕊.tSet ↔ ∃ i, x = 𝕊.tval i := by
  rw [tSet, 𝕊.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := 𝕊.mem_set.1 hy
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, 𝕊.mem_set.2 ⟨i, rfl⟩, rfl⟩

/-! ### Records -/

/-- A semantic type record: kind, constructor arguments, elements, relation, skeleton. -/
def rec5 (k : Nat) (args elts rel skel : 𝕊.S) : 𝕊.S :=
  𝕊.pair (𝕊.tagN k) (𝕊.pair args (𝕊.pair elts (𝕊.pair rel skel)))

/-- The constructor arguments. -/
noncomputable def argsOf (A : 𝕊.S) : 𝕊.S := 𝕊.fst (𝕊.snd A)
/-- The set of elements. -/
noncomputable def El (A : 𝕊.S) : 𝕊.S := 𝕊.fst (𝕊.snd (𝕊.snd A))
/-- The coarse relation, as the function sending an element to its class. -/
noncomputable def relOf (A : 𝕊.S) : 𝕊.S := 𝕊.fst (𝕊.snd (𝕊.snd (𝕊.snd A)))
/-- The skeleton. -/
noncomputable def skel (A : 𝕊.S) : 𝕊.S := 𝕊.snd (𝕊.snd (𝕊.snd (𝕊.snd A)))

@[simp] theorem kind_rec5 (k : Nat) (a e r s : 𝕊.S) : 𝕊.kind (𝕊.rec5 k a e r s) = 𝕊.tagN k := by
  simp [kind, rec5]
@[simp] theorem argsOf_rec5 (k : Nat) (a e r s : 𝕊.S) : 𝕊.argsOf (𝕊.rec5 k a e r s) = a := by
  simp [argsOf, rec5]
@[simp] theorem El_rec5 (k : Nat) (a e r s : 𝕊.S) : 𝕊.El (𝕊.rec5 k a e r s) = e := by
  simp [El, rec5]
@[simp] theorem relOf_rec5 (k : Nat) (a e r s : 𝕊.S) : 𝕊.relOf (𝕊.rec5 k a e r s) = r := by
  simp [relOf, rec5]
@[simp] theorem skel_rec5 (k : Nat) (a e r s : 𝕊.S) : 𝕊.skel (𝕊.rec5 k a e r s) = s := by
  simp [skel, rec5]

/-- Coarse relatedness of two elements of a semantic type. -/
def Rel (A x y : 𝕊.S) : Prop := y ∈ₛ 𝕊.app (𝕊.relOf A) x

/-- Coarse relatedness of two semantic types. -/
def TyRel (A B : 𝕊.S) : Prop := 𝕊.skel A = 𝕊.skel B

/-- The relation function of a set with a given relation. -/
def relFn (elts : 𝕊.S) (R : 𝕊.S → 𝕊.S → Prop) : 𝕊.S :=
  𝕊.lam elts fun x => 𝕊.sep elts (R x)

theorem mem_relFn {elts : 𝕊.S} {R : 𝕊.S → 𝕊.S → Prop} {x y : 𝕊.S} (hx : x ∈ₛ elts) :
    y ∈ₛ 𝕊.app (𝕊.relFn elts R) x ↔ y ∈ₛ elts ∧ R x y := by
  rw [relFn, 𝕊.app_lam hx, 𝕊.mem_sep]

end SetModel

end VEnv.Strengthening
end Lean4Lean
