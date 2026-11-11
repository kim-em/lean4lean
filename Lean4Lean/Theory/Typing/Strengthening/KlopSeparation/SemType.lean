import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Tower
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Values

/-! # Semantic types of the Klop model

Second layer of the model for `KlopInventory.separated` (`FIRST_PRINCIPLES.md` §28, §29),
inside a `UniverseTower`.

A semantic type is a record, encoded as nested pairs, that carries its own data: a tag with
the constructor's arguments, its set of elements, its coarse relation (as the function
sending an element to its class) and its *skeleton*, the type with every candidate replaced
by its emptiness bit. Two types are coarsely related (`~`) when their skeletons are equal.
Storing these components avoids defining them by recursion on sets.

This file gives the encodings and the constructors: candidates, `T`, the type of candidates
(`Prop`), universes, and dependent products over a data domain and over a proposition domain.
The validity predicate, the lemmas about them and the interpretation are still to be written.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable (𝕋 : UniverseTower)

local infix:50 " ∈ₛ " => 𝕋.mem

/-- First projection of a pair (junk on non-pairs). -/
noncomputable def fst (p : 𝕋.S) : 𝕋.S :=
  if h : ∃ a b, p = 𝕋.pair a b then h.choose else p

/-- Second projection of a pair (junk on non-pairs). -/
noncomputable def snd (p : 𝕋.S) : 𝕋.S :=
  if h : ∃ a b, p = 𝕋.pair a b then h.choose_spec.choose else p

theorem fst_pair (a b : 𝕋.S) : 𝕋.fst (𝕋.pair a b) = a := by
  have h : ∃ a' b', 𝕋.pair a b = 𝕋.pair a' b' := ⟨a, b, rfl⟩
  rw [fst, dif_pos h]
  exact (𝕋.pair_inj h.choose_spec.choose_spec).1.symm

theorem snd_pair (a b : 𝕋.S) : 𝕋.snd (𝕋.pair a b) = b := by
  have h : ∃ a' b', 𝕋.pair a b = 𝕋.pair a' b' := ⟨a, b, rfl⟩
  rw [snd, dif_pos h]
  exact (𝕋.pair_inj h.choose_spec.choose_spec).2.symm

/-- The element of every inhabited proposition, and of the one-point type. -/
def star : 𝕋.S := 𝕋.enc ()

/-- The one-point set `{•}`. -/
def one : 𝕋.S := 𝕋.set Unit

/-- The empty set. -/
def emptySet : 𝕋.S := 𝕋.set Empty

theorem mem_one {x : 𝕋.S} : x ∈ₛ 𝕋.one ↔ x = 𝕋.star := by
  rw [one, 𝕋.mem_set]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem not_mem_emptySet {x : 𝕋.S} : ¬ x ∈ₛ 𝕋.emptySet := by
  rw [emptySet, 𝕋.mem_set]; exact fun ⟨a, _⟩ => a.elim

/-- The elements of `T`: the three values `0`, `1`, `2`. -/
def tval (i : Fin 3) : 𝕋.S := 𝕋.enc i

theorem tval_inj {i j : Fin 3} (h : 𝕋.tval i = 𝕋.tval j) : i = j := 𝕋.enc_inj h

/-! ### Records -/

/-- A semantic type record. -/
def rec4 (tag elts rel skel : 𝕋.S) : 𝕋.S := 𝕋.pair tag (𝕋.pair elts (𝕋.pair rel skel))

/-- The tag and constructor arguments. -/
noncomputable def tagOf (A : 𝕋.S) : 𝕋.S := 𝕋.fst A
/-- The set of elements. -/
noncomputable def El (A : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.snd A)
/-- The coarse relation, as the function sending an element to its class. -/
noncomputable def relOf (A : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.snd (𝕋.snd A))
/-- The skeleton. -/
noncomputable def skel (A : 𝕋.S) : 𝕋.S := 𝕋.snd (𝕋.snd (𝕋.snd A))

@[simp] theorem tagOf_rec4 (t e r s : 𝕋.S) : 𝕋.tagOf (𝕋.rec4 t e r s) = t := 𝕋.fst_pair ..
@[simp] theorem El_rec4 (t e r s : 𝕋.S) : 𝕋.El (𝕋.rec4 t e r s) = e := by
  simp [El, rec4, snd_pair, fst_pair]
@[simp] theorem relOf_rec4 (t e r s : 𝕋.S) : 𝕋.relOf (𝕋.rec4 t e r s) = r := by
  simp [relOf, rec4, snd_pair, fst_pair]
@[simp] theorem skel_rec4 (t e r s : 𝕋.S) : 𝕋.skel (𝕋.rec4 t e r s) = s := by
  simp [skel, rec4, snd_pair]

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

/-! ### Constructors -/

/-- Tags of the constructors. -/
def tag (n : Nat) : 𝕋.S := 𝕋.enc n

/-- A proposition: its candidate. Its only element is `•`, present when the candidate is
non-empty; its skeleton records only whether it is empty. -/
noncomputable def cand (c : Candidate) : 𝕋.S :=
  let elts := if ∃ v, c.mem v then 𝕋.one else 𝕋.emptySet
  𝕋.rec4 (𝕋.pair (𝕋.tag 0) (𝕋.enc c)) elts (𝕋.relFn elts fun _ _ => True)
    (𝕋.pair (𝕋.tag 0) (𝕋.enc (decide (∃ v, c.mem v))))

/-- The data type `T = ℤ/3`, with the total coarse relation. -/
noncomputable def tT : 𝕋.S :=
  𝕋.rec4 (𝕋.tag 1) (𝕋.set (Fin 3)) (𝕋.relFn (𝕋.set (Fin 3)) fun _ _ => True) (𝕋.tag 1)

/-- The good candidates, as a set of semantic types. -/
noncomputable def candSet : 𝕋.S :=
  𝕋.sep (𝕋.set Candidate) fun x => ∃ c : Candidate, c.Good ∧ x = 𝕋.enc c

/-- `Prop`: the type of good candidates, coarsely related when both are empty or both
non-empty. Its elements are the encodings `enc c`; `cand c` is the type they denote. -/
noncomputable def tProp : 𝕋.S :=
  𝕋.rec4 (𝕋.tag 2) 𝕋.candSet
    (𝕋.relFn 𝕋.candSet fun x y => ∃ c d : Candidate, x = 𝕋.enc c ∧ y = 𝕋.enc d ∧
      ((∃ v, c.mem v) ↔ ∃ v, d.mem v))
    (𝕋.tag 2)

/-- A dependent product over a data domain with at least one data fibre: the functions that
respect the coarse relations, related pointwise. `F d` is the fibre over `d`. -/
noncomputable def tPi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.S :=
  let elts := 𝕋.sep (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) fun f =>
    ∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.Rel (F d) (𝕋.app f d) (𝕋.app f d')
  𝕋.rec4 (𝕋.pair (𝕋.tag 4) (𝕋.pair D (𝕋.lam (𝕋.El D) F))) elts
    (𝕋.relFn elts fun f g => ∀ d, d ∈ₛ 𝕋.El D → 𝕋.Rel (F d) (𝕋.app f d) (𝕋.app g d))
    (𝕋.pair (𝕋.tag 4) (𝕋.pair (𝕋.skel D) (𝕋.lam (𝕋.El D) fun d => 𝕋.skel (F d))))

/-- A function type from a non-empty proposition `c` to a data type `B`: functions on `{•}`. -/
noncomputable def tPiP (c : Candidate) (B : 𝕋.S) : 𝕋.S :=
  let elts := 𝕋.pi 𝕋.one fun _ => 𝕋.El B
  𝕋.rec4 (𝕋.pair (𝕋.tag 5) (𝕋.pair (𝕋.enc c) B)) elts
    (𝕋.relFn elts fun f g => 𝕋.Rel B (𝕋.app f 𝕋.star) (𝕋.app g 𝕋.star))
    (𝕋.pair (𝕋.tag 5) (𝕋.skel B))

/-- The universe of level `n`, given the set `tys` of its semantic types: coarse relation
`~`. -/
noncomputable def tU (n : Nat) (tys : 𝕋.S) : 𝕋.S :=
  𝕋.rec4 (𝕋.pair (𝕋.tag 3) (𝕋.enc n)) tys (𝕋.relFn tys fun A B => 𝕋.TyRel A B)
    (𝕋.pair (𝕋.tag 3) (𝕋.enc n))

/-- Whether a semantic type is a proposition, and which. -/
def IsCand (A : 𝕋.S) (c : Candidate) : Prop := A = 𝕋.cand c

theorem cand_inj {c d : Candidate} (h : 𝕋.cand c = 𝕋.cand d) : c = d := by
  have := congrArg 𝕋.tagOf h
  simp only [cand, tagOf_rec4] at this
  exact 𝕋.enc_inj (𝕋.pair_inj this).2

theorem El_cand (c : Candidate) :
    𝕋.El (𝕋.cand c) = if ∃ v, c.mem v then 𝕋.one else 𝕋.emptySet := by
  simp [cand]

theorem mem_El_cand {c : Candidate} {x : 𝕋.S} :
    x ∈ₛ 𝕋.El (𝕋.cand c) ↔ x = 𝕋.star ∧ ∃ v, c.mem v := by
  rw [El_cand]
  split
  · rw [mem_one]; exact ⟨fun h => ⟨h, ‹_›⟩, fun h => h.1⟩
  · exact ⟨fun h => (𝕋.not_mem_emptySet h).elim, fun h => (‹¬ _› h.2).elim⟩

theorem mem_El_tT {x : 𝕋.S} : x ∈ₛ 𝕋.El 𝕋.tT ↔ ∃ i, x = 𝕋.tval i := by
  simp [tT, 𝕋.mem_set, tval]

theorem rel_tT {x y : 𝕋.S} (hx : x ∈ₛ 𝕋.El 𝕋.tT) (hy : y ∈ₛ 𝕋.El 𝕋.tT) : 𝕋.Rel 𝕋.tT x y := by
  have hx' : x ∈ₛ 𝕋.set (Fin 3) := by simpa [tT] using hx
  have hy' : y ∈ₛ 𝕋.set (Fin 3) := by simpa [tT] using hy
  rw [Rel]
  simp only [tT, relOf_rec4]
  exact (𝕋.mem_relFn hx').2 ⟨hy', trivial⟩

end UniverseTower

end VEnv.Strengthening
end Lean4Lean
