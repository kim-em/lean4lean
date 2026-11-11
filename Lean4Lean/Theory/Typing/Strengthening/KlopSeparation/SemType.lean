import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Small

/-! # Semantic types of the Klop model

Second layer of the model for `KlopInventory.separated` (`FIRST_PRINCIPLES.md` §28, §29),
inside a `UniverseTower`.

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

namespace UniverseTower
variable (𝕋 : UniverseTower)

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

/-! ### Constructors -/

/-- A proposition: its candidate. Its only element is `•`, present when the candidate is
non-empty; its skeleton records only whether it is empty. -/
noncomputable def cand (c : Candidate) : 𝕋.S :=
  let elts := if ∃ v, c.mem v then 𝕋.one else 𝕋.emptySet
  𝕋.rec5 0 (𝕋.enc c) elts (𝕋.relFn elts fun _ _ => True)
    (𝕋.pair (𝕋.tagN 0) (𝕋.enc (decide (∃ v, c.mem v))))

/-- The data type `T = ℤ/3`, with the total coarse relation. -/
noncomputable def tT : 𝕋.S :=
  𝕋.rec5 1 𝕋.star 𝕋.tSet (𝕋.relFn 𝕋.tSet fun _ _ => True) (𝕋.pair (𝕋.tagN 1) 𝕋.star)

/-- The set of the propositions `cand c` for good candidates `c`. -/
noncomputable def candSet : 𝕋.S :=
  𝕋.image (𝕋.sep (𝕋.set Candidate) fun x => ∃ c : Candidate, c.Good ∧ x = 𝕋.enc c) fun x =>
    if h : ∃ c : Candidate, x = 𝕋.enc c then 𝕋.cand h.choose else x

/-- `Prop`: the type of the propositions of good candidates, coarsely related when both are
empty or both non-empty. -/
noncomputable def tProp : 𝕋.S :=
  𝕋.rec5 2 𝕋.star 𝕋.candSet (𝕋.relFn 𝕋.candSet fun A B => 𝕋.TyRel A B)
    (𝕋.pair (𝕋.tagN 2) 𝕋.star)

/-- The universe of level `n`, given the set `tys` of its semantic types, with coarse
relation `~`. -/
noncomputable def tU (n : Nat) (tys : 𝕋.S) : 𝕋.S :=
  𝕋.rec5 3 (𝕋.enc n) tys (𝕋.relFn tys fun A B => 𝕋.TyRel A B) (𝕋.pair (𝕋.tagN 3) (𝕋.enc n))

/-- A dependent product over a data domain with at least one data fibre: the functions that
respect the coarse relations, related pointwise. `F d` is the fibre over `d`. -/
noncomputable def tPi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.S :=
  let elts := 𝕋.image
    (𝕋.sep (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) fun f =>
      ∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.Rel (F d) (𝕋.app f d) (𝕋.app f d'))
    fun f => 𝕋.pair (𝕋.tagN 104) f
  𝕋.rec5 4 (𝕋.pair D (𝕋.lam (𝕋.El D) F)) elts
    (𝕋.relFn elts fun f g => ∀ d, d ∈ₛ 𝕋.El D → 𝕋.Rel (F d) (𝕋.ap f d) (𝕋.ap g d))
    (𝕋.pair (𝕋.tagN 4) (𝕋.pair (𝕋.skel D) (𝕋.lam (𝕋.El D) fun d => 𝕋.skel (F d))))

/-- A function type from a non-empty proposition `c` to a data type `B`: functions on `{•}`. -/
noncomputable def tPiP (c : Candidate) (B : 𝕋.S) : 𝕋.S :=
  let elts := 𝕋.image (𝕋.pi 𝕋.one fun _ => 𝕋.El B) fun f => 𝕋.pair (𝕋.tagN 104) f
  𝕋.rec5 5 (𝕋.pair (𝕋.enc c) B) elts
    (𝕋.relFn elts fun f g => 𝕋.Rel B (𝕋.ap f 𝕋.star) (𝕋.ap g 𝕋.star))
    (𝕋.pair (𝕋.tagN 5) (𝕋.skel B))

theorem cand_inj {c d : Candidate} (h : 𝕋.cand c = 𝕋.cand d) : c = d := by
  have := congrArg 𝕋.argsOf h
  simp only [cand, argsOf_rec5] at this
  exact 𝕋.enc_inj this

/-- The candidate of a semantic type that is a proposition (the empty one otherwise). -/
noncomputable def candOf (A : 𝕋.S) : Candidate :=
  if h : ∃ c, A = 𝕋.cand c then h.choose else Candidate.empty

@[simp] theorem candOf_cand (c : Candidate) : 𝕋.candOf (𝕋.cand c) = c := by
  have h : ∃ c', 𝕋.cand c = 𝕋.cand c' := ⟨c, rfl⟩
  rw [candOf, dif_pos h]
  exact (𝕋.cand_inj h.choose_spec).symm

/-- A semantic type is a proposition. -/
def IsCand (A : 𝕋.S) : Prop := ∃ c, A = 𝕋.cand c

theorem mem_El_cand {c : Candidate} {x : 𝕋.S} :
    x ∈ₛ 𝕋.El (𝕋.cand c) ↔ x = 𝕋.star ∧ ∃ v, c.mem v := by
  simp only [cand, El_rec5]
  split
  · rw [mem_one]; exact ⟨fun h => ⟨h, ‹_›⟩, fun h => h.1⟩
  · exact ⟨fun h => (𝕋.not_mem_emptySet h).elim, fun h => (‹¬ _› h.2).elim⟩

theorem mem_El_tT {x : 𝕋.S} : x ∈ₛ 𝕋.El 𝕋.tT ↔ ∃ i, x = 𝕋.tval i := by
  simp [tT, mem_tSet]

theorem rel_tT {x y : 𝕋.S} (hx : x ∈ₛ 𝕋.El 𝕋.tT) (hy : y ∈ₛ 𝕋.El 𝕋.tT) : 𝕋.Rel 𝕋.tT x y := by
  have hx' : x ∈ₛ 𝕋.tSet := by simpa [tT] using hx
  have hy' : y ∈ₛ 𝕋.tSet := by simpa [tT] using hy
  rw [Rel]
  simp only [tT, relOf_rec5]
  exact (𝕋.mem_relFn hx').2 ⟨hy', trivial⟩

/-! ### Uniform Π formation -/

/-- The candidate of a Π-proposition over a data domain: the values sending every argument
value to a realizer of every fibre. -/
noncomputable def piCand (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : Candidate where
  mem v := ∀ d, d ∈ₛ 𝕋.El D → ∀ u, (𝕋.candOf (F d)).mem (.app v u)
  step h := ⟨fun H d hd u => ((𝕋.candOf (F d)).step (.appL h)).1 (H d hd u),
    fun H d hd u => ((𝕋.candOf (F d)).step (.appL h)).2 (H d hd u)⟩

/-- **Π formation.** Over an empty proposition: the full candidate. Over a non-empty
proposition: a function proposition if the fibre is one, a `tPiP` otherwise. Over a data
domain: a Π-proposition if every fibre is a proposition, a `tPi` otherwise. -/
noncomputable def mkPi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.S :=
  if 𝕋.IsCand D then
    if ∃ v, (𝕋.candOf D).mem v then
      if 𝕋.IsCand (F 𝕋.star) then 𝕋.cand (Candidate.arrow (𝕋.candOf D) (𝕋.candOf (F 𝕋.star)))
      else 𝕋.tPiP (𝕋.candOf D) (F 𝕋.star)
    else 𝕋.cand Candidate.full
  else if ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d) then 𝕋.cand (𝕋.piCand D F)
  else 𝕋.tPi D F

/-- **λ formation.** A function all of whose values are `•` is `•`; otherwise the function
object on the elements of the domain. -/
noncomputable def mkLam (D : 𝕋.S) (f : 𝕋.S → 𝕋.S) : 𝕋.S :=
  if ∀ d, d ∈ₛ 𝕋.El D → f d = 𝕋.star then 𝕋.star else 𝕋.fn (𝕋.El D) f

/-- **Application.** `•` applied to anything is `•`. -/
noncomputable def mkApp (g x : 𝕋.S) : 𝕋.S :=
  if g = 𝕋.star then 𝕋.star else 𝕋.ap g x

theorem star_ne_fn (A : 𝕋.S) (f : 𝕋.S → 𝕋.S) : 𝕋.star ≠ 𝕋.fn A f := fun h => by
  have := 𝕋.tagN_inj (𝕋.pair_inj h).1
  omega

theorem mkApp_mkLam {D : 𝕋.S} {f : 𝕋.S → 𝕋.S} {x : 𝕋.S} (hx : x ∈ₛ 𝕋.El D) :
    𝕋.mkApp (𝕋.mkLam D f) x = f x := by
  unfold mkLam
  split
  · rename_i h; simp [mkApp, h x hx]
  · rw [mkApp, if_neg (fun h => 𝕋.star_ne_fn _ _ h.symm), 𝕋.ap_fn hx]

end UniverseTower

end VEnv.Strengthening
end Lean4Lean
