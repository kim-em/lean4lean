import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.UniformLemmas

/-! # Constructors of the semantic types of the Klop model

The constructors (`cand`, `tT`, `tProp`, `tU`, `tPi`, `tPiP`) and the uniform Π formation
`mkPi` with its collapse rule. The encodings and record accessors are in `Records.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕋 : SetModel)

local infix:50 " ∈ₛ " => 𝕋.mem

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

/-- The record of a Π-type before its elements are known: kind and constructor arguments
only. Uniformity of a function is stated against it. -/
noncomputable def prePi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.S :=
  𝕋.rec5 4 (𝕋.pair D (𝕋.lam (𝕋.El D) F)) 𝕋.emptySet 𝕋.emptySet 𝕋.emptySet

/-- The function object `g` is uniform at every level, as an element of the Π-type of `D` and
`F` (`FIRST_PRINCIPLES.md` §30.6). -/
def PiUnif (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) (g : 𝕋.S) : Prop :=
  𝕋.Unif 0 PUnit (fun _ => 𝕋.prePi D F) (fun _ => g)

/-- A dependent product over a data domain with at least one data fibre: the uniform functions
that respect the coarse relations, related pointwise. `F d` is the fibre over `d`. -/
noncomputable def tPi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.S :=
  let elts := 𝕋.image
    (𝕋.sep (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) fun f =>
      (∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.Rel (F d) (𝕋.app f d) (𝕋.app f d')) ∧
      𝕋.PiUnif D F (𝕋.pair (𝕋.tagN 104) f))
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

end SetModel

end VEnv.Strengthening
end Lean4Lean
