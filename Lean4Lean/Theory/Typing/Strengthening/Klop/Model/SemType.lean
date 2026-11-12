import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.UniformLemmas

/-! # Constructors of the semantic types

The constructors `cand` (a proposition), `tT`, `tProp`, `tU` (a universe), `tPi` and `tPiP`
(a function type out of a proposition), and the operations `mkPi`, `mkLam`, `mkApp` that
interpret Π, λ and application. `mkPi` collapses a Π-type whose fibres are all propositions to
a proposition, and `mkLam`, `mkApp` collapse proofs to `•`.

The elements of `tPi D F` are the functions on `D` with values in the fibres that respect
the coarse relation and are uniform (`PiUnif`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕊 : SetModel)

local infix:50 " ∈ₛ " => 𝕊.mem

/-! ### Constructors -/

/-- A proposition: its candidate. Its only element is `•`, present when the candidate is
non-empty; its skeleton records only whether it is empty. -/
noncomputable def cand (c : Candidate) : 𝕊.S :=
  let elts := if ∃ v, c.mem v then 𝕊.one else 𝕊.emptySet
  𝕊.rec5 0 (𝕊.enc c) elts (𝕊.relFn elts fun _ _ => True)
    (𝕊.pair (𝕊.tagN 0) (𝕊.enc (decide (∃ v, c.mem v))))

/-- The data type `T = ℤ/3`, with the total coarse relation. -/
noncomputable def tT : 𝕊.S :=
  𝕊.rec5 1 𝕊.star 𝕊.tSet (𝕊.relFn 𝕊.tSet fun _ _ => True) (𝕊.pair (𝕊.tagN 1) 𝕊.star)

/-- The set of the propositions `cand c` for good candidates `c`. -/
noncomputable def candSet : 𝕊.S :=
  𝕊.image (𝕊.sep (𝕊.set Candidate) fun x => ∃ c : Candidate, c.Good ∧ x = 𝕊.enc c) fun x =>
    if h : ∃ c : Candidate, x = 𝕊.enc c then 𝕊.cand h.choose else x

/-- `Prop`: the type of the propositions of good candidates, coarsely related when both are
empty or both non-empty. -/
noncomputable def tProp : 𝕊.S :=
  𝕊.rec5 2 𝕊.star 𝕊.candSet (𝕊.relFn 𝕊.candSet fun A B => 𝕊.TyRel A B)
    (𝕊.pair (𝕊.tagN 2) 𝕊.star)

/-- The universe of level `n`, given the set `tys` of its semantic types, with coarse
relation `~`. -/
noncomputable def tU (n : Nat) (tys : 𝕊.S) : 𝕊.S :=
  𝕊.rec5 3 (𝕊.enc n) tys (𝕊.relFn tys fun A B => 𝕊.TyRel A B) (𝕊.pair (𝕊.tagN 3) (𝕊.enc n))

/-- The record of a Π-type before its elements are known: kind and constructor arguments
only. Uniformity of a function is stated against it. -/
noncomputable def prePi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.S :=
  𝕊.rec5 4 (𝕊.pair D (𝕊.lam (𝕊.El D) F)) 𝕊.emptySet 𝕊.emptySet 𝕊.emptySet

/-- The function object `g` is uniform at every level, as an element of the Π-type of `D` and
`F`. -/
def PiUnif (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) (g : 𝕊.S) : Prop :=
  𝕊.Unif 0 PUnit (fun _ => 𝕊.prePi D F) (fun _ => g)

/-- A dependent product over a data domain with at least one data fibre: the uniform functions
that respect the coarse relations, related pointwise. `F d` is the fibre over `d`. -/
noncomputable def tPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.S :=
  let elts := 𝕊.image
    (𝕊.sep (𝕊.pi (𝕊.El D) fun d => 𝕊.El (F d)) fun f =>
      (∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F d) (𝕊.app f d) (𝕊.app f d')) ∧
      𝕊.PiUnif D F (𝕊.pair (𝕊.tagN 104) f))
    fun f => 𝕊.pair (𝕊.tagN 104) f
  𝕊.rec5 4 (𝕊.pair D (𝕊.lam (𝕊.El D) F)) elts
    (𝕊.relFn elts fun f g => ∀ d, d ∈ₛ 𝕊.El D → 𝕊.Rel (F d) (𝕊.ap f d) (𝕊.ap g d))
    (𝕊.pair (𝕊.tagN 4) (𝕊.pair (𝕊.skel D) (𝕊.lam (𝕊.El D) fun d => 𝕊.skel (F d))))

/-- A function type from a non-empty proposition `c` to a data type `B`: functions on `{•}`. -/
noncomputable def tPiP (c : Candidate) (B : 𝕊.S) : 𝕊.S :=
  let elts := 𝕊.image (𝕊.pi 𝕊.one fun _ => 𝕊.El B) fun f => 𝕊.pair (𝕊.tagN 104) f
  𝕊.rec5 5 (𝕊.pair (𝕊.enc c) B) elts
    (𝕊.relFn elts fun f g => 𝕊.Rel B (𝕊.ap f 𝕊.star) (𝕊.ap g 𝕊.star))
    (𝕊.pair (𝕊.tagN 5) (𝕊.skel B))

theorem cand_inj {c d : Candidate} (h : 𝕊.cand c = 𝕊.cand d) : c = d := by
  have := congrArg 𝕊.argsOf h
  simp only [cand, argsOf_rec5] at this
  exact 𝕊.enc_inj this

/-- The candidate of a semantic type that is a proposition (the empty one otherwise). -/
noncomputable def candOf (A : 𝕊.S) : Candidate :=
  if h : ∃ c, A = 𝕊.cand c then h.choose else Candidate.empty

@[simp] theorem candOf_cand (c : Candidate) : 𝕊.candOf (𝕊.cand c) = c := by
  have h : ∃ c', 𝕊.cand c = 𝕊.cand c' := ⟨c, rfl⟩
  rw [candOf, dif_pos h]
  exact (𝕊.cand_inj h.choose_spec).symm

/-- A semantic type is a proposition. -/
def IsCand (A : 𝕊.S) : Prop := ∃ c, A = 𝕊.cand c

theorem mem_El_cand {c : Candidate} {x : 𝕊.S} :
    x ∈ₛ 𝕊.El (𝕊.cand c) ↔ x = 𝕊.star ∧ ∃ v, c.mem v := by
  simp only [cand, El_rec5]
  split
  · rw [mem_one]; exact ⟨fun h => ⟨h, ‹_›⟩, fun h => h.1⟩
  · exact ⟨fun h => (𝕊.not_mem_emptySet h).elim, fun h => (‹¬ _› h.2).elim⟩

theorem mem_El_tT {x : 𝕊.S} : x ∈ₛ 𝕊.El 𝕊.tT ↔ ∃ i, x = 𝕊.tval i := by
  simp [tT, mem_tSet]

theorem rel_tT {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) (hy : y ∈ₛ 𝕊.El 𝕊.tT) : 𝕊.Rel 𝕊.tT x y := by
  have hx' : x ∈ₛ 𝕊.tSet := by simpa [tT] using hx
  have hy' : y ∈ₛ 𝕊.tSet := by simpa [tT] using hy
  rw [Rel]
  simp only [tT, relOf_rec5]
  exact (𝕊.mem_relFn hx').2 ⟨hy', trivial⟩

/-! ### Uniform Π formation -/

/-- The candidate of a Π-proposition over a data domain: the values sending every argument
value to a realizer of every fibre. -/
noncomputable def piCand (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : Candidate where
  mem v := ∀ d, d ∈ₛ 𝕊.El D → ∀ u, (𝕊.candOf (F d)).mem (.app v u)
  step h := ⟨fun H d hd u => ((𝕊.candOf (F d)).step (.appL h)).1 (H d hd u),
    fun H d hd u => ((𝕊.candOf (F d)).step (.appL h)).2 (H d hd u)⟩

/-- **Π formation.** Over an empty proposition: the full candidate. Over a non-empty
proposition: a function proposition if the fibre is one, a `tPiP` otherwise. Over a data
domain: a Π-proposition if every fibre is a proposition, a `tPi` otherwise. -/
noncomputable def mkPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.S :=
  if 𝕊.IsCand D then
    if ∃ v, (𝕊.candOf D).mem v then
      if 𝕊.IsCand (F 𝕊.star) then 𝕊.cand (Candidate.arrow (𝕊.candOf D) (𝕊.candOf (F 𝕊.star)))
      else 𝕊.tPiP (𝕊.candOf D) (F 𝕊.star)
    else 𝕊.cand Candidate.full
  else if ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d) then 𝕊.cand (𝕊.piCand D F)
  else 𝕊.tPi D F

/-- **λ formation.** A function all of whose values are `•` is `•`; otherwise the function
object on the elements of the domain. -/
noncomputable def mkLam (D : 𝕊.S) (f : 𝕊.S → 𝕊.S) : 𝕊.S :=
  if ∀ d, d ∈ₛ 𝕊.El D → f d = 𝕊.star then 𝕊.star else 𝕊.fn (𝕊.El D) f

/-- **Application.** `•` applied to anything is `•`. -/
noncomputable def mkApp (g x : 𝕊.S) : 𝕊.S :=
  if g = 𝕊.star then 𝕊.star else 𝕊.ap g x

theorem star_ne_fn (A : 𝕊.S) (f : 𝕊.S → 𝕊.S) : 𝕊.star ≠ 𝕊.fn A f := fun h => by
  have := 𝕊.tagN_inj (𝕊.pair_inj h).1
  omega

theorem mkApp_mkLam {D : 𝕊.S} {f : 𝕊.S → 𝕊.S} {x : 𝕊.S} (hx : x ∈ₛ 𝕊.El D) :
    𝕊.mkApp (𝕊.mkLam D f) x = f x := by
  unfold mkLam
  split
  · rename_i h; simp [mkApp, h x hx]
  · rw [mkApp, if_neg (fun h => 𝕊.star_ne_fn _ _ h.symm), 𝕊.ap_fn hx]

end SetModel

end VEnv.Strengthening
end Lean4Lean
