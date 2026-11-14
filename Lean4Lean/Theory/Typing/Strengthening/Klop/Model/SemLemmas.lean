import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Interp

/-! # Elements of the semantic types

The elements and the coarse relation of each constructor, the accessors on constructors, and
the fact that `•` is not an element of a data type: every valid semantic type is a record
with a tag below `6`, every element of a data type is such a record, an element of `T` (tag
`101`) or a function (tag `104`), and `•` has tag `100`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

theorem kind_star : 𝕊.kind 𝕊.star = 𝕊.tagN 100 := by simp [kind, star]
theorem kind_cand (c : Candidate) : 𝕊.kind (𝕊.cand c) = 𝕊.tagN 0 := by simp [cand]
theorem kind_tT : 𝕊.kind 𝕊.tT = 𝕊.tagN 1 := by simp [tT]
theorem kind_tProp : 𝕊.kind 𝕊.tProp = 𝕊.tagN 2 := by simp [tProp]
theorem kind_tU (n : Nat) (tys : 𝕊.S) : 𝕊.kind (𝕊.tU n tys) = 𝕊.tagN 3 := by simp [tU]
theorem kind_tPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.kind (𝕊.tPi D F) = 𝕊.tagN 4 := by simp [tPi]
theorem kind_tPiP (c : Candidate) (B : 𝕊.S) : 𝕊.kind (𝕊.tPiP c B) = 𝕊.tagN 5 := by simp [tPiP]

/-! ### Accessors of function type records -/

@[simp] theorem dom_tPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.dom (𝕊.tPi D F) = D := by
  simp [dom, tPi]
theorem fib_tPi {D d : 𝕊.S} {F : 𝕊.S → 𝕊.S} (hd : d ∈ₛ 𝕊.El D) : 𝕊.fib (𝕊.tPi D F) d = F d := by
  simp [fib, tPi, 𝕊.app_lam hd]
@[simp] theorem cod_tPiP (c : Candidate) (B : 𝕊.S) : 𝕊.cod (𝕊.tPiP c B) = B := by
  simp [cod, tPiP]
@[simp] theorem kind_prePi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.kind (𝕊.prePi D F) = 𝕊.tagN 4 := by
  simp [prePi]
theorem sameArgs_prePi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.SameArgs (𝕊.prePi D F) (𝕊.tPi D F) := by
  simp [SameArgs, prePi, tPi]
@[simp] theorem dom_prePi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : 𝕊.dom (𝕊.prePi D F) = D := by
  rw [(sameArgs_prePi D F).dom, dom_tPi]
theorem fib_prePi {D d : 𝕊.S} {F : 𝕊.S → 𝕊.S} (hd : d ∈ₛ 𝕊.El D) :
    𝕊.fib (𝕊.prePi D F) d = F d := by
  rw [(sameArgs_prePi D F).fib, fib_tPi hd]
theorem argsOf_univ (n : Nat) : 𝕊.argsOf (𝕊.univ n) = 𝕊.enc n := by simp [univ, tU]

/-- An object whose tag is not `100` is not `•`. -/
theorem ne_star_of_kind {x : 𝕊.S} {k : Nat} (h : 𝕊.kind x = 𝕊.tagN k) (hk : k ≠ 100) :
    x ≠ 𝕊.star := by
  rintro rfl
  rw [kind_star] at h
  exact hk (𝕊.tagN_inj h).symm

theorem mem_univList {u : 𝕊.S} {n : Nat} (h : u ∈ 𝕊.univList n) : ∃ m, m < n ∧ u = 𝕊.univ m := by
  induction n with
  | zero => simp [univList] at h
  | succ n ih =>
    simp only [univList, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨m, hm, rfl⟩ := ih h
      exact ⟨m, Nat.lt_succ_of_lt hm, rfl⟩
    · exact ⟨n, Nat.lt_succ_self n, h⟩

/-- Every valid semantic type is a record with a tag below `6`. -/
theorem ValidAny.kind {lower : List 𝕊.S} (hl : ∀ u ∈ lower, ∃ m, u = 𝕊.univ m) {x : 𝕊.S}
    (H : 𝕊.ValidAny lower x) : ∃ k, k < 6 ∧ 𝕊.kind x = 𝕊.tagN k := by
  cases H with
  | prop => exact ⟨0, by decide, kind_cand _⟩
  | tT => exact ⟨1, by decide, kind_tT⟩
  | tProp => exact ⟨2, by decide, kind_tProp⟩
  | univ h => obtain ⟨m, rfl⟩ := hl _ h; exact ⟨3, by decide, kind_tU ..⟩
  | pi => exact ⟨4, by decide, kind_tPi ..⟩
  | piP => exact ⟨5, by decide, kind_tPiP ..⟩

theorem ValidAny.ne_star {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x) :
    x ≠ 𝕊.star := by
  obtain ⟨k, hk, h⟩ := H.kind fun u hu => let ⟨m, _, e⟩ := mem_univList hu; ⟨m, e⟩
  exact ne_star_of_kind h (by omega)

/-! ### Elements -/

theorem mem_El_tPiP {c : Candidate} {B x : 𝕊.S} :
    x ∈ₛ 𝕊.El (𝕊.tPiP c B) ↔
      ∃ f, x = 𝕊.pair (𝕊.tagN 104) f ∧ f ∈ₛ 𝕊.pi 𝕊.one fun _ => 𝕊.El B := by
  simp only [tPiP, El_rec5, 𝕊.mem_image]
  exact ⟨fun ⟨f, hf, e⟩ => ⟨f, e, hf⟩, fun ⟨f, e, hf⟩ => ⟨f, hf, e⟩⟩

theorem mem_El_tPi {D x : 𝕊.S} {F : 𝕊.S → 𝕊.S} :
    x ∈ₛ 𝕊.El (𝕊.tPi D F) ↔
      ∃ f, x = 𝕊.pair (𝕊.tagN 104) f ∧ (f ∈ₛ 𝕊.pi (𝕊.El D) fun d => 𝕊.El (F d)) ∧
        (∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F d) (𝕊.app f d) (𝕊.app f d')) ∧
        𝕊.PiUnif D F x := by
  simp only [tPi, El_rec5, 𝕊.mem_image, 𝕊.mem_sep]
  exact ⟨fun ⟨f, ⟨hf, hr, hu⟩, e⟩ => ⟨f, e, hf, hr, e ▸ hu⟩,
    fun ⟨f, e, hf, hr, hu⟩ => ⟨f, ⟨hf, hr, e ▸ hu⟩, e⟩⟩

/-- A function object on `A` with values in `B` is a member of the product. -/
theorem lam_mem_pi {A : 𝕊.S} {B f : 𝕊.S → 𝕊.S} (h : ∀ x, x ∈ₛ A → f x ∈ₛ B x) :
    𝕊.lam A f ∈ₛ 𝕊.pi A B := by
  refine 𝕊.mem_pi.2 ⟨𝕊.lam_ext fun x hx => (𝕊.app_lam hx).symm, fun x hx => ?_⟩
  rw [𝕊.app_lam hx]; exact h x hx

/-- Function objects are elements of `tPiP`. -/
theorem fn_mem_tPiP {c : Candidate} {B : 𝕊.S} {f : 𝕊.S → 𝕊.S}
    (h : f 𝕊.star ∈ₛ 𝕊.El B) : 𝕊.fn 𝕊.one f ∈ₛ 𝕊.El (𝕊.tPiP c B) :=
  mem_El_tPiP.2 ⟨_, rfl, lam_mem_pi fun x hx => by rw [𝕊.mem_one.1 hx]; exact h⟩

/-- Function objects respecting the relations are elements of `tPi`. -/
theorem fn_mem_tPi {D : 𝕊.S} {F f : 𝕊.S → 𝕊.S}
    (h : ∀ d, d ∈ₛ 𝕊.El D → f d ∈ₛ 𝕊.El (F d))
    (hD : ∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → d' ∈ₛ 𝕊.El D)
    (hr : ∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F d) (f d) (f d'))
    (hu : 𝕊.PiUnif D F (𝕊.fn (𝕊.El D) f)) :
    𝕊.fn (𝕊.El D) f ∈ₛ 𝕊.El (𝕊.tPi D F) := by
  refine mem_El_tPi.2 ⟨_, rfl, lam_mem_pi h, fun d d' hd hdd' => ?_, hu⟩
  rw [𝕊.app_lam hd, 𝕊.app_lam (hD d d' hd hdd')]
  exact hr d d' hd hdd'

/-- The elements of a function type are not `•`. -/
theorem ne_star_of_mem_tPiP {c : Candidate} {B x : 𝕊.S} (h : x ∈ₛ 𝕊.El (𝕊.tPiP c B)) :
    x ≠ 𝕊.star := by
  obtain ⟨f, rfl, -⟩ := mem_El_tPiP.1 h
  exact ne_star_of_kind (k := 104) (by simp [kind]) (by decide)

theorem ne_star_of_mem_tPi {D x : 𝕊.S} {F : 𝕊.S → 𝕊.S} (h : x ∈ₛ 𝕊.El (𝕊.tPi D F)) :
    x ≠ 𝕊.star := by
  obtain ⟨f, rfl, -⟩ := mem_El_tPi.1 h
  exact ne_star_of_kind (k := 104) (by simp [kind]) (by decide)

theorem ne_star_of_mem_tT {x : 𝕊.S} (h : x ∈ₛ 𝕊.El 𝕊.tT) : x ≠ 𝕊.star := by
  obtain ⟨i, rfl⟩ := 𝕊.mem_El_tT.1 h
  exact 𝕊.tval_ne_star i

/-- The elements of `Prop` are the propositions of good candidates. -/
theorem mem_El_tProp {x : 𝕊.S} : x ∈ₛ 𝕊.El 𝕊.tProp ↔ ∃ c : Candidate, c.Good ∧ x = 𝕊.cand c := by
  simp only [tProp, El_rec5, candSet, 𝕊.mem_image, 𝕊.mem_sep, 𝕊.mem_set]
  constructor
  · rintro ⟨y, ⟨-, c, hc, rfl⟩, rfl⟩
    have h : ∃ c' : Candidate, 𝕊.enc c = 𝕊.enc c' := ⟨c, rfl⟩
    rw [dif_pos h, ← 𝕊.enc_inj h.choose_spec]
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨𝕊.enc c, ⟨⟨c, rfl⟩, c, hc, rfl⟩, ?_⟩
    have h : ∃ c' : Candidate, 𝕊.enc c = 𝕊.enc c' := ⟨c, rfl⟩
    rw [dif_pos h, ← 𝕊.enc_inj h.choose_spec]

theorem ne_star_of_mem_tProp {x : 𝕊.S} (h : x ∈ₛ 𝕊.El 𝕊.tProp) : x ≠ 𝕊.star := by
  obtain ⟨c, -, rfl⟩ := mem_El_tProp.1 h
  exact ne_star_of_kind (kind_cand c) (by decide)

/-- The elements of a universe are valid types of its level. -/
theorem mem_El_univ {n : Nat} {x : 𝕊.S} :
    x ∈ₛ 𝕊.El (𝕊.univ n) ↔ x ∈ₛ 𝕊.bset (𝕊.baseOf (𝕊.univList n)) ∧ 𝕊.ValidTy (𝕊.univList n) x := by
  simp [univ, tU, 𝕊.mem_sep]

theorem ne_star_of_mem_univ {n : Nat} {x : 𝕊.S} (h : x ∈ₛ 𝕊.El (𝕊.univ n)) : x ≠ 𝕊.star :=
  (mem_El_univ.1 h).2.1.ne_star

/-- **`•` is not an element of a data type.** -/
theorem ValidAny.star_not_mem {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x)
    (hx : ¬ 𝕊.IsCand x) : ¬ 𝕊.star ∈ₛ 𝕊.El x := by
  intro hs
  cases H with
  | prop => exact hx ⟨_, rfl⟩
  | tT => exact ne_star_of_mem_tT hs rfl
  | tProp => exact ne_star_of_mem_tProp hs rfl
  | univ h =>
    obtain ⟨m, -, rfl⟩ := mem_univList h
    exact ne_star_of_mem_univ hs rfl
  | pi => exact ne_star_of_mem_tPi hs rfl
  | piP => exact ne_star_of_mem_tPiP hs rfl

/-! ### Propositions among valid types -/

theorem isCand_eq {x : 𝕊.S} (h : 𝕊.IsCand x) : x = 𝕊.cand (𝕊.candOf x) := by
  obtain ⟨c, rfl⟩ := h
  rw [𝕊.candOf_cand]

/-- A valid type that is a proposition has a good candidate. -/
theorem ValidAny.good {n : Nat} {c : Candidate} (H : 𝕊.ValidAny (𝕊.univList n) (𝕊.cand c)) :
    c.Good := by
  generalize hx : 𝕊.cand c = x at H
  have hk : 𝕊.kind x = 𝕊.tagN 0 := hx ▸ kind_cand c
  cases H with
  | prop hc => rw [𝕊.cand_inj hx]; exact hc
  | tT => rw [kind_tT] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | tProp => rw [kind_tProp] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | univ h =>
    obtain ⟨m, -, rfl⟩ := mem_univList h
    rw [SetModel.univ, kind_tU] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | pi => rw [kind_tPi] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | piP => rw [kind_tPiP] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)

theorem star_mem_cand {c : Candidate} (h : ∃ v, c.mem v) : 𝕊.star ∈ₛ 𝕊.El (𝕊.cand c) :=
  𝕊.mem_El_cand.2 ⟨rfl, h⟩

/-- A good candidate whose proposition has an element contains `bot`. -/
theorem good_bot_mem {c : Candidate} (hc : c.Good) (h : ∃ v, c.mem v) :
    c.mem .bot := by
  rcases hc with hc | hc
  · obtain ⟨v, hv⟩ := h; exact (hc v hv).elim
  · exact hc

/-! ### λ-abstractions are elements of Π-types -/

/-- **Abstraction.** A function on the elements of a valid type `D` whose values are elements
of the valid fibres `F d` and which respects the coarse relations denotes, by `mkLam`, an
element of `mkPi D F`. -/
theorem mkLam_mem_mkPi {n : Nat} {D : 𝕊.S} {F f : 𝕊.S → 𝕊.S}
    (hF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.ValidAny (𝕊.univList n) (F d))
    (hf : ∀ d, d ∈ₛ 𝕊.El D → f d ∈ₛ 𝕊.El (F d))
    (hD : ∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → d' ∈ₛ 𝕊.El D)
    (hr : ∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F d) (f d) (f d'))
    (hu : ¬ 𝕊.IsCand D → (¬ ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)) →
      𝕊.PiUnif D F (𝕊.fn (𝕊.El D) f)) :
    𝕊.mkLam D f ∈ₛ 𝕊.El (𝕊.mkPi D F) := by
  unfold mkPi
  split
  · -- the domain is a proposition
    rename_i hDc
    have hDeq := isCand_eq hDc
    split
    · rename_i hne
      have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [hDeq]; exact star_mem_cand hne
      have hall : ∀ d, d ∈ₛ 𝕊.El D → d = 𝕊.star := fun d hd => by
        rw [hDeq] at hd; exact (𝕊.mem_El_cand.1 hd).1
      split
      · -- the fibre is a proposition
        rename_i hFc
        have hfs := hf _ hs
        rw [isCand_eq hFc] at hfs
        obtain ⟨hfstar, hbne⟩ := 𝕊.mem_El_cand.1 hfs
        have hgood : (𝕊.candOf (F 𝕊.star)).Good := by
          have := hF _ hs; rw [isCand_eq hFc] at this; exact this.good
        have hl : 𝕊.mkLam D f = 𝕊.star := by
          rw [mkLam, if_pos]; intro d hd; rw [hall d hd, hfstar]
        rw [hl]
        refine star_mem_cand ⟨.bot, fun u _ => ?_⟩
        exact ((𝕊.candOf (F 𝕊.star)).step .botApp).2 (good_bot_mem hgood hbne)
      · -- the fibre is a data type
        rename_i hFc
        have hne' : f 𝕊.star ≠ 𝕊.star := fun e =>
          (hF _ hs).star_not_mem hFc (by have := hf _ hs; rwa [e] at this)
        have hl : 𝕊.mkLam D f = 𝕊.fn (𝕊.El D) f := by
          rw [mkLam, if_neg]; exact fun h => hne' (h _ hs)
        have hEl : 𝕊.El D = 𝕊.one := by
          rw [hDeq]; simp only [cand, El_rec5]; rw [if_pos hne]
        rw [hl, hEl]
        exact fn_mem_tPiP (hf _ hs)
    · -- the domain is empty
      rename_i hne
      have hl : 𝕊.mkLam D f = 𝕊.star := by
        rw [mkLam, if_pos]
        intro d hd
        rw [hDeq] at hd
        exact (hne (𝕊.mem_El_cand.1 hd).2).elim
      rw [hl]
      exact star_mem_cand ⟨.bot, trivial⟩
  · split
    · -- every fibre is a proposition
      rename_i hDc hall
      have hl : 𝕊.mkLam D f = 𝕊.star := by
        rw [mkLam, if_pos]
        intro d hd
        have := hf d hd
        rw [isCand_eq (hall d hd)] at this
        exact (𝕊.mem_El_cand.1 this).1
      rw [hl]
      refine star_mem_cand ⟨.bot, fun d hd u => ?_⟩
      have hfd := hf d hd
      have hv := hF d hd
      rw [isCand_eq (hall d hd)] at hfd hv
      exact ((𝕊.candOf (F d)).step .botApp).2 (good_bot_mem hv.good (𝕊.mem_El_cand.1 hfd).2)
    · -- some fibre is a data type
      rename_i hDc hall
      have hl : 𝕊.mkLam D f = 𝕊.fn (𝕊.El D) f := by
        rw [mkLam, if_neg]
        intro h
        apply hall
        intro d hd
        refine Classical.byContradiction fun hc => ?_
        exact (hF d hd).star_not_mem hc (by have := hf d hd; rwa [h d hd] at this)
      rw [hl]
      exact fn_mem_tPi hf hD hr (hu hDc hall)

/-! ### Applications -/

/-- **Application.** An element of `mkPi D F` applied, by `mkApp`, to an element `x` of `D`
is an element of the fibre `F x`. -/
theorem mkApp_mem {D g x : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hg : g ∈ₛ 𝕊.El (𝕊.mkPi D F)) (hx : x ∈ₛ 𝕊.El D) : 𝕊.mkApp g x ∈ₛ 𝕊.El (F x) := by
  unfold mkPi at hg
  split at hg
  · rename_i hDc
    have hDeq := isCand_eq hDc
    have hxs : x = 𝕊.star := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).1
    have hne : ∃ v, (𝕊.candOf D).mem v := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).2
    rw [if_pos hne] at hg
    subst hxs
    split at hg
    · rename_i hFc
      obtain ⟨rfl, v, hv⟩ := 𝕊.mem_El_cand.1 hg
      obtain ⟨u, hu⟩ := hne
      rw [mkApp, if_pos rfl, isCand_eq hFc]
      exact star_mem_cand ⟨_, hv u hu⟩
    · obtain ⟨f, rfl, hf⟩ := mem_El_tPiP.1 hg
      have hns : 𝕊.pair (𝕊.tagN 104) f ≠ 𝕊.star :=
        ne_star_of_kind (k := 104) (by simp [SetModel.kind]) (by decide)
      rw [mkApp, if_neg hns]
      simp only [ap, snd_pair]
      exact (𝕊.mem_pi.1 hf).2 _ (𝕊.mem_one.2 rfl)
  · split at hg
    · rename_i hall
      obtain ⟨rfl, v, hv⟩ := 𝕊.mem_El_cand.1 hg
      rw [mkApp, if_pos rfl, isCand_eq (hall x hx)]
      exact star_mem_cand ⟨_, hv x hx .bot⟩
    · obtain ⟨f, rfl, hf, -⟩ := mem_El_tPi.1 hg
      have hns : 𝕊.pair (𝕊.tagN 104) f ≠ 𝕊.star :=
        ne_star_of_kind (k := 104) (by simp [SetModel.kind]) (by decide)
      rw [mkApp, if_neg hns]
      simp only [ap, snd_pair]
      exact (𝕊.mem_pi.1 hf).2 _ hx

/-- **Application, values.** If the fibre at the argument is a proposition, the value of
the application realizes it: the value of the function realizes the Π-proposition, or the
fibre is the full candidate. -/
theorem app_val_mem {D x : 𝕊.S} {F : 𝕊.S → 𝕊.S} {vf va : PVal}
    (hx : x ∈ₛ 𝕊.El D)
    (hvf : 𝕊.IsCand (𝕊.mkPi D F) → (𝕊.candOf (𝕊.mkPi D F)).mem vf)
    (hva : 𝕊.IsCand D → (𝕊.candOf D).mem va)
    (hmix : (¬ ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)) →
      ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d) → F d = 𝕊.cand Candidate.full)
    (hFx : 𝕊.IsCand (F x)) : (𝕊.candOf (F x)).mem (.app vf va) := by
  unfold mkPi at hvf
  split at hvf
  · rename_i hDc
    have hDeq := isCand_eq hDc
    have hxs : x = 𝕊.star := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).1
    have hne : ∃ v, (𝕊.candOf D).mem v := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).2
    rw [if_pos hne] at hvf
    subst hxs
    rw [if_pos hFx, 𝕊.candOf_cand] at hvf
    exact hvf ⟨_, rfl⟩ va (hva hDc)
  · split at hvf
    · rw [𝕊.candOf_cand] at hvf
      exact hvf ⟨_, rfl⟩ x hx va
    · rename_i hDc hall
      rw [hmix hall x hx hFx, 𝕊.candOf_cand]
      trivial

/-! ### The coarse relations, unfolded -/

theorem rel_cand {c : Candidate} {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El (𝕊.cand c)) :
    𝕊.Rel (𝕊.cand c) x y ↔ y ∈ₛ 𝕊.El (𝕊.cand c) := by
  have hx' := hx
  simp only [cand, El_rec5] at hx' ⊢
  rw [Rel]; simp only [relOf_rec5]; rw [𝕊.mem_relFn hx']
  simp

theorem rel_tT_iff {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) : 𝕊.Rel 𝕊.tT x y ↔ y ∈ₛ 𝕊.El 𝕊.tT := by
  have hx' : x ∈ₛ 𝕊.tSet := by simpa [tT] using hx
  rw [Rel]; simp only [tT, relOf_rec5]; rw [𝕊.mem_relFn hx']
  simp

theorem rel_tProp_iff {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tProp) :
    𝕊.Rel 𝕊.tProp x y ↔ y ∈ₛ 𝕊.El 𝕊.tProp ∧ 𝕊.TyRel x y := by
  have hx' : x ∈ₛ 𝕊.candSet := by simpa [tProp] using hx
  rw [Rel]; simp only [tProp, relOf_rec5]; rw [𝕊.mem_relFn hx']
  simp

theorem rel_univ_iff {n : Nat} {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El (𝕊.univ n)) :
    𝕊.Rel (𝕊.univ n) x y ↔ y ∈ₛ 𝕊.El (𝕊.univ n) ∧ 𝕊.TyRel x y := by
  have hx' : x ∈ₛ 𝕊.sep (𝕊.bset (𝕊.baseOf (𝕊.univList n))) (𝕊.ValidTy (𝕊.univList n)) := by
    simpa [univ, tU] using hx
  rw [Rel]; simp only [univ, tU, relOf_rec5]; rw [𝕊.mem_relFn hx']
  simp

theorem rel_tPiP_iff {c : Candidate} {B f g : 𝕊.S} (hf : f ∈ₛ 𝕊.El (𝕊.tPiP c B)) :
    𝕊.Rel (𝕊.tPiP c B) f g ↔
      g ∈ₛ 𝕊.El (𝕊.tPiP c B) ∧ 𝕊.Rel B (𝕊.ap f 𝕊.star) (𝕊.ap g 𝕊.star) := by
  have hf' := hf
  simp only [tPiP, El_rec5] at hf' ⊢
  rw [Rel]; simp only [relOf_rec5]; rw [𝕊.mem_relFn hf']

theorem rel_tPi_iff {D f g : 𝕊.S} {F : 𝕊.S → 𝕊.S} (hf : f ∈ₛ 𝕊.El (𝕊.tPi D F)) :
    𝕊.Rel (𝕊.tPi D F) f g ↔
      g ∈ₛ 𝕊.El (𝕊.tPi D F) ∧ ∀ d, d ∈ₛ 𝕊.El D → 𝕊.Rel (F d) (𝕊.ap f d) (𝕊.ap g d) := by
  have hf' := hf
  simp only [tPi, El_rec5] at hf' ⊢
  rw [Rel]; simp only [relOf_rec5]; rw [𝕊.mem_relFn hf']

/-- The skeleton of each constructor. -/
theorem skel_cand (c : Candidate) :
    𝕊.skel (𝕊.cand c) = 𝕊.pair (𝕊.tagN 0) (𝕊.enc (decide (∃ v, c.mem v))) := by simp [cand]
theorem skel_tT : 𝕊.skel 𝕊.tT = 𝕊.pair (𝕊.tagN 1) 𝕊.star := by simp [tT]
theorem skel_tProp : 𝕊.skel 𝕊.tProp = 𝕊.pair (𝕊.tagN 2) 𝕊.star := by simp [tProp]
theorem skel_univ (n : Nat) : 𝕊.skel (𝕊.univ n) = 𝕊.pair (𝕊.tagN 3) (𝕊.enc n) := by
  simp [univ, tU]
theorem skel_tPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) :
    𝕊.skel (𝕊.tPi D F) =
      𝕊.pair (𝕊.tagN 4) (𝕊.pair (𝕊.skel D) (𝕊.lam (𝕊.El D) fun d => 𝕊.skel (F d))) := by
  simp [tPi]
theorem skel_tPiP (c : Candidate) (B : 𝕊.S) :
    𝕊.skel (𝕊.tPiP c B) = 𝕊.pair (𝕊.tagN 5) (𝕊.skel B) := by simp [tPiP]

/-- Two propositions are coarsely related exactly when both or neither is inhabited. -/
theorem tyRel_cand {c d : Candidate} :
    𝕊.TyRel (𝕊.cand c) (𝕊.cand d) ↔ ((∃ v, c.mem v) ↔ ∃ v, d.mem v) := by
  rw [TyRel, skel_cand, skel_cand]
  constructor
  · intro h
    have := 𝕊.enc_inj (𝕊.pair_inj h).2
    simpa using this
  · intro h
    simp [h]

end SetModel
end VEnv.Strengthening
end Lean4Lean
