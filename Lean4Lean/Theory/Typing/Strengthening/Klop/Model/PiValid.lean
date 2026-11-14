import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.TyRelLemmas

/-! # Π formation is valid

`mkPi_valid`: the Π-type formed from a valid domain and valid fibres that respect the coarse
relation, all propositions or all members of a data universe, is a valid semantic type.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- A function proposition into a good candidate is inhabited exactly when the domain is
empty or the codomain is inhabited. -/
theorem arrow_nonempty_iff {c b : Candidate} (hb : b.Good) :
    (∃ v, (Candidate.arrow c b).mem v) ↔ (¬ ∃ u, c.mem u) ∨ ∃ w, b.mem w := by
  constructor
  · rintro ⟨v, hv⟩
    by_cases hc : ∃ u, c.mem u
    · obtain ⟨u, hu⟩ := hc
      exact .inr ⟨_, hv u hu⟩
    · exact .inl hc
  · rintro (hc | hw)
    · exact ⟨.bot, fun u hu => (hc ⟨u, hu⟩).elim⟩
    · exact ⟨.bot, fun u _ => (b.step .botApp).2 (good_bot_mem hb hw)⟩

theorem good_arrow {c b : Candidate} (hb : b.Good) : (Candidate.arrow c b).Good := by
  rcases hb with hb | hb
  · by_cases hc : ∃ u, c.mem u
    · obtain ⟨u, hu⟩ := hc
      exact .inl fun v hv => hb _ (hv u hu)
    · exact .inr fun u hu => (hc ⟨u, hu⟩).elim
  · exact .inr fun u _ => (b.step .botApp).2 hb

/-- A Π-proposition over a data domain with good fibres is inhabited exactly when every
fibre is. -/
theorem piCand_nonempty_iff {D : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hF : ∀ d, d ∈ₛ 𝕊.El D → (𝕊.candOf (F d)).Good) :
    (∃ v, (𝕊.piCand D F).mem v) ↔ ∀ d, d ∈ₛ 𝕊.El D → ∃ w, (𝕊.candOf (F d)).mem w := by
  constructor
  · rintro ⟨v, hv⟩ d hd
    exact ⟨_, hv d hd .bot⟩
  · intro h
    exact ⟨.bot, fun d hd u => ((𝕊.candOf (F d)).step .botApp).2 (good_bot_mem (hF d hd) (h d hd))⟩

theorem good_piCand {D : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hF : ∀ d, d ∈ₛ 𝕊.El D → (𝕊.candOf (F d)).Good) : (𝕊.piCand D F).Good := by
  by_cases h : ∀ d, d ∈ₛ 𝕊.El D → ∃ w, (𝕊.candOf (F d)).mem w
  · exact .inr fun d hd u => ((𝕊.candOf (F d)).step .botApp).2 (good_bot_mem (hF d hd) (h d hd))
  · exact .inl fun v hv => h ((piCand_nonempty_iff hF).1 ⟨v, hv⟩)

/-- **Π formation is valid.** -/
theorem mkPi_valid {n : Nat} {D : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hD : 𝕊.ValidAny (𝕊.univList n) D)
    (hF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.ValidAny (𝕊.univList n) (F d))
    (hFrel : ∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.TyRel (F d) (F d'))
    (hsort : (∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d) → F d = 𝕊.cand Candidate.full) ∨
      ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d))
    (hfam : ¬ 𝕊.IsCand D → 𝕊.FamUnif D F) :
    𝕊.ValidAny (𝕊.univList n) (𝕊.mkPi D F) := by
  unfold mkPi
  split
  · rename_i hDc
    have hDeq := isCand_eq hDc
    split
    · rename_i hne
      have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [hDeq]; exact star_mem_cand hne
      split
      · rename_i hFc
        have hg : (𝕊.candOf (F 𝕊.star)).Good := by
          have := hF _ hs; rw [isCand_eq hFc] at this; exact this.good
        exact .prop (good_arrow hg)
      · rename_i hFc
        have hgD : (𝕊.candOf D).Good := by
          have := hD; rw [hDeq] at this; exact this.good
        exact .piP hgD hne (hF _ hs) hFc
    · exact .prop Candidate.good_full
  · rename_i hDc
    split
    · rename_i hall
      refine .prop (good_piCand fun d hd => ?_)
      have := hF d hd
      rw [isCand_eq (hall d hd)] at this
      exact this.good
    · rename_i hall
      refine .pi hD hDc hF ?_ hFrel hall (hfam hDc)
      rcases hsort with h | h
      · exact h
      · exact (hall h).elim

/-! ### Π formation respects the coarse relation -/

/-- A valid type is a proposition exactly when its tag is `0`. -/
theorem ValidAny.isCand_iff {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x) :
    𝕊.IsCand x ↔ 𝕊.kind x = 𝕊.tagN 0 := by
  constructor
  · rintro ⟨c, rfl⟩; exact kind_cand c
  · intro hk
    cases H with
    | prop => exact ⟨_, rfl⟩
    | tT => rw [kind_tT] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
    | univ hu =>
      obtain ⟨m, -, rfl⟩ := mem_univList hu
      rw [SetModel.univ, kind_tU] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
    | pi => rw [kind_tPi] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)

/-- Coarsely related valid types are both propositions or both data types. -/
theorem ValidAny.isCand_congr {n : Nat} {A B : 𝕊.S} (hA : 𝕊.ValidAny (𝕊.univList n) A)
    (hB : 𝕊.ValidAny (𝕊.univList n) B) (h : 𝕊.TyRel A B) : 𝕊.IsCand A ↔ 𝕊.IsCand B := by
  rw [hA.isCand_iff, hB.isCand_iff, hA.kind_eq_of_tyRel hB h]

/-- Coarsely related propositions are both inhabited or both empty. -/
theorem nonempty_congr {A B : 𝕊.S} (hA : 𝕊.IsCand A) (hB : 𝕊.IsCand B) (h : 𝕊.TyRel A B) :
    (∃ v, (𝕊.candOf A).mem v) ↔ ∃ v, (𝕊.candOf B).mem v := by
  rw [isCand_eq hA, isCand_eq hB] at h
  exact tyRel_cand.1 h

/-- **Π formation respects the coarse relation.** -/
theorem mkPi_tyRel {n : Nat} {D D' : 𝕊.S} {F F' : 𝕊.S → 𝕊.S}
    (hD : 𝕊.ValidAny (𝕊.univList n) D) (hD' : 𝕊.ValidAny (𝕊.univList n) D')
    (hDD' : 𝕊.TyRel D D')
    (hF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.ValidAny (𝕊.univList n) (F d))
    (hF' : ∀ d, d ∈ₛ 𝕊.El D' → 𝕊.ValidAny (𝕊.univList n) (F' d))
    (hFF' : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.TyRel (F d) (F' d)) :
    𝕊.TyRel (𝕊.mkPi D F) (𝕊.mkPi D' F') := by
  have hEl : 𝕊.El D = 𝕊.El D' := (hD.tyRel_same hD' hDD').1
  have hcD := hD.isCand_congr hD' hDD'
  have hcF : ∀ d, d ∈ₛ 𝕊.El D → (𝕊.IsCand (F d) ↔ 𝕊.IsCand (F' d)) := fun d hd =>
    (hF d hd).isCand_congr (hF' d (hEl ▸ hd)) (hFF' d hd)
  have hgF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d) → (𝕊.candOf (F d)).Good := fun d hd hc => by
    have := hF d hd; rw [isCand_eq hc] at this; exact this.good
  have hgF' : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F' d) → (𝕊.candOf (F' d)).Good := fun d hd hc => by
    have := hF' d (hEl ▸ hd); rw [isCand_eq hc] at this; exact this.good
  unfold mkPi
  by_cases hDc : 𝕊.IsCand D
  · have hDc' := hcD.1 hDc
    rw [if_pos hDc, if_pos hDc']
    have hne := nonempty_congr hDc hDc' hDD'
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · rw [if_pos hn, if_pos (hne.1 hn)]
      have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      by_cases hFc : 𝕊.IsCand (F 𝕊.star)
      · have hFc' := (hcF _ hs).1 hFc
        rw [if_pos hFc, if_pos hFc']
        refine tyRel_cand.2 ?_
        rw [arrow_nonempty_iff (hgF _ hs hFc), arrow_nonempty_iff (hgF' _ hs hFc'), hne,
          nonempty_congr hFc hFc' (hFF' _ hs)]
      · have hFc' : ¬ 𝕊.IsCand (F' 𝕊.star) := fun h => hFc ((hcF _ hs).2 h)
        rw [if_neg hFc, if_neg hFc', TyRel, skel_tPiP, skel_tPiP, hFF' _ hs]
    · rw [if_neg hn, if_neg (fun h => hn (hne.2 h))]
      exact rfl
  · have hDc' : ¬ 𝕊.IsCand D' := fun h => hDc (hcD.2 h)
    rw [if_neg hDc, if_neg hDc']
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · have hall' : ∀ d, d ∈ₛ 𝕊.El D' → 𝕊.IsCand (F' d) := fun d hd =>
        (hcF d (hEl ▸ hd)).1 (hall d (hEl ▸ hd))
      rw [if_pos hall, if_pos hall']
      refine tyRel_cand.2 ?_
      rw [piCand_nonempty_iff fun d hd => hgF d hd (hall d hd),
        piCand_nonempty_iff fun d hd => hgF' d (hEl ▸ hd) (hall' d hd), ← hEl]
      exact forall_congr' fun d => imp_congr_right fun hd =>
        nonempty_congr (hall d hd) (hall' d (hEl ▸ hd)) (hFF' d hd)
    · have hall' : ¬ ∀ d, d ∈ₛ 𝕊.El D' → 𝕊.IsCand (F' d) := fun h =>
        hall fun d hd => (hcF d hd).2 (h d (hEl ▸ hd))
      rw [if_neg hall, if_neg hall', TyRel, skel_tPi, skel_tPi, ← hEl, hDD',
        𝕊.lam_ext fun d hd => hFF' d hd]

/-! ### Application respects the coarse relations -/

/-- **Application respects the coarse relations.** Coarsely related elements of a Π-type
applied to coarsely related arguments give coarsely related results. -/
theorem mkApp_rel {n : Nat} {D g g' x x' : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.ValidAny (𝕊.univList n) (F d))
    (hg : g ∈ₛ 𝕊.El (𝕊.mkPi D F)) (hgg' : 𝕊.Rel (𝕊.mkPi D F) g g')
    (hx : x ∈ₛ 𝕊.El D) (hxx' : 𝕊.Rel D x x') :
    𝕊.Rel (F x) (𝕊.mkApp g x) (𝕊.mkApp g' x') := by
  have hres := mkApp_mem hg hx
  have hper := (hF x hx).isPER
  unfold mkPi at hg hgg'
  split at hg
  · rename_i hDc
    have hDeq := isCand_eq hDc
    have hxs : x = 𝕊.star := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).1
    have hne : ∃ v, (𝕊.candOf D).mem v := by rw [hDeq] at hx; exact (𝕊.mem_El_cand.1 hx).2
    have hxs' : x' = 𝕊.star := by
      rw [hDeq] at hxx' hx
      exact (𝕊.mem_El_cand.1 ((rel_cand hx).1 hxx')).1
    rw [if_pos hDc, if_pos hne] at hgg'
    rw [if_pos hne] at hg
    subst hxs hxs'
    split at hg
    · rename_i hFc
      rw [if_pos hFc] at hgg'
      have hg's := (𝕊.mem_El_cand.1 ((rel_cand hg).1 hgg')).1
      have hgs := (𝕊.mem_El_cand.1 hg).1
      subst hg's hgs
      exact hper.refl _ hres
    · rename_i hFc
      rw [if_neg hFc] at hgg'
      obtain ⟨hg', hr⟩ := (rel_tPiP_iff hg).1 hgg'
      rw [mkApp, if_neg (ne_star_of_mem_tPiP hg), mkApp, if_neg (ne_star_of_mem_tPiP hg')]
      exact hr
  · rename_i hDc
    rw [if_neg hDc] at hgg'
    split at hg
    · rename_i hall
      rw [if_pos hall] at hgg'
      have hg's := (𝕊.mem_El_cand.1 ((rel_cand hg).1 hgg')).1
      have hgs := (𝕊.mem_El_cand.1 hg).1
      subst hg's hgs
      have : 𝕊.mkApp 𝕊.star x' = 𝕊.mkApp 𝕊.star x := by simp [mkApp]
      rw [this]
      exact hper.refl _ hres
    · rename_i hall
      rw [if_neg hall] at hgg'
      obtain ⟨hg', hr⟩ := (rel_tPi_iff hg).1 hgg'
      rw [mkApp, if_neg (ne_star_of_mem_tPi hg), mkApp, if_neg (ne_star_of_mem_tPi hg')]
      obtain ⟨f', rfl, -, hresp, -⟩ := mem_El_tPi.1 hg'
      have h2 : 𝕊.Rel (F x) (𝕊.ap (𝕊.pair (𝕊.tagN 104) f') x)
          (𝕊.ap (𝕊.pair (𝕊.tagN 104) f') x') := by
        simp only [ap, snd_pair]
        exact hresp x x' hx hxx'
      exact hper.trans _ _ _ (ap_mem_of_mem_tPi hg hx) (hr x hx) h2

end SetModel
end VEnv.Strengthening
end Lean4Lean
