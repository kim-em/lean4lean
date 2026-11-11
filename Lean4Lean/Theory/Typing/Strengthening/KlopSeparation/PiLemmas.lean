import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.TyRelLemmas

/-! # Π formation is valid

`mkPi_valid`: the Π-type formed from a valid domain and valid fibres that respect the coarse
relation, all propositions or all members of a data universe, is a valid semantic type.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- A good candidate is empty or contains `bot`; if it has an element it contains `bot`. -/
theorem good_cases {c : Candidate} (hc : c.Good) : (∀ v, ¬ c.mem v) ∨ c.mem .bot := hc

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
theorem piCand_nonempty_iff {D : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hF : ∀ d, d ∈ₛ 𝕋.El D → (𝕋.candOf (F d)).Good) :
    (∃ v, (𝕋.piCand D F).mem v) ↔ ∀ d, d ∈ₛ 𝕋.El D → ∃ w, (𝕋.candOf (F d)).mem w := by
  constructor
  · rintro ⟨v, hv⟩ d hd
    exact ⟨_, hv d hd .bot⟩
  · intro h
    exact ⟨.bot, fun d hd u => ((𝕋.candOf (F d)).step .botApp).2 (good_bot_mem (hF d hd) (h d hd))⟩

theorem good_piCand {D : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hF : ∀ d, d ∈ₛ 𝕋.El D → (𝕋.candOf (F d)).Good) : (𝕋.piCand D F).Good := by
  by_cases h : ∀ d, d ∈ₛ 𝕋.El D → ∃ w, (𝕋.candOf (F d)).mem w
  · exact .inr fun d hd u => ((𝕋.candOf (F d)).step .botApp).2 (good_bot_mem (hF d hd) (h d hd))
  · exact .inl fun v hv => h ((piCand_nonempty_iff hF).1 ⟨v, hv⟩)

/-- **Π formation is valid.** -/
theorem mkPi_valid {n : Nat} {D : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hD : 𝕋.ValidAny (𝕋.univList n) D)
    (hF : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.ValidAny (𝕋.univList n) (F d))
    (hFrel : ∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.TyRel (F d) (F d'))
    (hsort : (∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d) → F d = 𝕋.cand Candidate.full) ∨
      ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)) :
    𝕋.ValidAny (𝕋.univList n) (𝕋.mkPi D F) := by
  unfold mkPi
  split
  · rename_i hDc
    have hDeq := isCand_eq hDc
    split
    · rename_i hne
      have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [hDeq]; exact star_mem_cand hne
      split
      · rename_i hFc
        have hg : (𝕋.candOf (F 𝕋.star)).Good := by
          have := hF _ hs; rw [isCand_eq hFc] at this; exact this.good
        exact .prop (good_arrow hg)
      · rename_i hFc
        have hgD : (𝕋.candOf D).Good := by
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
      refine .pi hD hDc hF ?_ hFrel hall
      rcases hsort with h | h
      · exact h
      · exact (hall h).elim

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
