import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Univ

/-! # Coarsely related types have the same elements

`ValidAny.tyRel_same`: two valid semantic types with the same skeleton have the same set of
elements and the same coarse relation on it. By induction on the validity of the first.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The skeleton of a valid type is a pair headed by the type's tag. -/
theorem ValidAny.skel_tag {n : Nat} {x : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList n) x) :
    ∃ k s, k < 6 ∧ 𝕋.skel x = 𝕋.pair (𝕋.tagN k) s ∧ 𝕋.kind x = 𝕋.tagN k := by
  cases H with
  | prop => exact ⟨0, _, by decide, skel_cand _, kind_cand _⟩
  | tT => exact ⟨1, _, by decide, skel_tT, kind_tT⟩
  | tProp => exact ⟨2, _, by decide, skel_tProp, kind_tProp⟩
  | univ h =>
    obtain ⟨m, -, rfl⟩ := mem_univList h
    exact ⟨3, _, by decide, skel_univ m, kind_tU ..⟩
  | pi => exact ⟨4, _, by decide, skel_tPi .., kind_tPi ..⟩
  | piP => exact ⟨5, _, by decide, skel_tPiP .., kind_tPiP ..⟩

/-- Coarsely related valid types have the same tag. -/
theorem ValidAny.kind_eq_of_tyRel {n : Nat} {A B : 𝕋.S} (hA : 𝕋.ValidAny (𝕋.univList n) A)
    (hB : 𝕋.ValidAny (𝕋.univList n) B) (h : 𝕋.TyRel A B) : 𝕋.kind A = 𝕋.kind B := by
  obtain ⟨k, s, -, hs, hk⟩ := hA.skel_tag
  obtain ⟨k', s', -, hs', hk'⟩ := hB.skel_tag
  rw [TyRel, hs, hs'] at h
  rw [hk, hk', (𝕋.pair_inj h).1]

/-- The statement proved by induction: same elements and same relation. -/
def SameEl (𝕋 : UniverseTower) (A B : 𝕋.S) : Prop :=
  𝕋.El A = 𝕋.El B ∧ ∀ x y, 𝕋.mem x (𝕋.El A) → (𝕋.Rel A x y ↔ 𝕋.Rel B x y)

theorem sameEl_refl (A : 𝕋.S) : 𝕋.SameEl A A := ⟨rfl, fun _ _ _ => .rfl⟩

theorem pi_congr {A : 𝕋.S} {B B' : 𝕋.S → 𝕋.S} (h : ∀ x, x ∈ₛ A → B x = B' x) :
    𝕋.pi A B = 𝕋.pi A B' := by
  refine 𝕋.ext fun f => ?_
  rw [𝕋.mem_pi, 𝕋.mem_pi]
  exact and_congr_right fun _ => forall_congr' fun x => imp_congr_right fun hx => by rw [h x hx]

/-- **Coarsely related valid types have the same elements and the same relation.** -/
theorem ValidAny.tyRel_same {n : Nat} {A : 𝕋.S} (hA : 𝕋.ValidAny (𝕋.univList n) A) :
    ∀ {B : 𝕋.S}, 𝕋.ValidAny (𝕋.univList n) B → 𝕋.TyRel A B → 𝕋.SameEl A B := by
  induction hA with
  | @prop c hc =>
    intro B hB h
    have hk := (ValidAny.prop hc).kind_eq_of_tyRel hB h
    rw [kind_cand] at hk
    cases hB with
    | @prop d hd =>
      have hiff := tyRel_cand.1 h
      have hEl : 𝕋.El (𝕋.cand c) = 𝕋.El (𝕋.cand d) := by
        simp only [cand, El_rec5]
        by_cases hcne : ∃ v, c.mem v
        · rw [if_pos hcne, if_pos (hiff.1 hcne)]
        · rw [if_neg hcne, if_neg (fun h => hcne (hiff.2 h))]
      refine ⟨hEl, fun x y hx => ?_⟩
      rw [rel_cand hx, rel_cand (hEl ▸ hx), hEl]
    | tT => rw [kind_tT] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | univ hu =>
      obtain ⟨m, -, rfl⟩ := mem_univList hu
      rw [UniverseTower.univ, kind_tU] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | pi => rw [kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  | tT =>
    intro B hB h
    have hk := ValidAny.tT.kind_eq_of_tyRel hB h
    rw [kind_tT] at hk
    cases hB with
    | prop => rw [kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tT => exact sameEl_refl _
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | univ hu =>
      obtain ⟨m, -, rfl⟩ := mem_univList hu
      rw [UniverseTower.univ, kind_tU] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | pi => rw [kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  | tProp =>
    intro B hB h
    have hk := ValidAny.tProp.kind_eq_of_tyRel hB h
    rw [kind_tProp] at hk
    cases hB with
    | prop => rw [kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tT => rw [kind_tT] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tProp => exact sameEl_refl _
    | univ hu =>
      obtain ⟨m, -, rfl⟩ := mem_univList hu
      rw [UniverseTower.univ, kind_tU] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | pi => rw [kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  | @univ u hu =>
    intro B hB h
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    have hk := (ValidAny.univ hu).kind_eq_of_tyRel hB h
    rw [UniverseTower.univ, kind_tU] at hk
    cases hB with
    | prop => rw [kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tT => rw [kind_tT] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | univ hu' =>
      obtain ⟨m', -, rfl⟩ := mem_univList hu'
      rw [TyRel, skel_univ, skel_univ] at h
      have : m = m' := 𝕋.enc_inj (𝕋.pair_inj h).2
      subst this
      exact sameEl_refl _
    | pi => rw [kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  | @pi D F hD hDc hF hfull hFrel hmix ihD ihF =>
    intro B hB h
    have hk := (ValidAny.pi hD hDc hF hfull hFrel hmix).kind_eq_of_tyRel hB h
    rw [kind_tPi] at hk
    cases hB with
    | prop => rw [kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tT => rw [kind_tT] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | univ hu' =>
      obtain ⟨m', -, rfl⟩ := mem_univList hu'
      rw [UniverseTower.univ, kind_tU] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | @pi D' F' hD' hDc' hF' hfull' hFrel' hmix' =>
      rw [TyRel, skel_tPi, skel_tPi] at h
      obtain ⟨hsD, hsF⟩ := 𝕋.pair_inj (𝕋.pair_inj h).2
      obtain ⟨hElD, hRelD⟩ := ihD hD' hsD
      have hfib : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.SameEl (F d) (F' d) := fun d hd => by
        refine ihF d hd (hF' d (hElD ▸ hd)) ?_
        have : 𝕋.app (𝕋.lam (𝕋.El D) fun d => 𝕋.skel (F d)) d =
            𝕋.app (𝕋.lam (𝕋.El D') fun d => 𝕋.skel (F' d)) d := by rw [hsF]
        rwa [𝕋.app_lam hd, 𝕋.app_lam (hElD ▸ hd)] at this
      have hpi : (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) = 𝕋.pi (𝕋.El D') fun d => 𝕋.El (F' d) := by
        rw [← hElD]; exact pi_congr fun d hd => (hfib d hd).1
      have hmem : ∀ x, x ∈ₛ 𝕋.El (𝕋.tPi D F) ↔ x ∈ₛ 𝕋.El (𝕋.tPi D' F') := by
        intro x
        rw [mem_El_tPi, mem_El_tPi]
        refine exists_congr fun f => and_congr_right fun _ => ?_
        rw [← hpi]
        refine and_congr_right fun hf => ?_
        refine forall_congr' fun d => forall_congr' fun d' => ?_
        rw [← hElD]
        refine imp_congr_right fun hd => ?_
        rw [hRelD d d' hd, (hfib d hd).2 _ _ ((𝕋.mem_pi.1 hf).2 d hd)]
      have hEl := 𝕋.ext hmem
      refine ⟨hEl, fun f g hf => ?_⟩
      rw [rel_tPi_iff hf, rel_tPi_iff (hEl ▸ hf), hEl, ← hElD]
      refine and_congr_right fun _ => forall_congr' fun d => imp_congr_right fun hd => ?_
      obtain ⟨f', rfl, hf', -⟩ := mem_El_tPi.1 hf
      refine (hfib d hd).2 _ _ ?_
      simp only [ap, snd_pair]
      exact (𝕋.mem_pi.1 hf').2 d hd
    | piP => rw [kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  | @piP c B₀ hc hne hB₀ hB₀c ih =>
    intro B hB h
    have hk := (ValidAny.piP hc hne hB₀ hB₀c).kind_eq_of_tyRel hB h
    rw [kind_tPiP] at hk
    cases hB with
    | prop => rw [kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tT => rw [kind_tT] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | tProp => rw [kind_tProp] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | univ hu' =>
      obtain ⟨m', -, rfl⟩ := mem_univList hu'
      rw [UniverseTower.univ, kind_tU] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | pi => rw [kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    | @piP c' B₁ hc' hne' hB₁ hB₁c =>
      rw [TyRel, skel_tPiP, skel_tPiP] at h
      obtain ⟨hElB, hRelB⟩ := ih hB₁ (𝕋.pair_inj h).2
      have hEl : 𝕋.El (𝕋.tPiP c B₀) = 𝕋.El (𝕋.tPiP c' B₁) := by
        simp only [tPiP, El_rec5, hElB]
      refine ⟨hEl, fun f g hf => ?_⟩
      rw [rel_tPiP_iff hf, rel_tPiP_iff (hEl ▸ hf), hEl]
      refine and_congr_right fun _ => ?_
      obtain ⟨f', rfl, hf'⟩ := mem_El_tPiP.1 hf
      refine hRelB _ _ ?_
      simp only [ap, snd_pair]
      exact (𝕋.mem_pi.1 hf').2 _ (𝕋.mem_one.2 rfl)

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
