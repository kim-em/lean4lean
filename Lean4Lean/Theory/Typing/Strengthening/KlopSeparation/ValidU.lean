import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.PiLemmas

/-! # Valid types lie in the tower's universes

`ValidAny.mono`: validity is monotone in the level. `ValidAny.mem_U`: a valid semantic type
of level `n`, its set of elements and its skeleton are members of `U (n + 1)`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- Validity is monotone in the list of lower universes. -/
theorem ValidAny.mono_list {l l' : List 𝕋.S} (h : ∀ u, u ∈ l → u ∈ l') {x : 𝕋.S}
    (H : 𝕋.ValidAny l x) : 𝕋.ValidAny l' x := by
  induction H with
  | prop hc => exact .prop hc
  | tT => exact .tT
  | tProp => exact .tProp
  | univ hu => exact .univ (h _ hu)
  | pi _ hDc _ hfull hrel hmix ihD ihF => exact .pi ihD hDc ihF hfull hrel hmix
  | piP hc hne _ hBc ih => exact .piP hc hne ih hBc

/-- Validity is monotone in the level. -/
theorem ValidAny.mono {m n : Nat} (h : m ≤ n) {x : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList m) x) :
    𝕋.ValidAny (𝕋.univList n) x :=
  H.mono_list fun _ hu => univList_mono h hu

theorem tSet_mem_U (n : Nat) : 𝕋.tSet ∈ₛ 𝕋.U n :=
  𝕋.image_mem_U (mem_U_le (Nat.zero_le n) (𝕋.set_mem_U _)) fun x hx => by
    obtain ⟨i, rfl⟩ := 𝕋.mem_set.1 hx
    exact 𝕋.pair_mem_U (enc_mem_U _ n) (enc_mem_U _ n)

theorem tT_mem_U (n : Nat) : 𝕋.tT ∈ₛ 𝕋.U n :=
  rec5_mem_U (star_mem_U n) (tSet_mem_U n) (relFn_mem_U (tSet_mem_U n))
    (𝕋.pair_mem_U (enc_mem_U _ n) (star_mem_U n))

/-- A valid type, its elements and its skeleton lie in a universe of the tower. -/
structure InU (𝕋 : UniverseTower) (k : Nat) (x : 𝕋.S) : Prop where
  self : 𝕋.mem x (𝕋.U k)
  el : 𝕋.mem (𝕋.El x) (𝕋.U k)
  skel : 𝕋.mem (𝕋.skel x) (𝕋.U k)

theorem inU_cand (c : Candidate) (k : Nat) : 𝕋.InU k (𝕋.cand c) := by
  refine ⟨cand_mem_U c k, ?_, ?_⟩
  · simp only [cand, El_rec5]
    split
    · exact one_mem_U k
    · exact emptySet_mem_U k
  · rw [skel_cand]; exact 𝕋.pair_mem_U (enc_mem_U _ k) (enc_mem_U _ k)

/-- **Valid types of level `n` lie in `U (n + 1)`**, with their elements and skeletons. -/
theorem ValidAny.inU {n : Nat} {x : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList n) x) :
    𝕋.InU (n + 1) x := by
  induction H with
  | prop => exact inU_cand _ _
  | tT =>
    refine ⟨tT_mem_U _, ?_, ?_⟩
    · simp only [UniverseTower.tT, El_rec5]; exact tSet_mem_U _
    · rw [skel_tT]; exact 𝕋.pair_mem_U (enc_mem_U _ _) (star_mem_U _)
  | tProp =>
    refine ⟨tProp_mem_U _, ?_, ?_⟩
    · simp only [UniverseTower.tProp, El_rec5]; exact candSet_mem_U _
    · rw [skel_tProp]; exact 𝕋.pair_mem_U (enc_mem_U _ _) (star_mem_U _)
  | univ hu =>
    obtain ⟨m, hm, rfl⟩ := mem_univList hu
    have hle : m + 2 ≤ n + 1 := by omega
    refine ⟨mem_U_le hle (univ_mem_U m), ?_, ?_⟩
    · simp only [UniverseTower.univ, tU, El_rec5]
      exact mem_U_le hle (𝕋.sep_mem_U (𝕋.U_mem_U (m + 1)))
    · rw [skel_univ]; exact 𝕋.pair_mem_U (enc_mem_U _ _) (enc_mem_U _ _)
  | @pi D F _ _ _ _ _ _ ihD ihF =>
    have hpi : 𝕋.pi (𝕋.El D) (fun d => 𝕋.El (F d)) ∈ₛ 𝕋.U (n + 1) :=
      𝕋.pi_mem_U ihD.el fun d hd => (ihF d hd).el
    have hel : 𝕋.El (𝕋.tPi D F) ∈ₛ 𝕋.U (n + 1) := by
      simp only [tPi, El_rec5]
      refine 𝕋.image_mem_U (𝕋.sep_mem_U hpi) fun f hf => ?_
      exact 𝕋.pair_mem_U (enc_mem_U _ _) (𝕋.U_trans hpi (𝕋.mem_sep.1 hf).1)
    have hsk : 𝕋.skel (𝕋.tPi D F) ∈ₛ 𝕋.U (n + 1) := by
      rw [skel_tPi]
      exact 𝕋.pair_mem_U (enc_mem_U _ _) (𝕋.pair_mem_U ihD.skel
        (𝕋.lam_mem_U ihD.el fun d hd => (ihF d hd).skel))
    refine ⟨?_, hel, hsk⟩
    have hel' := hel
    have hsk' := hsk
    simp only [tPi, El_rec5, skel_rec5] at hel' hsk'
    exact rec5_mem_U (𝕋.pair_mem_U ihD.self (𝕋.lam_mem_U ihD.el fun d hd => (ihF d hd).self))
      hel' (relFn_mem_U hel') hsk'
  | @piP c B _ _ _ _ ih =>
    have hpi : 𝕋.pi 𝕋.one (fun _ => 𝕋.El B) ∈ₛ 𝕋.U (n + 1) :=
      𝕋.pi_mem_U (one_mem_U _) fun _ _ => ih.el
    have hel : 𝕋.El (𝕋.tPiP c B) ∈ₛ 𝕋.U (n + 1) := by
      simp only [tPiP, El_rec5]
      refine 𝕋.image_mem_U hpi fun f hf => ?_
      exact 𝕋.pair_mem_U (enc_mem_U _ _) (𝕋.U_trans hpi hf)
    have hsk : 𝕋.skel (𝕋.tPiP c B) ∈ₛ 𝕋.U (n + 1) := by
      rw [skel_tPiP]; exact 𝕋.pair_mem_U (enc_mem_U _ _) ih.skel
    refine ⟨?_, hel, hsk⟩
    have hel' := hel
    have hsk' := hsk
    simp only [tPiP, El_rec5, skel_rec5] at hel' hsk'
    exact rec5_mem_U (𝕋.pair_mem_U (enc_mem_U _ _) ih.self) hel' (relFn_mem_U hel') hsk'

/-- A valid data type of level `n` (or the full candidate) is an element of `𝒰ₙ`. -/
theorem ValidAny.mem_univ {n : Nat} {x : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList n) x)
    (hc : 𝕋.IsCand x → x = 𝕋.cand Candidate.full) : x ∈ₛ 𝕋.El (𝕋.univ n) :=
  mem_El_univ.2 ⟨H.inU.self, H, hc⟩

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
