import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SemLemmas

/-! # Universe membership

The objects of the model lie in the universes of the tower: encodings and `•` in `U 0`,
`Prop` in `U 0`, the universe `𝒰ₙ` in `U (n + 2)`. Hence `Prop` and `𝒰ₙ` are elements of the
next semantic universe, and sorts are related to themselves.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem mem_U_le {m n : Nat} {x : 𝕋.S} (h : m ≤ n) (hx : x ∈ₛ 𝕋.U m) : x ∈ₛ 𝕋.U n := by
  induction h with
  | refl => exact hx
  | step _ ih => exact 𝕋.U_mono ih

theorem enc_mem_U {α : Type} (a : α) (n : Nat) : 𝕋.enc a ∈ₛ 𝕋.U n :=
  mem_U_le (Nat.zero_le n) (𝕋.U_trans (𝕋.set_mem_U α) (𝕋.mem_set.2 ⟨a, rfl⟩))

theorem star_mem_U (n : Nat) : 𝕋.star ∈ₛ 𝕋.U n := 𝕋.pair_mem_U (enc_mem_U _ n) (enc_mem_U _ n)

theorem one_mem_U (n : Nat) : 𝕋.one ∈ₛ 𝕋.U n :=
  𝕋.image_mem_U (mem_U_le (Nat.zero_le n) (𝕋.set_mem_U _)) fun _ _ => star_mem_U n

theorem emptySet_mem_U (n : Nat) : 𝕋.emptySet ∈ₛ 𝕋.U n :=
  mem_U_le (Nat.zero_le n) (𝕋.set_mem_U _)

theorem relFn_mem_U {n : Nat} {A : 𝕋.S} {R : 𝕋.S → 𝕋.S → Prop} (hA : A ∈ₛ 𝕋.U n) :
    𝕋.relFn A R ∈ₛ 𝕋.U n :=
  𝕋.lam_mem_U hA fun _ _ => 𝕋.sep_mem_U hA

theorem rec5_mem_U {n k : Nat} {a e r s : 𝕋.S} (ha : a ∈ₛ 𝕋.U n) (he : e ∈ₛ 𝕋.U n)
    (hr : r ∈ₛ 𝕋.U n) (hs : s ∈ₛ 𝕋.U n) : 𝕋.rec5 k a e r s ∈ₛ 𝕋.U n :=
  𝕋.pair_mem_U (enc_mem_U _ n) (𝕋.pair_mem_U ha (𝕋.pair_mem_U he (𝕋.pair_mem_U hr hs)))

theorem cand_mem_U (c : Candidate) (n : Nat) : 𝕋.cand c ∈ₛ 𝕋.U n := by
  have he : (if ∃ v, c.mem v then 𝕋.one else 𝕋.emptySet) ∈ₛ 𝕋.U n := by
    split
    · exact one_mem_U n
    · exact emptySet_mem_U n
  exact rec5_mem_U (enc_mem_U _ n) he (relFn_mem_U he)
    (𝕋.pair_mem_U (enc_mem_U _ n) (enc_mem_U _ n))

theorem candSet_mem_U (n : Nat) : 𝕋.candSet ∈ₛ 𝕋.U n := by
  refine 𝕋.image_mem_U (𝕋.sep_mem_U (mem_U_le (Nat.zero_le n) (𝕋.set_mem_U _))) fun x _ => ?_
  split
  · exact cand_mem_U _ n
  · rename_i hx
    rename_i hmem
    obtain ⟨hs, -⟩ := 𝕋.mem_sep.1 hmem
    exact (hx (𝕋.mem_set.1 hs)).elim

theorem tProp_mem_U (n : Nat) : 𝕋.tProp ∈ₛ 𝕋.U n :=
  rec5_mem_U (star_mem_U n) (candSet_mem_U n) (relFn_mem_U (candSet_mem_U n))
    (𝕋.pair_mem_U (enc_mem_U _ n) (star_mem_U n))

theorem univ_mem_U (n : Nat) : 𝕋.univ n ∈ₛ 𝕋.U (n + 2) := by
  have ht : 𝕋.sep (𝕋.U (n + 1)) (𝕋.ValidTy (𝕋.univList n)) ∈ₛ 𝕋.U (n + 2) :=
    𝕋.sep_mem_U (𝕋.U_mem_U (n + 1))
  exact rec5_mem_U (enc_mem_U _ _) ht (relFn_mem_U ht)
    (𝕋.pair_mem_U (enc_mem_U _ _) (enc_mem_U _ _))

theorem univ_mem_univList (n : Nat) : 𝕋.univ n ∈ 𝕋.univList (n + 1) := by
  simp [univList, univ]

theorem univList_mono {m n : Nat} (h : m ≤ n) {u : 𝕋.S} (hu : u ∈ 𝕋.univList m) :
    u ∈ 𝕋.univList n := by
  induction h with
  | refl => exact hu
  | step _ ih => simp only [univList, List.mem_append]; exact .inl ih

theorem not_isCand_of_kind {x : 𝕋.S} {k : Nat} (h : 𝕋.kind x = 𝕋.tagN k) (hk : k ≠ 0) :
    ¬ 𝕋.IsCand x := by
  rintro ⟨c, rfl⟩
  rw [kind_cand] at h
  exact hk (𝕋.tagN_inj h).symm

theorem not_isCand_tProp : ¬ 𝕋.IsCand 𝕋.tProp := not_isCand_of_kind kind_tProp (by decide)
theorem not_isCand_univ (n : Nat) : ¬ 𝕋.IsCand (𝕋.univ n) :=
  not_isCand_of_kind (kind_tU ..) (by decide)
theorem not_isCand_tT : ¬ 𝕋.IsCand 𝕋.tT := not_isCand_of_kind kind_tT (by decide)

/-- `Prop` is an element of the first universe. -/
theorem tProp_mem_univ : 𝕋.tProp ∈ₛ 𝕋.El (𝕋.univ 0) :=
  mem_El_univ.2 ⟨tProp_mem_U 1, .tProp, fun h => (not_isCand_tProp h).elim⟩

/-- `𝒰ₙ` is an element of `𝒰ₙ₊₁`. -/
theorem univ_mem_univ (n : Nat) : 𝕋.univ n ∈ₛ 𝕋.El (𝕋.univ (n + 1)) :=
  mem_El_univ.2 ⟨univ_mem_U n, .univ (univ_mem_univList n),
    fun h => (not_isCand_univ n h).elim⟩

/-- Elements of a universe are coarsely related to themselves. -/
theorem rel_univ_refl {n : Nat} {x : 𝕋.S} (hx : x ∈ₛ 𝕋.El (𝕋.univ n)) : 𝕋.Rel (𝕋.univ n) x x := by
  have hx' : x ∈ₛ 𝕋.sep (𝕋.U (n + 1)) (𝕋.ValidTy (𝕋.univList n)) := by
    simpa [univ, tU] using hx
  rw [Rel]
  simp only [univ, tU, relOf_rec5]
  exact (𝕋.mem_relFn hx').2 ⟨hx', rfl⟩

theorem sortDen_congr {l l' : VLevel} (h : l ≈ l') : 𝕋.sortDen l = 𝕋.sortDen l' := by
  simp only [sortDen, VLevel.equiv_def.1 h []]

theorem sortDen_succ (l : VLevel) : 𝕋.sortDen (.succ l) = 𝕋.univ (l.eval []) := rfl

/-- `⟦Sort ℓ⟧` is an element of `⟦Sort (ℓ + 1)⟧`. -/
theorem sortDen_mem (l : VLevel) : 𝕋.sortDen l ∈ₛ 𝕋.El (𝕋.sortDen (.succ l)) := by
  rw [sortDen_succ]
  unfold sortDen
  cases l.eval [] with
  | zero => exact tProp_mem_univ
  | succ n => exact univ_mem_univ n

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
