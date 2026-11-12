import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SemLemmas

/-! # Universe membership

`Prop` and `𝒰ₙ` are elements of the next semantic universe, because they are in the base of
its bounding set, and sorts are related to themselves.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕋 : SetModel}

local infix:50 " ∈ₛ " => 𝕋.mem

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

theorem mem_bset_of_base {base x : 𝕋.S} (h : x ∈ₛ base) : x ∈ₛ 𝕋.bset base :=
  mem_bset.2 ⟨0, h⟩

/-- `Prop` is an element of the first universe. -/
theorem tProp_mem_univ : 𝕋.tProp ∈ₛ 𝕋.El (𝕋.univ 0) :=
  mem_El_univ.2 ⟨mem_bset_of_base (mem_baseOf.2 (.inr (.inr (.inl rfl)))), .tProp,
    fun h => (not_isCand_tProp h).elim⟩

/-- `𝒰ₙ` is an element of `𝒰ₙ₊₁`. -/
theorem univ_mem_univ (n : Nat) : 𝕋.univ n ∈ₛ 𝕋.El (𝕋.univ (n + 1)) :=
  mem_El_univ.2 ⟨mem_bset_of_base (mem_baseOf.2
      (.inr (.inr (.inr ⟨_, univ_mem_univList n, .inl rfl⟩)))),
    .univ (univ_mem_univList n), fun h => (not_isCand_univ n h).elim⟩

/-- Elements of a universe are coarsely related to themselves. -/
theorem rel_univ_refl {n : Nat} {x : 𝕋.S} (hx : x ∈ₛ 𝕋.El (𝕋.univ n)) : 𝕋.Rel (𝕋.univ n) x x := by
  have hx' : x ∈ₛ 𝕋.sep (𝕋.bset (𝕋.baseOf (𝕋.univList n))) (𝕋.ValidTy (𝕋.univList n)) := by
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

end SetModel
end VEnv.Strengthening
end Lean4Lean
