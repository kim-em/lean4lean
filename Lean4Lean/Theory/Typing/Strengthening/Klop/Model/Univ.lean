import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.SemLemmas

/-! # Universe membership

`Prop` and `𝒰ₙ` are elements of the next semantic universe, because they are in the base of
its bounding set, and sorts are related to themselves.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

theorem univ_mem_univList (n : Nat) : 𝕊.univ n ∈ 𝕊.univList (n + 1) := by
  simp [univList, univ]

theorem univList_mono {m n : Nat} (h : m ≤ n) {u : 𝕊.S} (hu : u ∈ 𝕊.univList m) :
    u ∈ 𝕊.univList n := by
  induction h with
  | refl => exact hu
  | step _ ih => simp only [univList, List.mem_append]; exact .inl ih

theorem not_isCand_of_kind {x : 𝕊.S} {k : Nat} (h : 𝕊.kind x = 𝕊.tagN k) (hk : k ≠ 0) :
    ¬ 𝕊.IsCand x := by
  rintro ⟨c, rfl⟩
  rw [kind_cand] at h
  exact hk (𝕊.tagN_inj h).symm

theorem not_isCand_tProp : ¬ 𝕊.IsCand 𝕊.tProp := not_isCand_of_kind kind_tProp (by decide)
theorem not_isCand_univ (n : Nat) : ¬ 𝕊.IsCand (𝕊.univ n) :=
  not_isCand_of_kind (kind_tU ..) (by decide)
theorem not_isCand_tT : ¬ 𝕊.IsCand 𝕊.tT := not_isCand_of_kind kind_tT (by decide)

theorem mem_bset_of_base {base x : 𝕊.S} (h : x ∈ₛ base) : x ∈ₛ 𝕊.bset base :=
  mem_bset.2 ⟨0, h⟩

/-- `Prop` is an element of the first universe. -/
theorem tProp_mem_univ : 𝕊.tProp ∈ₛ 𝕊.El (𝕊.univ 0) :=
  mem_El_univ.2 ⟨mem_bset_of_base (mem_baseOf.2 (.inr (.inr (.inl rfl)))), .tProp,
    fun h => (not_isCand_tProp h).elim⟩

/-- `𝒰ₙ` is an element of `𝒰ₙ₊₁`. -/
theorem univ_mem_univ (n : Nat) : 𝕊.univ n ∈ₛ 𝕊.El (𝕊.univ (n + 1)) :=
  mem_El_univ.2 ⟨mem_bset_of_base (mem_baseOf.2
      (.inr (.inr (.inr ⟨_, univ_mem_univList n, .inl rfl⟩)))),
    .univ (univ_mem_univList n), fun h => (not_isCand_univ n h).elim⟩

/-- Elements of a universe are coarsely related to themselves. -/
theorem rel_univ_refl {n : Nat} {x : 𝕊.S} (hx : x ∈ₛ 𝕊.El (𝕊.univ n)) : 𝕊.Rel (𝕊.univ n) x x := by
  have hx' : x ∈ₛ 𝕊.sep (𝕊.bset (𝕊.baseOf (𝕊.univList n))) (𝕊.ValidTy (𝕊.univList n)) := by
    simpa [univ, tU] using hx
  rw [Rel]
  simp only [univ, tU, relOf_rec5]
  exact (𝕊.mem_relFn hx').2 ⟨hx', rfl⟩

theorem sortDen_congr {l l' : VLevel} (h : l ≈ l') : 𝕊.sortDen l = 𝕊.sortDen l' := by
  simp only [sortDen, VLevel.equiv_def.1 h []]

theorem sortDen_succ (l : VLevel) : 𝕊.sortDen (.succ l) = 𝕊.univ (l.eval []) := rfl

/-- `⟦Sort ℓ⟧` is an element of `⟦Sort (ℓ + 1)⟧`. -/
theorem sortDen_mem (l : VLevel) : 𝕊.sortDen l ∈ₛ 𝕊.El (𝕊.sortDen (.succ l)) := by
  rw [sortDen_succ]
  unfold sortDen
  cases l.eval [] with
  | zero => exact tProp_mem_univ
  | succ n => exact univ_mem_univ n

end SetModel
end VEnv.Strengthening
end Lean4Lean
