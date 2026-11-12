import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SemType

/-! # Bounding sets for the universes

The semantic universe of level `n` is cut out, by separation, from the set `bset base` of all
records obtained from the base types and the members of the lower universes by a finite
number of Π formations. This file builds that set from pairing, Π, separation, replacement
and union: `bk base k` is the set of records of Π-depth at most `k` over `base`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕋 : SetModel)

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The singleton `{a}`. -/
def single (a : 𝕋.S) : 𝕋.S := 𝕋.image (𝕋.set Unit) fun _ => a

/-- Binary union. -/
noncomputable def union2 (a b : 𝕋.S) : 𝕋.S :=
  𝕋.sUnion (𝕋.image (𝕋.set Bool) fun x => if x = 𝕋.enc true then a else b)

/-- Union of a sequence of sets. -/
noncomputable def iUnionNat (f : Nat → 𝕋.S) : 𝕋.S :=
  𝕋.sUnion (𝕋.image (𝕋.set Nat) fun x =>
    if h : ∃ n : Nat, x = 𝕋.enc n then f h.choose else 𝕋.emptySet)

/-- The set of all propositions. -/
noncomputable def candAll : 𝕋.S :=
  𝕋.image (𝕋.set Candidate) fun x =>
    if h : ∃ c : Candidate, x = 𝕋.enc c then 𝕋.cand h.choose else x

/-- The Π records with domain in `V` and fibres in `V`. -/
noncomputable def piSet (V : 𝕋.S) : 𝕋.S :=
  𝕋.sUnion (𝕋.image V fun D =>
    𝕋.image (𝕋.pi (𝕋.El D) fun _ => V) fun g => 𝕋.tPi D (𝕋.app g))

/-- The records of function types from a proposition into a member of `V`. -/
noncomputable def piPSet (V : 𝕋.S) : 𝕋.S :=
  𝕋.sUnion (𝕋.image (𝕋.set Candidate) fun x =>
    𝕋.image V fun B => if h : ∃ c : Candidate, x = 𝕋.enc c then 𝕋.tPiP h.choose B else B)

/-- Records of Π-depth at most `k` over `base`. -/
noncomputable def bk (base : 𝕋.S) : Nat → 𝕋.S
  | 0 => base
  | k + 1 => 𝕋.union2 (bk base k) (𝕋.union2 (𝕋.piSet (bk base k)) (𝕋.piPSet (bk base k)))

/-- Records of finite Π-depth over `base`. -/
noncomputable def bset (base : 𝕋.S) : 𝕋.S := 𝕋.iUnionNat (𝕋.bk base)

/-- The base of level `n`, given the lower universes: propositions, `T`, `Prop`, the lower
universes and their members. -/
noncomputable def baseOf : List 𝕋.S → 𝕋.S
  | [] => 𝕋.union2 𝕋.candAll (𝕋.union2 (𝕋.single 𝕋.tT) (𝕋.single 𝕋.tProp))
  | u :: l => 𝕋.union2 (baseOf l) (𝕋.union2 (𝕋.single u) (𝕋.El u))

variable {𝕋}

theorem mem_single {a x : 𝕋.S} : x ∈ₛ 𝕋.single a ↔ x = a := by
  rw [single, 𝕋.mem_image]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨𝕋.enc (), 𝕋.mem_set.2 ⟨(), rfl⟩, h⟩⟩

theorem mem_union2 {a b x : 𝕋.S} : x ∈ₛ 𝕋.union2 a b ↔ x ∈ₛ a ∨ x ∈ₛ b := by
  rw [union2, 𝕋.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨z, -, rfl⟩ := 𝕋.mem_image.1 hy
    split at hx
    · exact .inl hx
    · exact .inr hx
  · rintro (h | h)
    · exact ⟨a, 𝕋.mem_image.2 ⟨𝕋.enc true, 𝕋.mem_set.2 ⟨true, rfl⟩, by simp⟩, h⟩
    · refine ⟨b, 𝕋.mem_image.2 ⟨𝕋.enc false, 𝕋.mem_set.2 ⟨false, rfl⟩, ?_⟩, h⟩
      rw [if_neg]; intro e; exact absurd (𝕋.enc_inj e) (by decide)

theorem mem_iUnionNat {f : Nat → 𝕋.S} {x : 𝕋.S} : x ∈ₛ 𝕋.iUnionNat f ↔ ∃ n, x ∈ₛ f n := by
  rw [iUnionNat, 𝕋.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨z, hz, rfl⟩ := 𝕋.mem_image.1 hy
    obtain ⟨n, rfl⟩ := 𝕋.mem_set.1 hz
    have h : ∃ n' : Nat, 𝕋.enc n = 𝕋.enc n' := ⟨n, rfl⟩
    rw [dif_pos h] at hx
    exact ⟨_, hx⟩
  · rintro ⟨n, hx⟩
    refine ⟨f n, 𝕋.mem_image.2 ⟨𝕋.enc n, 𝕋.mem_set.2 ⟨n, rfl⟩, ?_⟩, hx⟩
    have h : ∃ n' : Nat, 𝕋.enc n = 𝕋.enc n' := ⟨n, rfl⟩
    rw [dif_pos h, ← 𝕋.enc_inj h.choose_spec]

theorem cand_mem_candAll (c : Candidate) : 𝕋.cand c ∈ₛ 𝕋.candAll := by
  refine 𝕋.mem_image.2 ⟨𝕋.enc c, 𝕋.mem_set.2 ⟨c, rfl⟩, ?_⟩
  have h : ∃ c' : Candidate, 𝕋.enc c = 𝕋.enc c' := ⟨c, rfl⟩
  rw [dif_pos h, ← 𝕋.enc_inj h.choose_spec]

theorem tPi_mem_piSet {V D : 𝕋.S} {g : 𝕋.S} (hD : D ∈ₛ V)
    (hg : g ∈ₛ 𝕋.pi (𝕋.El D) fun _ => V) : 𝕋.tPi D (𝕋.app g) ∈ₛ 𝕋.piSet V :=
  𝕋.mem_sUnion.2 ⟨_, 𝕋.mem_image.2 ⟨D, hD, rfl⟩, 𝕋.mem_image.2 ⟨g, hg, rfl⟩⟩

theorem tPiP_mem_piPSet {V B : 𝕋.S} (c : Candidate) (hB : B ∈ₛ V) :
    𝕋.tPiP c B ∈ₛ 𝕋.piPSet V := by
  refine 𝕋.mem_sUnion.2 ⟨_, 𝕋.mem_image.2 ⟨𝕋.enc c, 𝕋.mem_set.2 ⟨c, rfl⟩, rfl⟩,
    𝕋.mem_image.2 ⟨B, hB, ?_⟩⟩
  have h : ∃ c' : Candidate, 𝕋.enc c = 𝕋.enc c' := ⟨c, rfl⟩
  rw [dif_pos h, ← 𝕋.enc_inj h.choose_spec]

theorem bk_mono {base : 𝕋.S} {k k' : Nat} (h : k ≤ k') {x : 𝕋.S} (hx : x ∈ₛ 𝕋.bk base k) :
    x ∈ₛ 𝕋.bk base k' := by
  induction h with
  | refl => exact hx
  | step _ ih => exact mem_union2.2 (.inl ih)

theorem mem_bset {base x : 𝕋.S} : x ∈ₛ 𝕋.bset base ↔ ∃ k, x ∈ₛ 𝕋.bk base k := mem_iUnionNat

theorem mem_baseOf {l : List 𝕋.S} {x : 𝕋.S} :
    x ∈ₛ 𝕋.baseOf l ↔ (∃ c, x = 𝕋.cand c) ∨ x = 𝕋.tT ∨ x = 𝕋.tProp ∨
      ∃ u, u ∈ l ∧ (x = u ∨ x ∈ₛ 𝕋.El u) := by
  induction l with
  | nil =>
    simp only [baseOf, mem_union2, mem_single, List.not_mem_nil, false_and, exists_false,
      or_false]
    refine or_congr_left ⟨fun h => ?_, fun ⟨c, e⟩ => e ▸ cand_mem_candAll c⟩
    obtain ⟨z, hz, rfl⟩ := 𝕋.mem_image.1 h
    obtain ⟨c, rfl⟩ := 𝕋.mem_set.1 hz
    have h : ∃ c' : Candidate, 𝕋.enc c = 𝕋.enc c' := ⟨c, rfl⟩
    exact ⟨_, by rw [dif_pos h]⟩
  | cons u l ih =>
    simp only [baseOf, mem_union2, mem_single, ih, List.mem_cons]
    constructor
    · rintro ((h | h | h | ⟨v, hv, h⟩) | h | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr ⟨v, .inr hv, h⟩))
      · exact .inr (.inr (.inr ⟨u, .inl rfl, .inl h⟩))
      · exact .inr (.inr (.inr ⟨u, .inl rfl, .inr h⟩))
    · rintro (h | h | h | ⟨v, rfl | hv, h⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr (.inl h))
      · exact .inl (.inr (.inr (.inl h)))
      · exact .inr h
      · exact .inl (.inr (.inr (.inr ⟨v, hv, h⟩)))

end SetModel

end VEnv.Strengthening
end Lean4Lean
