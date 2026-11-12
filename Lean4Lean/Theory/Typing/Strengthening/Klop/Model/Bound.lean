import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.SemType

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
variable (𝕊 : SetModel)

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The singleton `{a}`. -/
def single (a : 𝕊.S) : 𝕊.S := 𝕊.image (𝕊.set Unit) fun _ => a

/-- Binary union. -/
noncomputable def union2 (a b : 𝕊.S) : 𝕊.S :=
  𝕊.sUnion (𝕊.image (𝕊.set Bool) fun x => if x = 𝕊.enc true then a else b)

/-- Union of a sequence of sets. -/
noncomputable def iUnionNat (f : Nat → 𝕊.S) : 𝕊.S :=
  𝕊.sUnion (𝕊.image (𝕊.set Nat) fun x =>
    if h : ∃ n : Nat, x = 𝕊.enc n then f h.choose else 𝕊.emptySet)

/-- The set of all propositions. -/
noncomputable def candAll : 𝕊.S :=
  𝕊.image (𝕊.set Candidate) fun x =>
    if h : ∃ c : Candidate, x = 𝕊.enc c then 𝕊.cand h.choose else x

/-- The Π records with domain in `V` and fibres in `V`. -/
noncomputable def piSet (V : 𝕊.S) : 𝕊.S :=
  𝕊.sUnion (𝕊.image V fun D =>
    𝕊.image (𝕊.pi (𝕊.El D) fun _ => V) fun g => 𝕊.tPi D (𝕊.app g))

/-- The records of function types from a proposition into a member of `V`. -/
noncomputable def piPSet (V : 𝕊.S) : 𝕊.S :=
  𝕊.sUnion (𝕊.image (𝕊.set Candidate) fun x =>
    𝕊.image V fun B => if h : ∃ c : Candidate, x = 𝕊.enc c then 𝕊.tPiP h.choose B else B)

/-- Records of Π-depth at most `k` over `base`. -/
noncomputable def bk (base : 𝕊.S) : Nat → 𝕊.S
  | 0 => base
  | k + 1 => 𝕊.union2 (bk base k) (𝕊.union2 (𝕊.piSet (bk base k)) (𝕊.piPSet (bk base k)))

/-- Records of finite Π-depth over `base`. -/
noncomputable def bset (base : 𝕊.S) : 𝕊.S := 𝕊.iUnionNat (𝕊.bk base)

/-- The base of level `n`, given the lower universes: propositions, `T`, `Prop`, the lower
universes and their members. -/
noncomputable def baseOf : List 𝕊.S → 𝕊.S
  | [] => 𝕊.union2 𝕊.candAll (𝕊.union2 (𝕊.single 𝕊.tT) (𝕊.single 𝕊.tProp))
  | u :: l => 𝕊.union2 (baseOf l) (𝕊.union2 (𝕊.single u) (𝕊.El u))

variable {𝕊}

theorem mem_single {a x : 𝕊.S} : x ∈ₛ 𝕊.single a ↔ x = a := by
  rw [single, 𝕊.mem_image]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨𝕊.enc (), 𝕊.mem_set.2 ⟨(), rfl⟩, h⟩⟩

theorem mem_union2 {a b x : 𝕊.S} : x ∈ₛ 𝕊.union2 a b ↔ x ∈ₛ a ∨ x ∈ₛ b := by
  rw [union2, 𝕊.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨z, -, rfl⟩ := 𝕊.mem_image.1 hy
    split at hx
    · exact .inl hx
    · exact .inr hx
  · rintro (h | h)
    · exact ⟨a, 𝕊.mem_image.2 ⟨𝕊.enc true, 𝕊.mem_set.2 ⟨true, rfl⟩, by simp⟩, h⟩
    · refine ⟨b, 𝕊.mem_image.2 ⟨𝕊.enc false, 𝕊.mem_set.2 ⟨false, rfl⟩, ?_⟩, h⟩
      rw [if_neg]; intro e; exact absurd (𝕊.enc_inj e) (by decide)

theorem mem_iUnionNat {f : Nat → 𝕊.S} {x : 𝕊.S} : x ∈ₛ 𝕊.iUnionNat f ↔ ∃ n, x ∈ₛ f n := by
  rw [iUnionNat, 𝕊.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨z, hz, rfl⟩ := 𝕊.mem_image.1 hy
    obtain ⟨n, rfl⟩ := 𝕊.mem_set.1 hz
    have h : ∃ n' : Nat, 𝕊.enc n = 𝕊.enc n' := ⟨n, rfl⟩
    rw [dif_pos h] at hx
    exact ⟨_, hx⟩
  · rintro ⟨n, hx⟩
    refine ⟨f n, 𝕊.mem_image.2 ⟨𝕊.enc n, 𝕊.mem_set.2 ⟨n, rfl⟩, ?_⟩, hx⟩
    have h : ∃ n' : Nat, 𝕊.enc n = 𝕊.enc n' := ⟨n, rfl⟩
    rw [dif_pos h, ← 𝕊.enc_inj h.choose_spec]

theorem cand_mem_candAll (c : Candidate) : 𝕊.cand c ∈ₛ 𝕊.candAll := by
  refine 𝕊.mem_image.2 ⟨𝕊.enc c, 𝕊.mem_set.2 ⟨c, rfl⟩, ?_⟩
  have h : ∃ c' : Candidate, 𝕊.enc c = 𝕊.enc c' := ⟨c, rfl⟩
  rw [dif_pos h, ← 𝕊.enc_inj h.choose_spec]

theorem tPi_mem_piSet {V D : 𝕊.S} {g : 𝕊.S} (hD : D ∈ₛ V)
    (hg : g ∈ₛ 𝕊.pi (𝕊.El D) fun _ => V) : 𝕊.tPi D (𝕊.app g) ∈ₛ 𝕊.piSet V :=
  𝕊.mem_sUnion.2 ⟨_, 𝕊.mem_image.2 ⟨D, hD, rfl⟩, 𝕊.mem_image.2 ⟨g, hg, rfl⟩⟩

theorem tPiP_mem_piPSet {V B : 𝕊.S} (c : Candidate) (hB : B ∈ₛ V) :
    𝕊.tPiP c B ∈ₛ 𝕊.piPSet V := by
  refine 𝕊.mem_sUnion.2 ⟨_, 𝕊.mem_image.2 ⟨𝕊.enc c, 𝕊.mem_set.2 ⟨c, rfl⟩, rfl⟩,
    𝕊.mem_image.2 ⟨B, hB, ?_⟩⟩
  have h : ∃ c' : Candidate, 𝕊.enc c = 𝕊.enc c' := ⟨c, rfl⟩
  rw [dif_pos h, ← 𝕊.enc_inj h.choose_spec]

theorem bk_mono {base : 𝕊.S} {k k' : Nat} (h : k ≤ k') {x : 𝕊.S} (hx : x ∈ₛ 𝕊.bk base k) :
    x ∈ₛ 𝕊.bk base k' := by
  induction h with
  | refl => exact hx
  | step _ ih => exact mem_union2.2 (.inl ih)

theorem mem_bset {base x : 𝕊.S} : x ∈ₛ 𝕊.bset base ↔ ∃ k, x ∈ₛ 𝕊.bk base k := mem_iUnionNat

theorem mem_baseOf {l : List 𝕊.S} {x : 𝕊.S} :
    x ∈ₛ 𝕊.baseOf l ↔ (∃ c, x = 𝕊.cand c) ∨ x = 𝕊.tT ∨ x = 𝕊.tProp ∨
      ∃ u, u ∈ l ∧ (x = u ∨ x ∈ₛ 𝕊.El u) := by
  induction l with
  | nil =>
    simp only [baseOf, mem_union2, mem_single, List.not_mem_nil, false_and, exists_false,
      or_false]
    refine or_congr_left ⟨fun h => ?_, fun ⟨c, e⟩ => e ▸ cand_mem_candAll c⟩
    obtain ⟨z, hz, rfl⟩ := 𝕊.mem_image.1 h
    obtain ⟨c, rfl⟩ := 𝕊.mem_set.1 hz
    have h : ∃ c' : Candidate, 𝕊.enc c = 𝕊.enc c' := ⟨c, rfl⟩
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
