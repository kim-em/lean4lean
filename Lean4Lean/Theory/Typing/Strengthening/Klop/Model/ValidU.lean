import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.PiCongr

/-! # Valid types are members of their universe

`ValidAny.mem_univ`: a valid data type of level `n` is an element of `𝒰ₙ`. The universe is cut
out of the set of records of finite Π-depth over the lower universes, so this needs a bound on
the depth of a valid type (`ValidAny.exists_dpLe`). The bound for a Π-type comes from the
uniformity of its family of fibres, applied to the section of all elements of the domain,
which is uniform because the domain has bounded depth (`unif_full`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
universe u
variable {𝕊 : SetModel.{u}}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- Validity is monotone in the list of lower universes. -/
theorem ValidAny.mono_list {l l' : List 𝕊.S} (h : ∀ u, u ∈ l → u ∈ l') {x : 𝕊.S}
    (H : 𝕊.ValidAny l x) : 𝕊.ValidAny l' x := by
  induction H with
  | prop hc => exact .prop hc
  | tT => exact .tT
  | tProp => exact .tProp
  | univ hu => exact .univ (h _ hu)
  | pi _ hDc _ hfull hrel hmix hfam ihD ihF => exact .pi ihD hDc ihF hfull hrel hmix hfam
  | piP hc hne _ hBc ih => exact .piP hc hne ih hBc

/-- Validity is monotone in the level. -/
theorem ValidAny.mono {m n : Nat} (h : m ≤ n) {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList m) x) :
    𝕊.ValidAny (𝕊.univList n) x :=
  H.mono_list fun _ hu => univList_mono h hu

/-- A valid semantic type of some level. -/
def Valid (𝕊 : SetModel.{u}) (x : 𝕊.S) : Prop := ∃ n, 𝕊.ValidAny (𝕊.univList n) x

theorem univ_mem_univList_of_lt {m n : Nat} (h : m < n) : 𝕊.univ m ∈ 𝕊.univList n :=
  univList_mono h (univ_mem_univList m)

/-- A valid type of level `n` mentions only universes below `n`. -/
theorem ValidAny.lvLe {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x) : 𝕊.LvLe n x := by
  induction H with
  | prop => exact .base (.inl (kind_cand _))
  | tT => exact .base (.inr (.inl kind_tT))
  | tProp => exact .base (.inr (.inr kind_tProp))
  | univ hu =>
    obtain ⟨m, hm, rfl⟩ := mem_univList hu
    exact .univ (kind_tU ..) (argsOf_univ m) hm
  | pi _ _ _ _ _ _ _ ihD ihF =>
    exact .pi (kind_tPi ..) (by simpa using ihD) fun d hd => by
      have hd' := hd; rw [dom_tPi] at hd'
      rw [fib_tPi hd']; exact ihF d hd'
  | piP _ _ _ _ ih => exact .piP (kind_tPiP ..) (by simpa using ih)

/-- The domain, fibres and codomain of a valid function type are valid. -/
theorem Valid.child {X Y : 𝕊.S} (H : 𝕊.Valid X) (hc : 𝕊.Child X Y) : 𝕊.Valid Y := by
  obtain ⟨n, H⟩ := H
  cases H with
  | prop => exact (hc.not_isBase (.inl (kind_cand _))).elim
  | tT => exact (hc.not_isBase (.inr (.inl kind_tT))).elim
  | tProp => exact (hc.not_isBase (.inr (.inr kind_tProp))).elim
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    rcases hc with ⟨hk, -⟩ | ⟨hk, -⟩ <;>
      exact absurd (kind_unique (kind_tU ..) hk) (by decide)
  | pi hD _ hF =>
    rcases hc with ⟨-, h | ⟨d, hd, h⟩⟩ | ⟨hk, -⟩
    · rw [h, dom_tPi]; exact ⟨n, hD⟩
    · have hd' := hd; rw [dom_tPi] at hd'
      rw [h, fib_tPi hd']; exact ⟨n, hF d hd'⟩
    · exact absurd (kind_unique (kind_tPi ..) hk) (by decide)
  | piP _ _ hB =>
    rcases hc with ⟨hk, -⟩ | ⟨-, h⟩
    · exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)
    · rw [h, cod_tPiP]; exact ⟨n, hB⟩

/-- The elements of a valid universe `𝒰ⱼ` mention only universes below `j`. -/
theorem Valid.lvLe_of_mem {X x : 𝕊.S} {j : Nat} (H : 𝕊.Valid X) (hk : 𝕊.kind X = 𝕊.tagN 3)
    (ha : 𝕊.argsOf X = 𝕊.enc j) (hx : x ∈ₛ 𝕊.El X) : 𝕊.LvLe j x := by
  obtain ⟨n, H⟩ := H
  cases H with
  | prop => exact absurd (kind_unique (kind_cand _) hk) (by decide)
  | tT => exact absurd (kind_unique kind_tT hk) (by decide)
  | tProp => exact absurd (kind_unique kind_tProp hk) (by decide)
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    rw [argsOf_univ] at ha
    cases 𝕊.enc_inj ha
    exact (mem_El_univ.1 hx).2.1.lvLe
  | pi => exact absurd (kind_unique (kind_tPi ..) hk) (by decide)
  | piP => exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)

theorem Valid.ap_mem {X f d : 𝕊.S} (H : 𝕊.Valid X) (hk : 𝕊.kind X = 𝕊.tagN 4)
    (hf : f ∈ₛ 𝕊.El X) (hd : d ∈ₛ 𝕊.El (𝕊.dom X)) : 𝕊.ap f d ∈ₛ 𝕊.El (𝕊.fib X d) := by
  obtain ⟨n, H⟩ := H
  cases H with
  | prop => exact absurd (kind_unique (kind_cand _) hk) (by decide)
  | tT => exact absurd (kind_unique kind_tT hk) (by decide)
  | tProp => exact absurd (kind_unique kind_tProp hk) (by decide)
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    exact absurd (kind_unique (kind_tU ..) hk) (by decide)
  | pi =>
    have hd' := hd; rw [dom_tPi] at hd'
    rw [fib_tPi hd']; exact ap_mem_of_mem_tPi hf hd'
  | piP => exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)

theorem Valid.ap_mem_piP {X f : 𝕊.S} (H : 𝕊.Valid X) (hk : 𝕊.kind X = 𝕊.tagN 5)
    (hf : f ∈ₛ 𝕊.El X) : 𝕊.ap f 𝕊.star ∈ₛ 𝕊.El (𝕊.cod X) := by
  obtain ⟨n, H⟩ := H
  cases H with
  | prop => exact absurd (kind_unique (kind_cand _) hk) (by decide)
  | tT => exact absurd (kind_unique kind_tT hk) (by decide)
  | tProp => exact absurd (kind_unique kind_tProp hk) (by decide)
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    exact absurd (kind_unique (kind_tU ..) hk) (by decide)
  | pi => exact absurd (kind_unique (kind_tPi ..) hk) (by decide)
  | piP => rw [cod_tPiP]; exact ap_mem_of_mem_tPiP hf

/-- **Every section of a family of valid types of level `m` and bounded depth is uniform from
level `m` on**. -/
theorem unif_full {m k : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (h : ∀ i, 𝕊.Valid (H i) ∧ 𝕊.LvLe m (H i) ∧ 𝕊.DpLe m (H i) k ∧ s i ∈ₛ 𝕊.El (H i)) :
    𝕊.Unif m I H s := by
  intro m' hm
  rcases Nat.lt_or_ge m m' with hlt | hge
  · exact ⟨(0, 0), Lf_of_small _ (fun i => (h i).2.1.small.mono hlt) _⟩
  · obtain rfl : m = m' := Nat.le_antisymm hm hge
    exact ⟨(m, k), Lf_full 𝕊.Valid (fun _ _ => Valid.child)
      (fun _ _ _ hX hk ha hx => hX.lvLe_of_mem hk ha hx)
      (fun _ _ _ hX hk hf hd => hX.ap_mem hk hf hd)
      (fun _ _ hX hk hf => hX.ap_mem_piP hk hf) m k I H s h⟩

/-- **A valid type has finite depth at every level that bounds it.** -/
theorem ValidAny.exists_dpLe {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x) :
    ∀ m, 𝕊.LvLe m x → ∃ k, 𝕊.DpLe m x k := by
  induction H with
  | prop => exact fun m _ => ⟨0, .small (.inl (.inl (kind_cand _)))⟩
  | tT => exact fun m _ => ⟨0, .small (.inl (.inr (.inl kind_tT)))⟩
  | tProp => exact fun m _ => ⟨0, .small (.inl (.inr (.inr kind_tProp)))⟩
  | univ hu =>
    obtain ⟨j, -, rfl⟩ := mem_univList hu
    exact fun m _ => ⟨0, .univ (kind_tU ..)⟩
  | @pi D F hD _ hF _ _ _ hfam ihD ihF =>
    intro m hl
    have hlD : 𝕊.LvLe m D := by
      have := hl.child (.inl ⟨kind_tPi .., .inl rfl⟩); simpa using this
    have hlF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.LvLe m (F d) := fun d hd => by
      have := hl.child (.inl ⟨kind_tPi .., .inr ⟨d, by simpa using hd, rfl⟩⟩)
      rwa [fib_tPi hd] at this
    obtain ⟨kD, hkD⟩ := ihD m hlD
    obtain ⟨kF, hkF⟩ := hfam m {d // d ∈ₛ 𝕊.El D} (fun d => d.1) (fun d => d.2)
      (unif_full fun d => ⟨⟨n, hD⟩, hlD, hkD, d.2⟩)
    refine ⟨max kD kF + 1, .pi (kind_tPi ..) ?_ fun d hd => ?_⟩
    · rw [dom_tPi]; exact hkD.mono (Nat.le_max_left ..)
    · have hd' : d ∈ₛ 𝕊.El D := by simpa using hd
      rw [fib_tPi hd']
      exact (hkF ⟨d, hd'⟩ (hlF d hd')).mono (Nat.le_max_right ..)
  | @piP c B _ _ _ _ ih =>
    intro m hl
    have hlB : 𝕊.LvLe m B := by
      have := hl.child (.inr ⟨kind_tPiP .., rfl⟩); simpa using this
    obtain ⟨k, hk⟩ := ih m hlB
    exact ⟨k + 1, .piP (kind_tPiP ..) (by simpa using hk)⟩

/-- A valid type that mentions only universes below `n'` is valid at level `n'`. -/
theorem ValidAny.restrict {n n' : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x)
    (hl : 𝕊.LvLe n' x) : 𝕊.ValidAny (𝕊.univList n') x := by
  induction H with
  | prop hc => exact .prop hc
  | tT => exact .tT
  | tProp => exact .tProp
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    cases hl with
    | base hb => exact (not_isBase_of_kind (kind_tU ..) (by omega) hb).elim
    | univ _ ha hj =>
      rw [argsOf_univ] at ha
      cases 𝕊.enc_inj ha
      exact .univ (univ_mem_univList_of_lt hj)
    | pi hk => exact absurd (kind_unique (kind_tU ..) hk) (by decide)
    | piP hk => exact absurd (kind_unique (kind_tU ..) hk) (by decide)
  | @pi D F _ hDc _ hfull hrel hmix hfam ihD ihF =>
    have hlD : 𝕊.LvLe n' D := by
      have := hl.child (.inl ⟨kind_tPi .., .inl rfl⟩); simpa using this
    have hlF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.LvLe n' (F d) := fun d hd => by
      have := hl.child (.inl ⟨kind_tPi .., .inr ⟨d, by simpa using hd, rfl⟩⟩)
      rwa [fib_tPi hd] at this
    exact .pi (ihD hlD) hDc (fun d hd => ihF d hd (hlF d hd)) hfull hrel hmix hfam
  | @piP c B hc hne _ hBc ih =>
    have hlB : 𝕊.LvLe n' B := by
      have := hl.child (.inr ⟨kind_tPiP .., rfl⟩); simpa using this
    exact .piP hc hne (ih hlB) hBc

theorem not_isCand_tPi (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : ¬ 𝕊.IsCand (𝕊.tPi D F) :=
  not_isCand_of_kind (kind_tPi ..) (by decide)
theorem not_isCand_tPiP (c : Candidate) (B : 𝕊.S) : ¬ 𝕊.IsCand (𝕊.tPiP c B) :=
  not_isCand_of_kind (kind_tPiP ..) (by decide)

/-- **A valid type of level `n` is a record of finite depth over the lower universes.** -/
theorem ValidAny.mem_bset : ∀ (n : Nat) {x : 𝕊.S}, 𝕊.ValidAny (𝕊.univList n) x →
    x ∈ₛ 𝕊.bset (𝕊.baseOf (𝕊.univList n)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    -- a small valid data type is a member of a lower universe, hence in the base
    have small_mem : ∀ {x : 𝕊.S}, 𝕊.ValidAny (𝕊.univList n) x → ¬ 𝕊.IsCand x →
        ¬ 𝕊.IsBase x → 𝕊.Small n x → x ∈ₛ 𝕊.baseOf (𝕊.univList n) := by
      intro x hx hxc hxb hs
      rcases hs with hb | ⟨n', rfl, hl⟩
      · exact (hxb hb).elim
      · have hx' := hx.restrict hl
        have hmem : x ∈ₛ 𝕊.El (𝕊.univ n') :=
          mem_El_univ.2 ⟨IH n' (Nat.lt_succ_self n') hx', hx', fun h => (hxc h).elim⟩
        exact mem_baseOf.2 (.inr (.inr (.inr ⟨_, univ_mem_univList n', .inr hmem⟩)))
    have corr : ∀ {x : 𝕊.S}, 𝕊.ValidAny (𝕊.univList n) x → ∀ k, 𝕊.DpLe n x k →
        x ∈ₛ 𝕊.bk (𝕊.baseOf (𝕊.univList n)) k := by
      intro x hx
      induction hx with
      | prop => exact fun k _ => bk_mono (Nat.zero_le k) (mem_baseOf.2 (.inl ⟨_, rfl⟩))
      | tT => exact fun k _ => bk_mono (Nat.zero_le k) (mem_baseOf.2 (.inr (.inl rfl)))
      | tProp => exact fun k _ => bk_mono (Nat.zero_le k) (mem_baseOf.2 (.inr (.inr (.inl rfl))))
      | univ hu =>
        exact fun k _ => bk_mono (Nat.zero_le k)
          (mem_baseOf.2 (.inr (.inr (.inr ⟨_, hu, .inl rfl⟩))))
      | @pi D F hD hDc hF hfull hrel hmix hfam ihD ihF =>
        intro k hd
        have hX := ValidAny.pi hD hDc hF hfull hrel hmix hfam
        cases hd with
        | small hs =>
          exact bk_mono (Nat.zero_le _) (small_mem hX (not_isCand_tPi D F)
            (not_isBase_of_kind (kind_tPi ..) (by omega)) hs)
        | univ hk => exact absurd (kind_unique (kind_tPi ..) hk) (by decide)
        | @pi _ k' _ hdD hdF =>
          have h1 : D ∈ₛ 𝕊.bk (𝕊.baseOf (𝕊.univList n)) k' := ihD k' (by simpa using hdD)
          have h2 : ∀ d, d ∈ₛ 𝕊.El D → F d ∈ₛ 𝕊.bk (𝕊.baseOf (𝕊.univList n)) k' :=
            fun d hd => ihF d hd k' (by have := hdF d (by simpa using hd); rwa [fib_tPi hd] at this)
          have e : 𝕊.tPi D F = 𝕊.tPi D (𝕊.app (𝕊.lam (𝕊.El D) F)) :=
            tPi_congr fun d hd => (𝕊.app_lam hd).symm
          rw [e]
          exact mem_union2.2 (.inr (mem_union2.2 (.inl (tPi_mem_piSet h1 (lam_mem_pi h2)))))
        | piP hk => exact absurd (kind_unique (kind_tPi ..) hk) (by decide)
      | @piP c B hc hne hB hBc ih =>
        intro k hd
        have hX := ValidAny.piP hc hne hB hBc
        cases hd with
        | small hs =>
          exact bk_mono (Nat.zero_le _) (small_mem hX (not_isCand_tPiP c B)
            (not_isBase_of_kind (kind_tPiP ..) (by omega)) hs)
        | univ hk => exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)
        | pi hk => exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)
        | @piP _ k' _ hdB =>
          have h1 : B ∈ₛ 𝕊.bk (𝕊.baseOf (𝕊.univList n)) k' := ih k' (by simpa using hdB)
          exact mem_union2.2 (.inr (mem_union2.2 (.inr (tPiP_mem_piPSet c h1))))
    intro x hx
    obtain ⟨k, hk⟩ := hx.exists_dpLe n hx.lvLe
    exact SetModel.mem_bset.2 ⟨k, corr hx k hk⟩

/-- A valid data type of level `n` (or the full candidate) is an element of `𝒰ₙ`. -/
theorem ValidAny.mem_univ {n : Nat} {x : 𝕊.S} (H : 𝕊.ValidAny (𝕊.univList n) x)
    (hc : 𝕊.IsCand x → x = 𝕊.cand Candidate.full) : x ∈ₛ 𝕊.El (𝕊.univ n) :=
  mem_El_univ.2 ⟨H.mem_bset n, H, hc⟩

end SetModel
end VEnv.Strengthening
end Lean4Lean
