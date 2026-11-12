import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.ValidU

/-! # Uniformity of the semantic operations

World-indexed forms of the three facts the fundamental theorem needs about uniform sections
(`FIRST_PRINCIPLES.md` §30.6, §30.7):

* `ValidAny.unif_const`: an element of a valid type is uniform, as a constant section;
* `dp_bound_mkPi`: a family of Π-types has bounded depth when its domains and fibres do;
* `unif_mkLam`: a family of abstractions is uniform when its bodies are uniform on uniform
  arguments;
* `unif_mkApp`: applying a uniform family of functions to a uniform family of arguments gives
  a uniform family, when the family of result types is tame.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
universe u
variable {𝕋 : UniverseTower.{u}}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem Unif.congr {m : Nat} {I : World.{u}} {H H' s : I → 𝕋.S}
    (hh : ∀ i, 𝕋.SameArgs (H i) (H' i)) (h : 𝕋.Unif m I H s) : 𝕋.Unif m I H' s := fun m' hm =>
  (h m' hm).imp fun b hb => Lf.congr b m' I H H' s hh hb

/-- A constant family at a valid type is tame. -/
theorem ValidAny.tame_const {n : Nat} {X : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList n) X) (m : Nat)
    (I : World.{u}) : 𝕋.Tame m (fun _ : I => X) := by
  refine ⟨⟨n, fun _ => H.lvLe⟩, fun m' _ => ?_⟩
  by_cases hl : 𝕋.LvLe m' X
  · obtain ⟨k, hk⟩ := H.exists_dpLe m' hl
    exact ⟨k, fun _ _ => hk⟩
  · exact ⟨0, fun _ h => (hl h).elim⟩

/-- **An element of a valid type is uniform**, as a constant section over any world. -/
theorem ValidAny.unif_const {n : Nat} {X : 𝕋.S} (H : 𝕋.ValidAny (𝕋.univList n) X) :
    ∀ {x : 𝕋.S} (I : World.{u}), x ∈ₛ 𝕋.El X → 𝕋.Unif 0 I (fun _ => X) (fun _ => x) := by
  induction H with
  | prop => exact fun I _ => unif_of_small (fun _ => .inl (.inl (kind_cand _))) _
  | tT => exact fun I _ => unif_of_small (fun _ => .inl (.inr (.inl kind_tT))) _
  | tProp => exact fun I _ => unif_of_small (fun _ => .inl (.inr (.inr kind_tProp))) _
  | univ hu =>
    obtain ⟨j, hj, rfl⟩ := mem_univList hu
    intro x I hx m _
    have hxv := (mem_El_univ.1 hx).2.1
    refine ⟨_, Lf_leaf (N := j + 1) (fun _ => .inr (kind_tU ..))
      (fun _ => .univ (kind_tU ..) (argsOf_univ j) (Nat.lt_succ_self j)) ?_⟩
    by_cases hl : 𝕋.LvLe m x
    · obtain ⟨k, hk⟩ := hxv.exists_dpLe m hl
      exact ⟨k, fun _ _ _ _ => hk⟩
    · exact ⟨0, fun _ _ _ h => (hl h).elim⟩
  | @pi D F _ _ _ _ _ _ _ _ _ =>
    intro x I hx
    obtain ⟨f, -, -, -, hu⟩ := mem_El_tPi.1 hx
    exact Unif.congr (fun _ => sameArgs_prePi D F) (hu.comp fun _ : I => PUnit.unit)
  | @piP c B hc hne hB hBc ih =>
    intro x I hx m _
    have hX := ValidAny.piP hc hne hB hBc
    have hT := hX.tame_const m I
    obtain ⟨b, hb⟩ := exists_famLe_of_tame hT
    refine ⟨b, Lf_iff.2 ⟨hT, hb, ⟨0, fun _ hk => ?_⟩, ?_, ?_⟩⟩
    · exact absurd (kind_unique (kind_tPiP ..) hk) (by decide)
    · intro _ _ I' φ a hk _ _ _ _
      exact Lf_of_isEmpty _ _
        (fun i' => absurd (kind_unique (kind_tPiP ..) (hk i').1) (by decide)) _ _
    · intro b' _ I' φ _ _ hF
      simp only [cod_tPiP] at hF ⊢
      obtain ⟨b'', h''⟩ := ih I' (ap_mem_of_mem_tPiP hx) m (Nat.zero_le m)
      exact h''.fuel hF

/-! ### The three forms of a Π-type -/

theorem El_of_isCand_nonempty {D : 𝕋.S} (hDc : 𝕋.IsCand D) (hne : ∃ v, (𝕋.candOf D).mem v) :
    𝕋.El D = 𝕋.one := by
  rw [isCand_eq hDc]; simp only [cand, El_rec5]; rw [if_pos hne]

/-- A Π-type is a proposition with propositions as fibres, a function type out of a non-empty
proposition, or a Π record. -/
theorem mkPi_cases (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) :
    (𝕋.IsCand (𝕋.mkPi D F) ∧ ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)) ∨
    (𝕋.mkPi D F = 𝕋.tPiP (𝕋.candOf D) (F 𝕋.star) ∧ 𝕋.IsCand D ∧
      (∃ v, (𝕋.candOf D).mem v) ∧ ¬ 𝕋.IsCand (F 𝕋.star)) ∨
    (𝕋.mkPi D F = 𝕋.tPi D F ∧ ¬ 𝕋.IsCand D ∧ ¬ ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)) := by
  unfold mkPi
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc]
    have hall : ∀ d, d ∈ₛ 𝕋.El D → d = 𝕋.star ∧ ∃ v, (𝕋.candOf D).mem v := fun d hd => by
      rw [isCand_eq hDc] at hd; exact 𝕋.mem_El_cand.1 hd
    by_cases hne : ∃ v, (𝕋.candOf D).mem v
    · rw [if_pos hne]
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc]
        exact .inl ⟨⟨_, rfl⟩, fun d hd => (hall d hd).1 ▸ hFc⟩
      · rw [if_neg hFc]
        exact .inr (.inl ⟨rfl, hDc, hne, hFc⟩)
    · rw [if_neg hne]
      exact .inl ⟨⟨_, rfl⟩, fun d hd => (hne (hall d hd).2).elim⟩
  · rw [if_neg hDc]
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall]; exact .inl ⟨⟨_, rfl⟩, hall⟩
    · rw [if_neg hall]; exact .inr (.inr ⟨rfl, hDc, hall⟩)

theorem isBase_of_isCand {X : 𝕋.S} (h : 𝕋.IsCand X) : 𝕋.IsBase X := by
  obtain ⟨c, rfl⟩ := h; exact .inl (kind_cand c)

theorem mkPi_of_kind4 {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} (hk : 𝕋.kind (𝕋.mkPi D F) = 𝕋.tagN 4) :
    𝕋.mkPi D F = 𝕋.tPi D F ∧ ¬ 𝕋.IsCand D ∧ ¬ ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d) := by
  rcases mkPi_cases D F with ⟨hc, -⟩ | ⟨e, -⟩ | h
  · exact (not_isBase_of_kind hk (by omega) (isBase_of_isCand hc)).elim
  · rw [e, kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  · exact h

theorem mkPi_of_kind5 {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} (hk : 𝕋.kind (𝕋.mkPi D F) = 𝕋.tagN 5) :
    𝕋.mkPi D F = 𝕋.tPiP (𝕋.candOf D) (F 𝕋.star) ∧ 𝕋.IsCand D ∧
      (∃ v, (𝕋.candOf D).mem v) ∧ ¬ 𝕋.IsCand (F 𝕋.star) := by
  rcases mkPi_cases D F with ⟨hc, -⟩ | h | ⟨e, -⟩
  · exact (not_isBase_of_kind hk (by omega) (isBase_of_isCand hc)).elim
  · exact h
  · rw [e, kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)

theorem kind_mkPi_ne3 (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) : 𝕋.kind (𝕋.mkPi D F) ≠ 𝕋.tagN 3 := by
  intro hk
  rcases mkPi_cases D F with ⟨hc, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact not_isBase_of_kind hk (by omega) (isBase_of_isCand hc)
  · rw [e, kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  · rw [e, kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)

/-- An abstraction with a data value somewhere is a function object. -/
theorem mkLam_eq_fn {D d₀ : 𝕋.S} {F f : 𝕋.S → 𝕋.S} (hd₀ : d₀ ∈ₛ 𝕋.El D)
    (hv : 𝕋.Valid (F d₀)) (hc : ¬ 𝕋.IsCand (F d₀)) (hf : f d₀ ∈ₛ 𝕋.El (F d₀)) :
    𝕋.mkLam D f = 𝕋.fn (𝕋.El D) f := by
  rw [mkLam, if_neg]
  intro h
  obtain ⟨n, hv⟩ := hv
  exact hv.star_not_mem hc (by rwa [h d₀ hd₀] at hf)

/-! ### Π formation -/

/-- **A family of Π-types has bounded depth when its domains and fibres do.** -/
theorem dp_bound_mkPi {m : Nat} {I : World.{u}} {D : I → 𝕋.S} {F : I → 𝕋.S → 𝕋.S}
    (hD : ∃ k, ∀ i, 𝕋.LvLe m (D i) → 𝕋.DpLe m (D i) k)
    (hF : ∃ k, ∀ i d, 𝕋.LvLe m (D i) → d ∈ₛ 𝕋.El (D i) → 𝕋.LvLe m (F i d) →
      𝕋.DpLe m (F i d) k) :
    ∃ k, ∀ i, 𝕋.LvLe m (𝕋.mkPi (D i) (F i)) → 𝕋.DpLe m (𝕋.mkPi (D i) (F i)) k := by
  obtain ⟨kD, hkD⟩ := hD
  obtain ⟨kF, hkF⟩ := hF
  refine ⟨max kD kF + 1, fun i hl => ?_⟩
  rcases mkPi_cases (D i) (F i) with ⟨hc, -⟩ | ⟨e, hDc, hne, -⟩ | ⟨e, -, -⟩
  · exact .small (.inl (isBase_of_isCand hc))
  · rw [e] at hl ⊢
    have hlB : 𝕋.LvLe m (F i 𝕋.star) := by
      have := hl.child (.inr ⟨kind_tPiP .., rfl⟩); simpa using this
    have hs : 𝕋.star ∈ₛ 𝕋.El (D i) := by
      rw [El_of_isCand_nonempty hDc hne]; exact 𝕋.mem_one.2 rfl
    refine .piP (kind_tPiP ..) ?_
    rw [cod_tPiP]
    exact (hkF i _ (.base (isBase_of_isCand hDc)) hs hlB).mono (Nat.le_max_right ..)
  · rw [e] at hl ⊢
    have hlD : 𝕋.LvLe m (D i) := by
      have := hl.child (.inl ⟨kind_tPi .., .inl rfl⟩); simpa using this
    refine .pi (kind_tPi ..) ?_ fun d hd => ?_
    · rw [dom_tPi]; exact (hkD i hlD).mono (Nat.le_max_left ..)
    · have hd' := hd; rw [dom_tPi] at hd'
      have hlF : 𝕋.LvLe m (F i d) := by
        have := hl.child (.inl ⟨kind_tPi .., .inr ⟨d, hd, rfl⟩⟩)
        rwa [fib_tPi hd'] at this
      rw [fib_tPi hd']
      exact (hkF i d hlD hd' hlF).mono (Nat.le_max_right ..)

/-! ### Abstraction -/

/-- **A family of abstractions is uniform when its bodies are uniform on uniform
arguments.** -/
theorem unif_mkLam {m : Nat} {I : World.{u}} {D : I → 𝕋.S} {F f : I → 𝕋.S → 𝕋.S}
    (hFv : ∀ i d, d ∈ₛ 𝕋.El (D i) → 𝕋.Valid (F i d))
    (hf : ∀ i d, d ∈ₛ 𝕋.El (D i) → f i d ∈ₛ 𝕋.El (F i d))
    (hT : 𝕋.Tame m (fun i => 𝕋.mkPi (D i) (F i)))
    (h : ∀ m', m ≤ m' → ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕋.S),
      (∀ i', a i' ∈ₛ 𝕋.El (D (φ i'))) → 𝕋.Unif m' I' (fun i' => D (φ i')) a →
      𝕋.Tame m' (fun i' => F (φ i') (a i')) →
      ∃ b, 𝕋.Lf b m' I' (fun i' => F (φ i') (a i')) (fun i' => f (φ i') (a i'))) :
    𝕋.Unif m I (fun i => 𝕋.mkPi (D i) (F i)) (fun i => 𝕋.mkLam (D i) (f i)) := by
  intro m' hm
  have hT' := hT.mono hm
  obtain ⟨b, hb⟩ := exists_famLe_of_tame hT'
  refine ⟨b, Lf_iff.2 ⟨hT', hb, ⟨0, fun i hk => (kind_mkPi_ne3 _ _ hk).elim⟩, ?_, ?_⟩⟩
  · intro b' _ I' φ a hk ha hG hTr hFr
    have e1 := fun i' => mkPi_of_kind4 (hk i').1
    have ha' : ∀ i', a i' ∈ₛ 𝕋.El (D (φ i')) := fun i' => by
      have := ha i'; rwa [(e1 i').1, dom_tPi] at this
    have eD : (fun i' => 𝕋.dom (𝕋.mkPi (D (φ i')) (F (φ i')))) = fun i' => D (φ i') :=
      funext fun i' => by rw [(e1 i').1, dom_tPi]
    have eF : (fun i' => 𝕋.fib (𝕋.mkPi (D (φ i')) (F (φ i'))) (a i')) =
        fun i' => F (φ i') (a i') := funext fun i' => by rw [(e1 i').1, fib_tPi (ha' i')]
    have eS : (fun i' => 𝕋.ap (𝕋.mkLam (D (φ i')) (f (φ i'))) (a i')) =
        fun i' => f (φ i') (a i') := funext fun i' => by
      obtain ⟨d₀, hd₀, hc₀⟩ : ∃ d₀, d₀ ∈ₛ 𝕋.El (D (φ i')) ∧ ¬ 𝕋.IsCand (F (φ i') d₀) :=
        Classical.byContradiction fun hn => (e1 i').2.2 fun d hd =>
          Classical.byContradiction fun hc => hn ⟨d, hd, hc⟩
      rw [mkLam_eq_fn hd₀ (hFv _ _ hd₀) hc₀ (hf _ _ hd₀), 𝕋.ap_fn (ha' i')]
    rw [eD] at hG
    rw [eF] at hTr hFr ⊢
    rw [eS]
    obtain ⟨b'', h''⟩ := h m' hm I' φ a ha' (fun m'' hm'' => ⟨b', hG m'' hm''⟩) hTr
    exact h''.fuel hFr
  · intro b' _ I' φ hk hTr hFr
    have e1 := fun i' => mkPi_of_kind5 (hk i').1
    have hs : ∀ i', 𝕋.star ∈ₛ 𝕋.El (D (φ i')) := fun i' => by
      rw [El_of_isCand_nonempty (e1 i').2.1 (e1 i').2.2.1]; exact 𝕋.mem_one.2 rfl
    have eF : (fun i' => 𝕋.cod (𝕋.mkPi (D (φ i')) (F (φ i')))) =
        fun i' => F (φ i') 𝕋.star := funext fun i' => by rw [(e1 i').1, cod_tPiP]
    have eS : (fun i' => 𝕋.ap (𝕋.mkLam (D (φ i')) (f (φ i'))) 𝕋.star) =
        fun i' => f (φ i') 𝕋.star := funext fun i' => by
      rw [mkLam_eq_fn (hs i') (hFv _ _ (hs i')) (e1 i').2.2.2 (hf _ _ (hs i')), 𝕋.ap_fn (hs i')]
    rw [eF] at hTr hFr ⊢
    rw [eS]
    obtain ⟨b'', h''⟩ := h m' hm I' φ (fun _ => 𝕋.star) hs
      (unif_of_small (fun i' => .inl (isBase_of_isCand (e1 i').2.1)) _) hTr
    exact h''.fuel hFr

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
