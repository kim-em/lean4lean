import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.ValidU

/-! # Π formation depends only on the fibres over the domain

`mkPi_congr`: two fibre functions that agree on the elements of the domain form the same
Π-type. Also: a Π-proposition all of whose fibres are the full candidate is the full
candidate.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

theorem Candidate.ext' {c d : Candidate} (h : ∀ v, c.mem v ↔ d.mem v) : c = d := by
  cases c; cases d
  congr
  funext v
  exact propext (h v)

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem sep_congr {A : 𝕋.S} {p q : 𝕋.S → Prop} (h : ∀ x, x ∈ₛ A → (p x ↔ q x)) :
    𝕋.sep A p = 𝕋.sep A q := by
  refine 𝕋.ext fun x => ?_
  rw [𝕋.mem_sep, 𝕋.mem_sep]
  exact and_congr_right fun hx => h x hx

theorem relFn_congr {A : 𝕋.S} {R R' : 𝕋.S → 𝕋.S → Prop}
    (h : ∀ x y, x ∈ₛ A → y ∈ₛ A → (R x y ↔ R' x y)) : 𝕋.relFn A R = 𝕋.relFn A R' :=
  𝕋.lam_ext fun x hx => sep_congr fun y hy => h x y hx hy

theorem piCand_congr {D : 𝕋.S} {F F' : 𝕋.S → 𝕋.S} (h : ∀ d, d ∈ₛ 𝕋.El D → F d = F' d) :
    𝕋.piCand D F = 𝕋.piCand D F' := by
  refine Candidate.ext' fun v => ?_
  show (∀ d, d ∈ₛ 𝕋.El D → ∀ u, (𝕋.candOf (F d)).mem (.app v u)) ↔
    (∀ d, d ∈ₛ 𝕋.El D → ∀ u, (𝕋.candOf (F' d)).mem (.app v u))
  exact forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]

theorem tPi_congr {D : 𝕋.S} {F F' : 𝕋.S → 𝕋.S} (h : ∀ d, d ∈ₛ 𝕋.El D → F d = F' d) :
    𝕋.tPi D F = 𝕋.tPi D F' := by
  have hpi : (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) = 𝕋.pi (𝕋.El D) fun d => 𝕋.El (F' d) :=
    pi_congr fun d hd => by rw [h d hd]
  have hsep : (𝕋.sep (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F d)) fun f =>
        ∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.Rel (F d) (𝕋.app f d) (𝕋.app f d')) =
      𝕋.sep (𝕋.pi (𝕋.El D) fun d => 𝕋.El (F' d)) fun f =>
        ∀ d d', d ∈ₛ 𝕋.El D → 𝕋.Rel D d d' → 𝕋.Rel (F' d) (𝕋.app f d) (𝕋.app f d') := by
    rw [hpi]
    exact sep_congr fun f _ => forall_congr' fun d => forall_congr' fun d' =>
      imp_congr_right fun hd => by rw [h d hd]
  have hlam : 𝕋.lam (𝕋.El D) F = 𝕋.lam (𝕋.El D) F' := 𝕋.lam_ext h
  have hskel : (𝕋.lam (𝕋.El D) fun d => 𝕋.skel (F d)) = 𝕋.lam (𝕋.El D) fun d => 𝕋.skel (F' d) :=
    𝕋.lam_ext fun d hd => by rw [h d hd]
  simp only [tPi]
  rw [hsep, hlam, hskel]
  congr 3
  funext f g
  exact propext (forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd])

/-- **Π formation depends only on the fibres over the elements of the domain.** -/
theorem mkPi_congr {D : 𝕋.S} {F F' : 𝕋.S → 𝕋.S} (h : ∀ d, d ∈ₛ 𝕋.El D → F d = F' d) :
    𝕋.mkPi D F = 𝕋.mkPi D F' := by
  unfold mkPi
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc, if_pos hDc]
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn, if_pos hn, h _ hs]
    · rw [if_neg hn, if_neg hn]
  · rw [if_neg hDc, if_neg hDc]
    have hiff : (∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)) ↔ ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F' d) :=
      forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall, if_pos (hiff.1 hall), piCand_congr h]
    · rw [if_neg hall, if_neg (fun h' => hall (hiff.2 h')), tPi_congr h]

/-- λ formation depends only on the values over the elements of the domain. -/
theorem mkLam_congr {D : 𝕋.S} {f f' : 𝕋.S → 𝕋.S} (h : ∀ d, d ∈ₛ 𝕋.El D → f d = f' d) :
    𝕋.mkLam D f = 𝕋.mkLam D f' := by
  unfold mkLam
  have hiff : (∀ d, d ∈ₛ 𝕋.El D → f d = 𝕋.star) ↔ ∀ d, d ∈ₛ 𝕋.El D → f' d = 𝕋.star :=
    forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]
  by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → f d = 𝕋.star
  · rw [if_pos hall, if_pos (hiff.1 hall)]
  · rw [if_neg hall, if_neg (fun h' => hall (hiff.2 h')), 𝕋.fn_ext h]

/-! ### Π-propositions -/

/-- A Π all of whose fibres are propositions is a proposition. -/
theorem mkPi_isCand {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} (h : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)) :
    𝕋.IsCand (𝕋.mkPi D F) := by
  unfold mkPi
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc]
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn, if_pos (h _ hs)]; exact ⟨_, rfl⟩
    · rw [if_neg hn]; exact ⟨_, rfl⟩
  · rw [if_neg hDc, if_pos h]; exact ⟨_, rfl⟩

/-- A Π that is a proposition and whose proposition fibres are all the full candidate is the
full candidate. -/
theorem mkPi_full {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} (hc : 𝕋.IsCand (𝕋.mkPi D F))
    (h : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d) → F d = 𝕋.cand Candidate.full) :
    𝕋.mkPi D F = 𝕋.cand Candidate.full := by
  unfold mkPi at hc ⊢
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hc ⊢
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hc ⊢
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc, h _ hs hFc, 𝕋.candOf_cand]
        congr 1
        exact Candidate.ext' fun v => ⟨fun _ => trivial, fun _ _ _ => trivial⟩
      · rw [if_neg hFc] at hc
        exact absurd hc (not_isCand_of_kind (kind_tPiP ..) (by decide))
    · rw [if_neg hn]
  · rw [if_neg hDc] at hc ⊢
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall]
      congr 1
      refine Candidate.ext' fun v => ⟨fun _ => trivial, fun _ d hd u => ?_⟩
      rw [h d hd (hall d hd), 𝕋.candOf_cand]
      trivial
    · rw [if_neg hall] at hc
      exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-! ### Pointwise related elements of a Π-type are related -/

theorem rel_mkPi_of_pointwise {D g g' : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hg : g ∈ₛ 𝕋.El (𝕋.mkPi D F)) (hg' : g' ∈ₛ 𝕋.El (𝕋.mkPi D F))
    (h : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.Rel (F d) (𝕋.mkApp g d) (𝕋.mkApp g' d)) :
    𝕋.Rel (𝕋.mkPi D F) g g' := by
  unfold mkPi at hg hg' ⊢
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hg hg' ⊢
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hg hg' ⊢
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc] at hg hg' ⊢
        exact (rel_cand hg).2 hg'
      · rw [if_neg hFc] at hg hg' ⊢
        refine (rel_tPiP_iff hg).2 ⟨hg', ?_⟩
        have := h _ hs
        rwa [mkApp, if_neg (ne_star_of_mem_tPiP hg), mkApp,
          if_neg (ne_star_of_mem_tPiP hg')] at this
    · rw [if_neg hn] at hg hg' ⊢
      exact (rel_cand hg).2 hg'
  · rw [if_neg hDc] at hg hg' ⊢
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall] at hg hg' ⊢
      exact (rel_cand hg).2 hg'
    · rw [if_neg hall] at hg hg' ⊢
      refine (rel_tPi_iff hg).2 ⟨hg', fun d hd => ?_⟩
      have := h d hd
      rwa [mkApp, if_neg (ne_star_of_mem_tPi hg), mkApp,
        if_neg (ne_star_of_mem_tPi hg')] at this

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
