import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.PiValid

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

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

theorem sep_congr {A : 𝕊.S} {p q : 𝕊.S → Prop} (h : ∀ x, x ∈ₛ A → (p x ↔ q x)) :
    𝕊.sep A p = 𝕊.sep A q := by
  refine 𝕊.ext fun x => ?_
  rw [𝕊.mem_sep, 𝕊.mem_sep]
  exact and_congr_right fun hx => h x hx

theorem piCand_congr {D : 𝕊.S} {F F' : 𝕊.S → 𝕊.S} (h : ∀ d, d ∈ₛ 𝕊.El D → F d = F' d) :
    𝕊.piCand D F = 𝕊.piCand D F' := by
  refine Candidate.ext' fun v => ?_
  show (∀ d, d ∈ₛ 𝕊.El D → ∀ u, (𝕊.candOf (F d)).mem (.app v u)) ↔
    (∀ d, d ∈ₛ 𝕊.El D → ∀ u, (𝕊.candOf (F' d)).mem (.app v u))
  exact forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]

theorem tPi_congr {D : 𝕊.S} {F F' : 𝕊.S → 𝕊.S} (h : ∀ d, d ∈ₛ 𝕊.El D → F d = F' d) :
    𝕊.tPi D F = 𝕊.tPi D F' := by
  have hpi : (𝕊.pi (𝕊.El D) fun d => 𝕊.El (F d)) = 𝕊.pi (𝕊.El D) fun d => 𝕊.El (F' d) :=
    pi_congr fun d hd => by rw [h d hd]
  have hlam : 𝕊.lam (𝕊.El D) F = 𝕊.lam (𝕊.El D) F' := 𝕊.lam_ext h
  have hun : 𝕊.PiUnif D F = 𝕊.PiUnif D F' := by
    funext g; simp only [PiUnif, prePi, hlam]
  have hsep : (𝕊.sep (𝕊.pi (𝕊.El D) fun d => 𝕊.El (F d)) fun f =>
        (∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F d) (𝕊.app f d) (𝕊.app f d')) ∧
        𝕊.PiUnif D F (𝕊.pair (𝕊.tagN 104) f)) =
      𝕊.sep (𝕊.pi (𝕊.El D) fun d => 𝕊.El (F' d)) fun f =>
        (∀ d d', d ∈ₛ 𝕊.El D → 𝕊.Rel D d d' → 𝕊.Rel (F' d) (𝕊.app f d) (𝕊.app f d')) ∧
        𝕊.PiUnif D F' (𝕊.pair (𝕊.tagN 104) f) := by
    rw [hpi, hun]
    exact sep_congr fun f _ => and_congr_left fun _ => forall_congr' fun d =>
      forall_congr' fun d' => imp_congr_right fun hd => by rw [h d hd]
  have hskel : (𝕊.lam (𝕊.El D) fun d => 𝕊.skel (F d)) = 𝕊.lam (𝕊.El D) fun d => 𝕊.skel (F' d) :=
    𝕊.lam_ext fun d hd => by rw [h d hd]
  simp only [tPi]
  rw [hsep, hlam, hskel]
  congr 3
  funext f g
  exact propext (forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd])

/-- **Π formation depends only on the fibres over the elements of the domain.** -/
theorem mkPi_congr {D : 𝕊.S} {F F' : 𝕊.S → 𝕊.S} (h : ∀ d, d ∈ₛ 𝕊.El D → F d = F' d) :
    𝕊.mkPi D F = 𝕊.mkPi D F' := by
  unfold mkPi
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc, if_pos hDc]
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn, if_pos hn, h _ hs]
    · rw [if_neg hn, if_neg hn]
  · rw [if_neg hDc, if_neg hDc]
    have hiff : (∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)) ↔ ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F' d) :=
      forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · rw [if_pos hall, if_pos (hiff.1 hall), piCand_congr h]
    · rw [if_neg hall, if_neg (fun h' => hall (hiff.2 h')), tPi_congr h]

/-- λ formation depends only on the values over the elements of the domain. -/
theorem mkLam_congr {D : 𝕊.S} {f f' : 𝕊.S → 𝕊.S} (h : ∀ d, d ∈ₛ 𝕊.El D → f d = f' d) :
    𝕊.mkLam D f = 𝕊.mkLam D f' := by
  unfold mkLam
  have hiff : (∀ d, d ∈ₛ 𝕊.El D → f d = 𝕊.star) ↔ ∀ d, d ∈ₛ 𝕊.El D → f' d = 𝕊.star :=
    forall_congr' fun d => imp_congr_right fun hd => by rw [h d hd]
  by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → f d = 𝕊.star
  · rw [if_pos hall, if_pos (hiff.1 hall)]
  · rw [if_neg hall, if_neg (fun h' => hall (hiff.2 h')), 𝕊.fn_ext h]

/-! ### Π-propositions -/

/-- A Π all of whose fibres are propositions is a proposition. -/
theorem mkPi_isCand {D : 𝕊.S} {F : 𝕊.S → 𝕊.S} (h : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)) :
    𝕊.IsCand (𝕊.mkPi D F) := by
  unfold mkPi
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc]
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn, if_pos (h _ hs)]; exact ⟨_, rfl⟩
    · rw [if_neg hn]; exact ⟨_, rfl⟩
  · rw [if_neg hDc, if_pos h]; exact ⟨_, rfl⟩

/-- A Π that is a proposition and whose proposition fibres are all the full candidate is the
full candidate. -/
theorem mkPi_full {D : 𝕊.S} {F : 𝕊.S → 𝕊.S} (hc : 𝕊.IsCand (𝕊.mkPi D F))
    (h : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d) → F d = 𝕊.cand Candidate.full) :
    𝕊.mkPi D F = 𝕊.cand Candidate.full := by
  unfold mkPi at hc ⊢
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc] at hc ⊢
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hc ⊢
      by_cases hFc : 𝕊.IsCand (F 𝕊.star)
      · rw [if_pos hFc, h _ hs hFc, 𝕊.candOf_cand]
        congr 1
        exact Candidate.ext' fun v => ⟨fun _ => trivial, fun _ _ _ => trivial⟩
      · rw [if_neg hFc] at hc
        exact absurd hc (not_isCand_of_kind (kind_tPiP ..) (by decide))
    · rw [if_neg hn]
  · rw [if_neg hDc] at hc ⊢
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · rw [if_pos hall]
      congr 1
      refine Candidate.ext' fun v => ⟨fun _ => trivial, fun _ d hd u => ?_⟩
      rw [h d hd (hall d hd), 𝕊.candOf_cand]
      trivial
    · rw [if_neg hall] at hc
      exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-! ### Pointwise related elements of a Π-type are related -/

theorem rel_mkPi_of_pointwise {D g g' : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hg : g ∈ₛ 𝕊.El (𝕊.mkPi D F)) (hg' : g' ∈ₛ 𝕊.El (𝕊.mkPi D F))
    (h : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.Rel (F d) (𝕊.mkApp g d) (𝕊.mkApp g' d)) :
    𝕊.Rel (𝕊.mkPi D F) g g' := by
  unfold mkPi at hg hg' ⊢
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc] at hg hg' ⊢
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hg hg' ⊢
      by_cases hFc : 𝕊.IsCand (F 𝕊.star)
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
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · rw [if_pos hall] at hg hg' ⊢
      exact (rel_cand hg).2 hg'
    · rw [if_neg hall] at hg hg' ⊢
      refine (rel_tPi_iff hg).2 ⟨hg', fun d hd => ?_⟩
      have := h d hd
      rwa [mkApp, if_neg (ne_star_of_mem_tPi hg), mkApp,
        if_neg (ne_star_of_mem_tPi hg')] at this

end SetModel
end VEnv.Strengthening
end Lean4Lean
