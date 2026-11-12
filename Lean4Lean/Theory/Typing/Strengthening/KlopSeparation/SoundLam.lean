import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.ValSubst

/-! # Soundness: the abstraction rule -/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕋 : SetModel}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- A value realizes a Π-proposition when its applications realize the fibres. -/
theorem lam_val_mem {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} {v : PVal} (hc : 𝕋.IsCand (𝕋.mkPi D F))
    (hbody : ∀ d, d ∈ₛ 𝕋.El D → ∀ u, (𝕋.IsCand D → (𝕋.candOf D).mem u) →
      𝕋.IsCand (F d) → (𝕋.candOf (F d)).mem (.app v u)) :
    (𝕋.candOf (𝕋.mkPi D F)).mem v := by
  unfold mkPi at hc ⊢
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hc ⊢
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hc ⊢
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc, 𝕋.candOf_cand]
        exact fun u hu => hbody _ hs u (fun _ => hu) hFc
      · rw [if_neg hFc] at hc
        exact absurd hc (not_isCand_of_kind (kind_tPiP ..) (by decide))
    · rw [if_neg hn, 𝕋.candOf_cand]; trivial
  · rw [if_neg hDc] at hc ⊢
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall, 𝕋.candOf_cand]
      exact fun d hd u => hbody d hd u (fun h => (hDc h).elim) (hall d hd)
    · rw [if_neg hall] at hc
      exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-- The abstraction rule (`IsDefEqStrong.lamDF`). -/
theorem Sem.lam {Γ : List VExpr} {A A' B body body' : VExpr} {u v : VLevel}
    (HA : 𝕋.Sem Γ A A' (.sort u)) (HB : 𝕋.Sem (A :: Γ) B B (.sort v))
    (Hb : 𝕋.Sem (A :: Γ) body body' B)
    (HAU : 𝕋.SemU Γ A (.sort u)) (HBU : 𝕋.SemU (A :: Γ) B (.sort v))
    (HbU : 𝕋.SemU (A :: Γ) body B) :
    𝕋.Sem Γ (.lam A body) (.lam A' body') (.forallE A B) := by
  have HPi : 𝕋.Sem Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
    Sem.forallE (HA.trans HA.symm) HB HBU
  have HlamU := SemU.lam (HA.trans HA.symm) HB (Hb.trans Hb.symm) HAU HBU HbU
  -- membership, at any valuation
  have key : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.mem (𝕋.den ρ (.lam A body)) (𝕋.El (𝕋.den ρ (.forallE A B))) := by
    intro ρ w hρ
    obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
    have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
    obtain ⟨n, hAv⟩ := hAty
    obtain ⟨hfib, -⟩ := HB.fibres hρ ⟨n, hAv⟩
    refine mkLam_mem_mkPi (n := sortLv v) (fun d hd => (mem_sortDen (hfib d hd).1).1)
      (fun d hd => ?_) (fun d d' hd hdd' => hAv.isPER.mem _ _ hd hdd') (fun d d' hd hdd' => ?_)
      (fun hDc hall => SemDU.piUnif (d := fun ρ => 𝕋.den ρ body) HlamU hρ
        (fun d hd => ⟨_, (mem_sortDen (hfib d hd).1).1⟩) (fun d hd => ?_) hDc hall)
    · obtain ⟨u', hu'⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd
      exact (Hb _ _ hu').2.2.1
    · have hd' := hAv.isPER.mem _ _ hd hdd'
      obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd
      obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd'
      exact ((Hb _ _ h₁).2.2.2.2 _ _ h₂ (coRel_cons (coRel_refl hρ) rfl hdd')).2
    · obtain ⟨u', hu'⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd
      exact (Hb _ _ hu').2.2.1
  intro ρ w hρ
  obtain ⟨-, hAA', hAm, -, hAr⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨-, -, hPim, -, hPir⟩ := HPi ρ w hρ
  refine ⟨isSemTy_of_mem_sortDen hPim, ?_, key ρ w hρ, fun hc => ?_, fun ρ' w' hρ' hr => ?_⟩
  · show 𝕋.mkLam _ _ = 𝕋.mkLam _ _
    rw [← hAA']
    refine mkLam_congr fun d hd => ?_
    obtain ⟨u', hu'⟩ := exists_valOK_cons hρ hAty hd
    exact (Hb _ _ hu').2.1
  · have hc' : 𝕋.IsCand (𝕋.mkPi (𝕋.den ρ A) fun d => 𝕋.den (𝕋.cons d ρ) B) := hc
    constructor
    · refine lam_val_mem hc' fun d hd u hu hFc => ?_
      have hv := ((Hb _ _ (valOK_cons hρ hAty hd hu)).2.2.2.1 hFc).1
      exact ((𝕋.candOf _).step (PVal.step_lam_app body A w u)).2 hv
    · refine lam_val_mem hc' fun d hd u hu hFc => ?_
      have hv := ((Hb _ _ (valOK_cons hρ hAty hd hu)).2.2.2.1 hFc).2
      exact ((𝕋.candOf _).step (PVal.step_lam_app body' A' w u)).2 hv
  · obtain ⟨-, -, hAm', -, -⟩ := HA ρ' w' hρ'
    have hAty' : 𝕋.IsSemTy (𝕋.den ρ' A) := isSemTy_of_mem_sortDen hAm'
    obtain ⟨-, -, hPim', -, -⟩ := HPi ρ' w' hρ'
    have hTP := (tyRel_of_rel_sortDen hPim (hPir ρ' w' hρ' hr).2).2
    have hTA : 𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) :=
      (tyRel_of_rel_sortDen hAm (hAr ρ' w' hρ' hr).2).2
    have hsameP := (mem_sortDen hPim).1.tyRel_same (mem_sortDen hPim').1 hTP
    have hsameA := (mem_sortDen hAm).1.tyRel_same (mem_sortDen hAm').1 hTA
    refine ⟨hTP, ?_⟩
    have hg' : 𝕋.mem (𝕋.den ρ' (.lam A body)) (𝕋.El (𝕋.den ρ (.forallE A B))) := by
      rw [hsameP.1]; exact key ρ' w' hρ'
    refine rel_mkPi_of_pointwise (key ρ w hρ) hg' fun d hd => ?_
    have hd' : 𝕋.mem d (𝕋.El (𝕋.den ρ' A)) := hsameA.1 ▸ hd
    show 𝕋.Rel _ (𝕋.mkApp (𝕋.mkLam _ _) d) (𝕋.mkApp (𝕋.mkLam _ _) d)
    rw [𝕋.mkApp_mkLam hd, 𝕋.mkApp_mkLam hd']
    obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ hAty hd
    obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ' hAty' hd'
    obtain ⟨n, hAv⟩ := hAty
    exact ((Hb _ _ h₁).2.2.2.2 _ _ h₂ (coRel_cons hr hTA (hAv.isPER.refl _ hd))).2

end SetModel
end VEnv.Strengthening
end Lean4Lean
