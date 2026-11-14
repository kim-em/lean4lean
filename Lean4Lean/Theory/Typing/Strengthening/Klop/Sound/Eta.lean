import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Beta

/-! # Soundness: η -/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace PVal

theorem liftN_subst_upN_scons (t u : PVal) (σ : Nat → PVal) (k : Nat) :
    (t.liftN 1 k).subst (upN k (scons u σ)) = t.subst (upN k σ) := by
  induction t generalizing k with
  | var i =>
    simp only [liftN, subst, upN, liftVar]
    by_cases h : i < k
    · simp [h]
    · have h1 : ¬ (1 + i < k) := by omega
      have h2 : 1 + i - k = (i - k) + 1 := by omega
      simp [h, h1, h2, scons]
  | lam b ih => simp only [liftN, subst, up_upN, ih]
  | app f a ihf iha => simp only [liftN, subst, ihf, iha]
  | r => rfl
  | bot => rfl
  | case s x y ihs ihx ihy => simp only [liftN, subst, ihs, ihx, ihy]

/-- Substituting into a lifted value ignores the new variable. -/
theorem lift_subst_scons (t u : PVal) (σ : Nat → PVal) :
    (t.liftN 1).subst (scons u σ) = t.subst σ := by
  have := liftN_subst_upN_scons t u σ 0
  rwa [upN_zero, upN_zero] at this

end PVal

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- **Semantic η.** An element of a Π-type with valid fibres is the abstraction of its
applications. -/
theorem mkLam_mkApp {n : Nat} {D g : 𝕊.S} {F : 𝕊.S → 𝕊.S}
    (hF : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.ValidAny (𝕊.univList n) (F d))
    (hg : g ∈ₛ 𝕊.El (𝕊.mkPi D F)) : 𝕊.mkLam D (fun d => 𝕊.mkApp g d) = g := by
  have hres : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.mkApp g d ∈ₛ 𝕊.El (F d) := fun d hd => mkApp_mem hg hd
  unfold mkPi at hg
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc] at hg
    by_cases hn : ∃ v, (𝕊.candOf D).mem v
    · have hs : 𝕊.star ∈ₛ 𝕊.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hg
      by_cases hFc : 𝕊.IsCand (F 𝕊.star)
      · rw [if_pos hFc] at hg
        have hgs := (𝕊.mem_El_cand.1 hg).1
        subst hgs
        rw [mkLam, if_pos fun d _ => by simp [mkApp]]
      · rw [if_neg hFc] at hg
        have hne : 𝕊.mkApp g 𝕊.star ≠ 𝕊.star := fun e =>
          (hF _ hs).star_not_mem hFc (by have := hres _ hs; rwa [e] at this)
        rw [mkLam, if_neg fun h => hne (h _ hs)]
        have hEl : 𝕊.El D = 𝕊.one := by
          rw [isCand_eq hDc]; simp only [cand, El_rec5]; rw [if_pos hn]
        obtain ⟨f', rfl, hf'⟩ := mem_El_tPiP.1 hg
        rw [hEl, fn]
        congr 1
        rw [(𝕊.mem_pi.1 hf').1]
        refine 𝕊.lam_ext fun x hx => ?_
        rw [mkApp, if_neg (ne_star_of_kind (k := 104) (by simp [SetModel.kind]) (by decide))]
        simp only [ap, snd_pair]
        rw [← (𝕊.mem_pi.1 hf').1]
    · rw [if_neg hn] at hg
      have hgs := (𝕊.mem_El_cand.1 hg).1
      subst hgs
      rw [mkLam, if_pos fun d _ => by simp [mkApp]]
  · rw [if_neg hDc] at hg
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · rw [if_pos hall] at hg
      have hgs := (𝕊.mem_El_cand.1 hg).1
      subst hgs
      rw [mkLam, if_pos fun d _ => by simp [mkApp]]
    · rw [if_neg hall] at hg
      have hne : ¬ ∀ d, d ∈ₛ 𝕊.El D → 𝕊.mkApp g d = 𝕊.star := fun h => hall fun d hd =>
        Classical.byContradiction fun hc =>
          (hF d hd).star_not_mem hc (by have := hres d hd; rwa [h d hd] at this)
      rw [mkLam, if_neg hne]
      obtain ⟨f', rfl, hf', -, -⟩ := mem_El_tPi.1 hg
      rw [fn]
      congr 1
      rw [(𝕊.mem_pi.1 hf').1]
      refine 𝕊.lam_ext fun x hx => ?_
      rw [mkApp, if_neg (ne_star_of_kind (k := 104) (by simp [SetModel.kind]) (by decide))]
      simp only [ap, snd_pair]
      rw [← (𝕊.mem_pi.1 hf').1]

/-- The η rule (`IsDefEqStrong.eta`). -/
theorem Sem.eta {Γ : List VExpr} {A B e : VExpr} {u v : VLevel}
    (HA : 𝕊.Sem Γ A A (.sort u)) (HB : 𝕊.Sem (A :: Γ) B B (.sort v))
    (He : 𝕊.Sem Γ e e (.forallE A B)) :
    𝕊.Sem Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) := by
  have hη : ∀ ρ w, 𝕊.ValOK Γ ρ w →
      𝕊.den ρ (.lam A (.app e.lift (.bvar 0))) = 𝕊.den ρ e := by
    intro ρ w hρ
    obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
    obtain ⟨hfib, -⟩ := HB.fibres hρ (isSemTy_of_mem_sortDen hAm)
    obtain ⟨-, -, hem, -, -⟩ := He ρ w hρ
    have : 𝕊.den ρ (.lam A (.app e.lift (.bvar 0))) =
        𝕊.mkLam (𝕊.den ρ A) fun d => 𝕊.mkApp (𝕊.den ρ e) d := by
      show 𝕊.mkLam _ _ = _
      congr 1
      funext d
      show 𝕊.mkApp (𝕊.den (𝕊.cons d ρ) e.lift) d = _
      rw [𝕊.den_lift]
    rw [this]
    exact mkLam_mkApp (n := sortLv v) (fun d hd => (mem_sortDen (hfib d hd).1).1) hem
  intro ρ w hρ
  obtain ⟨hty, -, hem, hev, her⟩ := He ρ w hρ
  obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
  have hAty : 𝕊.IsSemTy (𝕊.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨hfib, -⟩ := HB.fibres hρ hAty
  refine ⟨hty, hη ρ w hρ, (hη ρ w hρ) ▸ hem, fun hc => ⟨?_, (hev hc).1⟩, fun ρ' w' hρ' hrr => ?_⟩
  · have hc' : 𝕊.IsCand (𝕊.mkPi (𝕊.den ρ A) fun d => 𝕊.den (𝕊.cons d ρ) B) := hc
    refine lam_val_mem hc' fun d hd x hx hFc => ?_
    have hmix : (¬ ∀ d, 𝕊.mem d (𝕊.El (𝕊.den ρ A)) → 𝕊.IsCand (𝕊.den (𝕊.cons d ρ) B)) →
        ∀ d, 𝕊.mem d (𝕊.El (𝕊.den ρ A)) → 𝕊.IsCand (𝕊.den (𝕊.cons d ρ) B) →
          𝕊.den (𝕊.cons d ρ) B = 𝕊.cand Candidate.full := by
      intro hn d hd hdc
      rcases (mem_sortDen (hfib d hd).1).2 with h | h
      · exact (hn fun d hd => h _ (hfib d hd).1).elim
      · exact h _ (hfib d hd).1 hdc
    have happ := app_val_mem (vf := (pval e).subst w) (va := x) hd
      (fun h => (hev h).1) hx hmix hFc
    refine ((𝕊.candOf _).step (PVal.step_lam_app _ A w x)).2 ?_
    have : (pval (.app e.lift (.bvar 0))).subst (consV x w) = .app ((pval e).subst w) x := by
      show PVal.app ((pval e.lift).subst (consV x w)) (consV x w 0) = _
      rw [VExpr.lift, pval_liftN, consV_eq_scons, PVal.lift_subst_scons]
      rfl
    rw [this]
    exact happ
  · obtain ⟨h1, h2⟩ := her ρ' w' hρ' hrr
    refine ⟨h1, ?_⟩
    rw [hη ρ w hρ, hη ρ' w' hρ']
    exact h2

end SetModel
end VEnv.Strengthening
end Lean4Lean
