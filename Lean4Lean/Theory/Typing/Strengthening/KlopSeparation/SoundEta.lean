import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SoundBeta

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

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- **Semantic η.** An element of a Π-type with valid fibres is the abstraction of its
applications. -/
theorem mkLam_mkApp {n : Nat} {D g : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hF : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.ValidAny (𝕋.univList n) (F d))
    (hg : g ∈ₛ 𝕋.El (𝕋.mkPi D F)) : 𝕋.mkLam D (fun d => 𝕋.mkApp g d) = g := by
  have hres : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.mkApp g d ∈ₛ 𝕋.El (F d) := fun d hd => mkApp_mem hg hd
  unfold mkPi at hg
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hg
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · have hs : 𝕋.star ∈ₛ 𝕋.El D := by rw [isCand_eq hDc]; exact star_mem_cand hn
      rw [if_pos hn] at hg
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc] at hg
        have hgs := (𝕋.mem_El_cand.1 hg).1
        subst hgs
        rw [mkLam, if_pos fun d _ => by simp [mkApp]]
      · rw [if_neg hFc] at hg
        have hne : 𝕋.mkApp g 𝕋.star ≠ 𝕋.star := fun e =>
          (hF _ hs).star_not_mem hFc (by have := hres _ hs; rwa [e] at this)
        rw [mkLam, if_neg fun h => hne (h _ hs)]
        have hEl : 𝕋.El D = 𝕋.one := by
          rw [isCand_eq hDc]; simp only [cand, El_rec5]; rw [if_pos hn]
        obtain ⟨f', rfl, hf'⟩ := mem_El_tPiP.1 hg
        rw [hEl, fn]
        congr 1
        rw [(𝕋.mem_pi.1 hf').1]
        refine 𝕋.lam_ext fun x hx => ?_
        rw [mkApp, if_neg (ne_star_of_kind (k := 104) (by simp [UniverseTower.kind]) (by decide))]
        simp only [ap, snd_pair]
        rw [← (𝕋.mem_pi.1 hf').1]
    · rw [if_neg hn] at hg
      have hgs := (𝕋.mem_El_cand.1 hg).1
      subst hgs
      rw [mkLam, if_pos fun d _ => by simp [mkApp]]
  · rw [if_neg hDc] at hg
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall] at hg
      have hgs := (𝕋.mem_El_cand.1 hg).1
      subst hgs
      rw [mkLam, if_pos fun d _ => by simp [mkApp]]
    · rw [if_neg hall] at hg
      have hne : ¬ ∀ d, d ∈ₛ 𝕋.El D → 𝕋.mkApp g d = 𝕋.star := fun h => hall fun d hd =>
        Classical.byContradiction fun hc =>
          (hF d hd).star_not_mem hc (by have := hres d hd; rwa [h d hd] at this)
      rw [mkLam, if_neg hne]
      obtain ⟨f', rfl, hf', -⟩ := mem_El_tPi.1 hg
      rw [fn]
      congr 1
      rw [(𝕋.mem_pi.1 hf').1]
      refine 𝕋.lam_ext fun x hx => ?_
      rw [mkApp, if_neg (ne_star_of_kind (k := 104) (by simp [UniverseTower.kind]) (by decide))]
      simp only [ap, snd_pair]
      rw [← (𝕋.mem_pi.1 hf').1]

/-- The η rule (`IsDefEqStrong.eta`). -/
theorem Sem.eta {Γ : List VExpr} {A B e : VExpr} {u v : VLevel}
    (HA : 𝕋.Sem Γ A A (.sort u)) (HB : 𝕋.Sem (A :: Γ) B B (.sort v))
    (He : 𝕋.Sem Γ e e (.forallE A B)) :
    𝕋.Sem Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) := by
  have hη : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.den ρ (.lam A (.app e.lift (.bvar 0))) = 𝕋.den ρ e := by
    intro ρ w hρ
    obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
    obtain ⟨hfib, -⟩ := HB.fibres hρ (isSemTy_of_mem_sortDen hAm)
    obtain ⟨-, -, hem, -, -⟩ := He ρ w hρ
    have : 𝕋.den ρ (.lam A (.app e.lift (.bvar 0))) =
        𝕋.mkLam (𝕋.den ρ A) fun d => 𝕋.mkApp (𝕋.den ρ e) d := by
      show 𝕋.mkLam _ _ = _
      congr 1
      funext d
      show 𝕋.mkApp (𝕋.den (𝕋.cons d ρ) e.lift) d = _
      rw [𝕋.den_lift]
    rw [this]
    exact mkLam_mkApp (n := sortLv v) (fun d hd => (mem_sortDen (hfib d hd).1).1) hem
  intro ρ w hρ
  obtain ⟨hty, -, hem, hev, her⟩ := He ρ w hρ
  obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨hfib, -⟩ := HB.fibres hρ hAty
  refine ⟨hty, hη ρ w hρ, (hη ρ w hρ) ▸ hem, fun hc => ⟨?_, (hev hc).1⟩, fun ρ' w' hρ' hrr => ?_⟩
  · have hc' : 𝕋.IsCand (𝕋.mkPi (𝕋.den ρ A) fun d => 𝕋.den (𝕋.cons d ρ) B) := hc
    refine lam_val_mem hc' fun d hd x hx hFc => ?_
    have hmix : (¬ ∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) → 𝕋.IsCand (𝕋.den (𝕋.cons d ρ) B)) →
        ∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) → 𝕋.IsCand (𝕋.den (𝕋.cons d ρ) B) →
          𝕋.den (𝕋.cons d ρ) B = 𝕋.cand Candidate.full := by
      intro hn d hd hdc
      rcases (mem_sortDen (hfib d hd).1).2 with h | h
      · exact (hn fun d hd => h _ (hfib d hd).1).elim
      · exact h _ (hfib d hd).1 hdc
    have happ := app_val_mem (vf := (pval e).subst w) (va := x) hd
      (fun h => (hev h).1) hx hmix hFc
    refine ((𝕋.candOf _).step (PVal.step_lam_app _ A w x)).2 ?_
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

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
