import Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent

/-! # Size-preserving descent of bidirectional certificates

Semantic descent can be strengthened to reconstruct a finite certificate below
insertion without increasing its index. In the eta-both case, fresh-spine
inversion produces a smaller inferred certificate, which descends recursively.
This supplies a decreasing replacement for eta-both during composition.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private lifted_sort_types from Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent
variable [Params]

/-- Reconstruct a bidirectional normal certificate below any thinning, with an
index no larger than the original. The advertised mode premise is retained. -/
theorem BiNormal.certificate_descend : ∀ n {mode ρ Γ Γ' a b A B},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    env.HasType univs Γ a A → env.HasType univs Γ b B →
    BiNormal mode n Γ' (a.lift' ρ) (b.lift' ρ) →
    (if mode then env.IsDefEqU univs Γ A B else ¬ IsProof Γ a) →
    ∃ m, m ≤ n ∧ BiNormal mode m Γ a b := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro mode ρ Γ Γ' a b A B W hΓ hΓ' ha hb H hmode
    by_cases hp : IsProof Γ a
    · cases mode with
      | false => exact (hmode hp).elim
      | true =>
        have HE := IsProof.descend hΓ hp ha hb hmode
        obtain ⟨P, haP, hP⟩ := hp
        exact ⟨0, Nat.zero_le _, .proofIrrel hP haP (HE.of_l henv hΓ haP).hasType.2⟩
    generalize hl : a.lift' ρ = l at H
    generalize hr : b.lift' ρ = r at H
    cases H with
    | refl _ =>
      cases lift'_inj.1 (hl.trans hr.symm)
      exact ⟨0, Nat.zero_le _, .refl ha⟩
    | sortDF h1 h2 h3 =>
      cases lift'_eq_sort hl; cases lift'_eq_sort hr
      exact ⟨0, Nat.zero_le _, .sortDF h1 h2 h3⟩
    | constDF h1 h2 h3 h4 h5 =>
      cases lift'_eq_const hl; cases lift'_eq_const hr
      exact ⟨0, Nat.zero_le _, .constDF h1 h2 h3 h4 h5⟩
    | appDF _ _ _ _ Hf Hx =>
      obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
      obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
      obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
      obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
      obtain ⟨nf, hnf, HF⟩ := ih _ (by omega) W hΓ hΓ' hf hf' Hf (not_isProof_fn hΓ hf hx hp)
      have hfPi := (HF.defeq hΓ).of_l henv hΓ hf
      obtain ⟨⟨_, hD⟩, _⟩ := (hfPi.uniqU henv hΓ hf').forallE_inv henv hΓ
      obtain ⟨nx, hnx, HX⟩ := ih _ (by omega) W hΓ hΓ' hx hx' Hx ⟨_, hD⟩
      exact ⟨_, by omega, .appDF hf hfPi.hasType.2 hx (hD.symm.defeq hx') HF HX⟩
    | projDF _ Hm =>
      obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
      obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
      obtain ⟨nm, hnm, HM⟩ := ih _ (by omega) W hΓ hΓ' hm.hasType.2 hm'.hasType.2 Hm
        (not_isProof_major hΓ ha hp)
      exact ⟨_, by omega, .projDF ha HM⟩
    | lamIndependent _ HD HB =>
      obtain ⟨D, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
      obtain ⟨D', b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
      obtain ⟨⟨u, hD⟩, _, hb₁⟩ := ha.lam_inv henv hΓ
      obtain ⟨⟨_, hD'⟩, _, hb₂⟩ := hb.lam_inv henv hΓ
      obtain ⟨nd, hnd, HD'⟩ := ih _ (by omega) W hΓ hΓ' hD hD' HD
        (lifted_sort_types hΓ hΓ' W hD hD' (HD.defeq hΓ'))
      have hDD := (HD'.defeq hΓ).of_l henv hΓ hD
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
      have hΓD' : OnCtx (D.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weak' henv W⟩
      have hb₂' := hb₂.defeqDFC henv (.succ .zero hDD.symm)
      obtain ⟨nb, hnb, HB'⟩ := ih _ (by omega) W.cons hΓD hΓD' hb₁ hb₂' HB
        (fun h => hp (h.lam hΓ hD))
      exact ⟨_, by omega, .lamIndependent hD HD' HB'⟩
    | lamCommon hD _ HB =>
      obtain ⟨D, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
      obtain ⟨D', b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
      obtain ⟨B₁, hPi₁, hb₁⟩ := ha.lam_inv_forallE henv hΓ
      obtain ⟨B₂, hPi₂, hb₂⟩ := hb.lam_inv_forallE henv hΓ
      have hPiPi := (hPi₁.trans henv hΓ hmode).trans henv hΓ hPi₂.symm
      obtain ⟨⟨u, hDD⟩, _, hBB⟩ := hPiPi.forallE_inv henv hΓ
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hDD.hasType.1⟩
      have hΓD' : OnCtx (D.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hDD.hasType.1.weak' henv W⟩
      have hb₂' := hb₂.defeqDFC henv (.succ .zero hDD.symm)
      have HB' := HB.defeqDFC hΓ' (.succ .zero hD)
      obtain ⟨nb, hnb, Hbb⟩ := ih _ (by omega) W.cons hΓD hΓD' hb₁ hb₂' HB' ⟨_, hBB⟩
      exact ⟨_, by omega, .lamCommon hDD.hasType.1 hDD Hbb⟩
    | forallEDF _ HD _ HB =>
      obtain ⟨D, B₁, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
      obtain ⟨D', B₂, rfl, rfl, rfl⟩ := lift'_eq_forallE hr
      obtain ⟨⟨u, hD⟩, _, hB₁⟩ := ha.forallE_inv henv
      obtain ⟨⟨_, hD'⟩, _, hB₂⟩ := hb.forallE_inv henv
      obtain ⟨nd, hnd, HD'⟩ := ih _ (by omega) W hΓ hΓ' hD hD' HD
        (lifted_sort_types hΓ hΓ' W hD hD' (HD.defeq hΓ'))
      have hDD := (HD'.defeq hΓ).of_l henv hΓ hD
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
      have hΓD' : OnCtx (D.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weak' henv W⟩
      have hB₂' := hB₂.defeqDFC henv (.succ .zero hDD.symm)
      obtain ⟨nb, hnb, HB'⟩ := ih _ (by omega) W.cons hΓD hΓD' hB₁ hB₂' HB
        (lifted_sort_types hΓD hΓD' W.cons hB₁ hB₂' (HB.defeq hΓD'))
      exact ⟨_, by omega, .forallEDF hD HD' hB₁ HB'⟩
    | etaL he' Hb =>
      obtain ⟨A₀, e₀, rfl, rfl, rfl⟩ := lift'_eq_lam hl
      subst hr
      obtain ⟨B₁, hPi₁, he₀⟩ := ha.lam_inv_forallE henv hΓ
      have hbPi := hb.defeqU_r henv hΓ (hmode.symm.trans henv hΓ hPi₁.symm)
      obtain ⟨⟨u, hA₀⟩, -⟩ := (hbPi.isType henv hΓ).forallE_inv henv
      have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
      have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weak' henv W⟩
      have hbody : env.HasType univs (A₀ :: Γ) (.app b.lift (.bvar 0)) B₁ := by
        simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (hbPi.weak henv (B := A₀)) (.bvar .zero)
      rw [show (b.lift' ρ).lift.app (.bvar 0) = (VExpr.app b.lift (.bvar 0)).lift' ρ.cons by
        simp [lift', lift_lift'_cons]] at Hb
      obtain ⟨w, hB₁s⟩ := he₀.isType henv hΓA
      obtain ⟨nb, hnb, HB⟩ := ih _ (by omega) W.cons hΓA hΓA' he₀ hbody Hb ⟨_, hB₁s⟩
      exact ⟨_, by omega, .etaL hbPi HB⟩
    | etaR he Hb =>
      obtain ⟨A₂, e₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
      subst hl
      obtain ⟨B₂, hPi₂, he₂⟩ := hb.lam_inv_forallE henv hΓ
      have haPi := ha.defeqU_r henv hΓ (hmode.trans henv hΓ hPi₂.symm)
      obtain ⟨⟨u, hA₂⟩, -⟩ := (haPi.isType henv hΓ).forallE_inv henv
      have hΓA : OnCtx (A₂ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₂⟩
      have hΓA' : OnCtx (A₂.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₂.weak' henv W⟩
      have hbody : env.HasType univs (A₂ :: Γ) (.app a.lift (.bvar 0)) B₂ := by
        simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (haPi.weak henv (B := A₂)) (.bvar .zero)
      rw [show (a.lift' ρ).lift.app (.bvar 0) = (VExpr.app a.lift (.bvar 0)).lift' ρ.cons by
        simp [lift', lift_lift'_cons]] at Hb
      obtain ⟨w, hB₂s⟩ := he₂.isType henv hΓA
      obtain ⟨nb, hnb, HB⟩ := ih _ (by omega) W.cons hΓA hΓA' hbody he₂ Hb ⟨_, hB₂s⟩
      exact ⟨_, by omega, .etaR haPi HB⟩
    | @etaBoth _ _ Ad Bd _ _ he he' Hb =>
      subst hl hr
      obtain ⟨⟨u, hAd⟩, -⟩ := (he.isType henv hΓ').forallE_inv henv
      have hΓA' : OnCtx (Ad :: Γ') (env.IsType univs) := ⟨hΓ', u, hAd⟩
      have hn' : ¬ IsProof (Ad :: Γ') (varSpine (a.lift' ρ.skip) [0]) := by
        intro hproof
        change IsProof (Ad :: Γ') (.app (a.lift' ρ.skip) (.bvar 0)) at hproof
        rw [← lift_lift'_skip] at hproof
        obtain ⟨P, hproof, hP⟩ := IsProof.of_etaBody hΓ' he hproof
        exact hp (IsProof.of_lift hΓ hΓ' W ha hP hproof)
      rw [show (a.lift' ρ).lift.app (.bvar 0) = varSpine (a.lift' ρ.skip) [0] by
          simp [varSpine, lift_lift'_skip],
        show (b.lift' ρ).lift.app (.bvar 0) = varSpine (b.lift' ρ.skip) [0] by
          simp [varSpine, lift_lift'_skip]] at Hb
      obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := BiNormal.spine_inv _ (by simp) (W.skip (A := Ad)) hΓA' hn' Hb
      obtain ⟨j, hj, HJ⟩ := ih k (by omega) W' hΓ hΓ'' ha hb H' hp
      exact ⟨j+1, by omega, .promote HJ⟩
    | proofIrrel hP hl' _ =>
      subst hl
      exact (hp (IsProof.of_lift hΓ hΓ' W ha hP hl')).elim
    | promote H =>
      subst hl hr
      obtain ⟨m, hm, HM⟩ := ih _ (by omega) W hΓ hΓ' ha hb H hp
      exact ⟨m+1, by omega, .promote HM⟩

/-- The eta-both body already contains a smaller inferred certificate of its
original functions. Fresh-spine cancellation and certificate descent preserve
the body's index bound; no Pi-head recovery or proposition front is assumed. -/
theorem BiNormal.etaBoth_inferred (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B)) (hn : ¬ IsProof Γ f)
    (HB : BiNormal true n (A :: Γ) (.app f.lift (.bvar 0)) (.app g.lift (.bvar 0))) :
    ∃ k, k ≤ n ∧ BiNormal false k Γ f g := by
  obtain ⟨⟨u, hA⟩, -⟩ := (hf.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hn' : ¬ IsProof (A :: Γ) (varSpine (f.lift' (.skip .refl)) [0]) := by
    intro hp
    have hp' : IsProof (A :: Γ) (.app f.lift (.bvar 0)) := by
      simpa only [varSpine, lift_eq_lift'] using hp
    exact hn (IsProof.of_etaBody hΓ hf hp')
  have HB' : BiNormal true n (A :: Γ)
      (varSpine (f.lift' (.skip .refl)) [0]) (varSpine (g.lift' (.skip .refl)) [0]) := by
    simpa only [varSpine, lift_eq_lift'] using HB
  obtain ⟨k, Δ, hk, W, hΔ, HK⟩ := BiNormal.spine_inv n (by simp)
    (Ctx.Lift'.skip .refl) hΓA hn' HB'
  obtain ⟨j, hj, HJ⟩ := BiNormal.certificate_descend k W hΓ hΔ hf hg HK hn
  exact ⟨j, Nat.le_trans hj hk, HJ⟩

end Lean4Lean.VEnv.Strengthening
