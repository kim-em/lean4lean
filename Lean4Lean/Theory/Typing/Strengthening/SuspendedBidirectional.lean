import Lean4Lean.Theory.Typing.Strengthening.SuspendedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent

/-! # Bidirectional comparison through separate ambient substitutions

Each endpoint may use a different ambient realization. In particular, eta-only
binders can be instantiated independently without exposing a Pi below.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {e e' a b A D : VExpr}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- An arbitrary typed prefix of the source context can be realized in a fresh
ambient target. The smaller context and its substitution remain unchanged. -/
theorem SubstLiftSquare.extend (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hΔs : OnCtx (Ξ ++ Δ) (Params.env.IsType univs)) :
    ∃ Γ'' κ' τ', OnCtx Γ'' (Params.env.IsType univs) ∧
      SubstLiftSquare Γ Γ'' (Ξ ++ Δ) (ρ.skipN Ξ.length) κ' σ τ' := by
  induction Ξ with
  | nil => exact ⟨Γ', κ, τ, hΓ', S⟩
  | cons A Ξ ih =>
    obtain ⟨hΞ, u, hA⟩ := hΔs
    obtain ⟨Γ'', κ', τ', hΓ'', S'⟩ := ih hΞ
    have hA' := hA.subst henv S'.typed hΓ''
    exact ⟨A.subst τ' :: Γ'', κ'.skip, τ'.lift, ⟨hΓ'', _, hA'⟩,
      S'.skip_at hΓ'' hA ⟨_, hA'⟩⟩

/-- A sort level of a suspended template is preserved when its instance is
independently typed below; uniqueness is used only inside its own ambient target. -/
theorem SubstLiftSquare.sort_level (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Δ ⊢ e.lift' ρ : .sort u) (he' : Γ ⊢ e.subst σ : .sort v) : u ≈ v := by
  have h := he.subst henv S.typed hΓ'
  rw [S.apply] at h
  exact (h.uniqU henv hΓ' (he'.weak' henv S.context)).sort_inv henv hΓ'

/-- Source equality of types aligns the sort levels of their independently
instantiated typings, even when the two ambient targets differ. -/
theorem suspended_sort_types
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂)
    (he : Δ ⊢ e.lift' ρ : .sort u) (H : Δ ⊢ e.lift' ρ ≡ e'.lift' ρ)
    (ha : Γ ⊢ e.subst σ₁ : .sort v) (hb : Γ ⊢ e'.subst σ₂ : .sort w) :
    Γ ⊢ .sort v ≡ .sort w := by
  have h₁ := S₁.sort_level hΓ₁ he ha
  have h₂ := S₂.sort_level hΓ₂ (H.of_l henv S₁.typed.wf he).hasType.2 hb
  exact ⟨_, IsDefEq.sortDF (ha.sort_r henv hΓ) (hb.sort_r henv hΓ) (h₁.symm.trans h₂)⟩


/-- Mode-indexed comparisons descend through heterogeneous suspended proof
substitutions, allowing each endpoint its own typed ambient realization. The
input must still carry recursive domain certificates in independent mode. -/
theorem BiNormal.suspended_reflect : ∀ n {mode : Bool} {Γ Γ₁ Γ₂ Δ : List VExpr}
    {ρ κ₁ κ₂ : Lift} {σ₁ σ₂ τ₁ τ₂ : Subst} {a b A B : VExpr},
    OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ₁ (Params.env.IsType univs) → OnCtx Γ₂ (Params.env.IsType univs) →
    SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁ → SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂ →
    ProofSubstRel Γ σ₁ σ₂ → (Γ ⊢ a.subst σ₁ : A) → (Γ ⊢ b.subst σ₂ : B) →
    BiNormal mode n Δ (a.lift' ρ) (b.lift' ρ) →
    (if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a.subst σ₁)) →
    ∃ m, BiNormal mode m Γ (a.subst σ₁) (b.subst σ₂) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mode Γ Γ₁ Γ₂ Δ ρ κ₁ κ₂ σ₁ σ₂ τ₁ τ₂ a b A B hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ ha hb H hmode
  by_cases hp : IsProof Γ (a.subst σ₁)
  · cases mode with
    | false => exact (hmode hp).elim
    | true =>
      obtain ⟨P, haP, hP⟩ := hp
      have hAP := ha.uniqU henv hΓ haP
      exact ⟨_, .proofIrrel hP haP (hb.defeqU_r henv hΓ (hmode.symm.trans henv hΓ hAP))⟩
  have hΔ := S₁.typed.wf
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  cases H with
  | refl _ =>
    cases lift'_inj.1 (hl.trans hr.symm)
    obtain ⟨_, H⟩ := subst_certificate_nonproof a hΓ Hσ ha hb hp
    obtain ⟨_, H⟩ := H.toBiNormal
    cases mode with
    | false => exact ⟨_, H⟩
    | true => exact ⟨_, .promote H⟩
  | sortDF h1 h2 h3 =>
    cases lift'_eq_sort hl; cases lift'_eq_sort hr
    exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    cases lift'_eq_const hl; cases lift'_eq_const hr
    exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF _ _ _ _ Hf Hx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    obtain ⟨_, HF⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hf hf' Hf
      (not_isProof_fn hΓ hf hx hp)
    have hff := (HF.defeq hΓ).of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
    obtain ⟨_, HX⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hx hx' Hx ⟨_, hDD⟩
    exact ⟨_, .appDF hf hff.hasType.2 hx ((HX.defeq hΓ).of_l henv hΓ hx).hasType.2 HF HX⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    obtain ⟨_, HM⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hm.hasType.2 hm'.hasType.2 Hm
      (not_isProof_major hΓ ha hp)
    exact ⟨_, .projDF ha HM⟩
  | lamIndependent hD HD HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.lam_inv henv hΓ
    obtain ⟨_, HC⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hD₀ hD₁ HD
      (suspended_sort_types hΓ hΓ₁ hΓ₂ S₁ S₂ hD (HD.defeq hΔ) hD₀ hD₁)
    have hDD := (HC.defeq hΓ).of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ₁ hD
    have SS₂ := S₂.lift_via_template hΓ₂ hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    obtain ⟨_, HB₀⟩ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB
      (fun h => hp (h.lam hΓ hD₀))
    exact ⟨_, .lamIndependent hD₀ HC HB₀⟩
  | lamCommon hD₁ hD₂ HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨B₁, hPi₁, hb₁⟩ := ha.lam_inv_forallE henv hΓ
    obtain ⟨B₂, hPi₂, hb₂⟩ := hb.lam_inv_forallE henv hΓ
    obtain ⟨⟨_, hDD⟩, _, hBB⟩ := ((hPi₁.trans henv hΓ hmode).trans henv hΓ hPi₂.symm).forallE_inv henv hΓ
    have hD₀ := hDD.hasType.1
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    have SS₁ := S₁.lift_via_template hΓ₁ hD₁.hasType.1 ⟨_, hD₁⟩ ⟨_, hD₀⟩
    have SS₂ := S₂.lift_via_template hΓ₂ hD₂.hasType.1 ⟨_, hD₂⟩ ⟨_, hDD.symm⟩
    have hb₂' := hb₂.defeqDFC henv (.succ .zero hDD.symm)
    obtain ⟨_, HB₀⟩ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₁ hb₂' HB ⟨_, hBB⟩
    exact ⟨_, .lamCommon hD₀ hDD HB₀⟩
  | forallEDF hD HD hBody HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.forallE_inv henv
    obtain ⟨_, HC⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hD₀ hD₁ HD
      (suspended_sort_types hΓ hΓ₁ hΓ₂ S₁ S₂ hD (HD.defeq hΔ) hD₀ hD₁)
    have hDD := (HC.defeq hΓ).of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ₁ hD
    have SS₂ := S₂.lift_via_template hΓ₂ hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    obtain ⟨_, HB₀⟩ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB
      (suspended_sort_types hΓD hΓ₁D hΓ₂D SS₁ SS₂ hBody (HB.defeq ⟨hΔ, _, hD⟩) hb₀ hb₁')
    exact ⟨_, .forallEDF hD₀ HC hb₀ HB₀⟩
  | etaL hf HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    subst hr
    obtain ⟨⟨_, hD⟩, _⟩ := (hf.isType henv.ordered hΔ).forallE_inv henv.ordered
    obtain ⟨B₁, hPi, hbody⟩ := ha.lam_inv_forallE henv hΓ
    have hbPi : Γ ⊢ b.subst σ₂ : .forallE (D.subst σ₁) B₁ :=
      hb.defeqU_r henv hΓ (hmode.symm.trans henv hΓ hPi.symm)
    obtain ⟨⟨_, hD₀⟩, _⟩ := (hbPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    have hfAmbient := hf.subst henv S₂.typed hΓ₂
    rw [S₂.apply] at hfAmbient
    obtain ⟨⟨_, hdomains⟩, _⟩ := (hfAmbient.uniqU henv hΓ₂ (hbPi.weak' henv S₂.context)).forallE_inv henv hΓ₂
    have SS₁ := S₁.lift_template hΓ₁ hD
    have SS₂ := S₂.lift_at (D := D.subst σ₁) hΓ₂ hD ⟨_, hdomains⟩
    have hright : D.subst σ₁ :: Γ ⊢ .app (b.subst σ₂).lift (.bvar 0) : B₁ := by
      have h := HasType.app (hbPi.weak henv.ordered (B := D.subst σ₁)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using h
    have H' := HB
    rw [show (b.lift' ρ).lift.app (.bvar 0) =
        (VExpr.app b.lift (.bvar 0)).lift' ρ.cons by simp [lift', lift_lift'_cons]] at H'
    have hright' : D.subst σ₁ :: Γ ⊢ (VExpr.app b.lift (.bvar 0)).subst σ₂.lift : B₁ := by
      simpa only [subst, Subst.lift, lift_subst_lift] using hright
    obtain ⟨_, hB₁⟩ := hbody.isType henv.ordered hΓD
    obtain ⟨_, HB₀⟩ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hbody hright' H' ⟨_, hB₁⟩
    simp only [subst, Subst.lift, lift_subst_lift] at HB₀
    exact ⟨_, .etaL hbPi HB₀⟩
  | etaR hf HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    subst hl
    obtain ⟨⟨_, hD⟩, _⟩ := (hf.isType henv.ordered hΔ).forallE_inv henv.ordered
    obtain ⟨B₂, hPi, hbody⟩ := hb.lam_inv_forallE henv hΓ
    have haPi : Γ ⊢ a.subst σ₁ : .forallE (D.subst σ₂) B₂ :=
      ha.defeqU_r henv hΓ (hmode.trans henv hΓ hPi.symm)
    obtain ⟨⟨_, hD₀⟩, _⟩ := (haPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓD : OnCtx (D.subst σ₂ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₂).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₂).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    have hfAmbient := hf.subst henv S₁.typed hΓ₁
    rw [S₁.apply] at hfAmbient
    obtain ⟨⟨_, hdomains⟩, _⟩ := (hfAmbient.uniqU henv hΓ₁ (haPi.weak' henv S₁.context)).forallE_inv henv hΓ₁
    have SS₁ := S₁.lift_at (D := D.subst σ₂) hΓ₁ hD ⟨_, hdomains⟩
    have SS₂ := S₂.lift_template hΓ₂ hD
    have hleft : D.subst σ₂ :: Γ ⊢ .app (a.subst σ₁).lift (.bvar 0) : B₂ := by
      have h := HasType.app (haPi.weak henv.ordered (B := D.subst σ₂)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using h
    have H' := HB
    rw [show (a.lift' ρ).lift.app (.bvar 0) =
        (VExpr.app a.lift (.bvar 0)).lift' ρ.cons by simp [lift', lift_lift'_cons]] at H'
    have hleft' : D.subst σ₂ :: Γ ⊢ (VExpr.app a.lift (.bvar 0)).subst σ₁.lift : B₂ := by
      simpa only [subst, Subst.lift, lift_subst_lift] using hleft
    obtain ⟨_, hB₂⟩ := hbody.isType henv.ordered hΓD
    obtain ⟨_, HB₀⟩ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hleft' hbody H' ⟨_, hB₂⟩
    simp only [subst, Subst.lift, lift_subst_lift] at HB₀
    exact ⟨_, .etaR haPi HB₀⟩
  | @etaBoth _ _ Ad Bd _ _ hf hg HB =>
    subst hl hr
    obtain ⟨⟨_, hAd⟩, _⟩ := (hf.isType henv.ordered hΔ).forallE_inv henv.ordered
    have hΔA : OnCtx (Ad :: Δ) (Params.env.IsType univs) := ⟨hΔ, _, hAd⟩
    have hn' : ¬ IsProof (Ad :: Δ) (varSpine (a.lift' ρ.skip) [0]) := by
      intro hproof
      change IsProof (Ad :: Δ) (.app (a.lift' ρ.skip) (.bvar 0)) at hproof
      rw [← lift_lift'_skip] at hproof
      exact hp (S₁.proof_reflect hΓ hΓ₁ ha (IsProof.of_etaBody hΔ hf hproof))
    have H' := HB
    rw [show (a.lift' ρ).lift.app (.bvar 0) =
        varSpine ((a.lift' ρ.skip).lift' .refl) [0] by simp [varSpine, lift_lift'_skip],
      show (b.lift' ρ).lift.app (.bvar 0) =
        varSpine ((b.lift' ρ.skip).lift' .refl) [0] by simp [varSpine, lift_lift'_skip]] at H'
    obtain ⟨k, Ξ, hk, _, hΞ, H''⟩ := BiNormal.spine_inv _ (by simp)
      (Ctx.Lift'.refl : Ctx.Lift' .refl (Ad :: Δ) (Ad :: Δ)) hΔA
      (by simpa only [lift'_refl] using hn') H'
    have hΞ' : OnCtx ((Ξ ++ [Ad]) ++ Δ) (Params.env.IsType univs) := by
      simpa only [List.append_assoc, List.singleton_append] using hΞ
    obtain ⟨Γ₁', κ₁', τ₁', hΓ₁', SS₁⟩ := S₁.extend hΓ₁ hΞ'
    obtain ⟨Γ₂', κ₂', τ₂', hΓ₂', SS₂⟩ := S₂.extend hΓ₂ hΞ'
    have H''' : BiNormal false k ((Ξ ++ [Ad]) ++ Δ)
        (a.lift' (ρ.skipN (Ξ ++ [Ad]).length))
        (b.lift' (ρ.skipN (Ξ ++ [Ad]).length)) := by
      simpa only [← lift'_comp, Lift.comp_skipN, Lift.comp, Lift.skipN_succ',
        List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using H''
    obtain ⟨_, H₀⟩ := ih k (by omega) hΓ hΓ₁' hΓ₂' SS₁ SS₂ Hσ ha hb H''' hp
    exact ⟨_, .promote H₀⟩
  | proofIrrel hP ht _ =>
    subst hl
    exact (hp (S₁.proof_reflect hΓ hΓ₁ ha ⟨_, ht, hP⟩)).elim
  | promote H =>
    subst hl hr
    obtain ⟨_, H₀⟩ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ ha hb H hp
    exact ⟨_, .promote H₀⟩


/-- Extend both suspensions with proof arguments, retaining every bidirectional
comparison rule, including eta. Proof propositions need not align below. -/
theorem BiNormal.suspended_proof_inst
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂) (Hσ : ProofSubstRel Γ σ₁ σ₂)
    (hD : Δ ⊢ D : .sort u) (hp : IsProof Γ p) (hq : IsProof Γ q)
    (hp' : Γ₁ ⊢ p.lift' κ₁ : D.subst τ₁) (hq' : Γ₂ ⊢ q.lift' κ₂ : D.subst τ₂)
    (ha : Γ ⊢ a.subst (σ₁.cons p) : A) (hb : Γ ⊢ b.subst (σ₂.cons q) : B)
    (H : BiNormal mode n (D :: Δ) (a.lift' ρ.cons) (b.lift' ρ.cons))
    (hmode : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a.subst (σ₁.cons p))) :
    ∃ m, BiNormal mode m Γ (a.subst (σ₁.cons p)) (b.subst (σ₂.cons q)) :=
  BiNormal.suspended_reflect n hΓ hΓ₁ hΓ₂ (S₁.cons hD hp') (S₂.cons hD hq')
    (Hσ.cons_proofs hp hq) ha hb H hmode

/-- Contract a suspended pair with distinct bodies and proof arguments. A
common-mode source body certificate suffices; lower beta subject reduction
supplies the independently typed instances. Lambda annotations below may differ. -/
theorem suspended_beta_proofs {body₁ body₂ D₁ D₂ : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂) (Hσ : ProofSubstRel Γ σ₁ σ₂)
    (hD : Δ ⊢ D : .sort u) (hp : IsProof Γ p) (hq : IsProof Γ q)
    (hp' : Γ₁ ⊢ p.lift' κ₁ : D.subst τ₁) (hq' : Γ₂ ⊢ q.lift' κ₂ : D.subst τ₂)
    (ha : Γ ⊢ .app (.lam D₁ (body₁.subst σ₁.lift)) p : A)
    (hb : Γ ⊢ .app (.lam D₂ (body₂.subst σ₂.lift)) q : B)
    (H : BiNormal true n (D :: Δ) (body₁.lift' ρ.cons) (body₂.lift' ρ.cons))
    (hAB : Γ ⊢ A ≡ B) :
    BiBetaJoin true Γ (.app (.lam D₁ (body₁.subst σ₁.lift)) p)
      (.app (.lam D₂ (body₂.subst σ₂.lift)) q) := by
  have ra : BetaRed (.app (.lam D₁ (body₁.subst σ₁.lift)) p) (body₁.subst (σ₁.cons p)) := by
    rw [← inst_lift_cons]
    exact .beta
  have rb : BetaRed (.app (.lam D₂ (body₂.subst σ₂.lift)) q) (body₂.subst (σ₂.cons q)) := by
    rw [← inst_lift_cons]
    exact .beta
  have ha' := ra.simAt henv.orderedStrong henv.betaSubjectReduction hΓ A ha
  have hb' := rb.simAt henv.orderedStrong henv.betaSubjectReduction hΓ B hb
  obtain ⟨_, H₀⟩ := BiNormal.suspended_proof_inst hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hD hp hq hp' hq'
    ha'.hasType.2 hb'.hasType.2 H hAB
  exact ⟨_, _, _, ra, rb, H₀⟩

end Lean4Lean.VEnv.Strengthening
