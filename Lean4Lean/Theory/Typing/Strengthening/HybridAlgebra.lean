import Lean4Lean.Theory.Typing.Strengthening.HybridNormal
import Lean4Lean.Theory.Typing.Strengthening.DomainNormalAlgebra

/-! # Selective comparisons under binders and substitution

Variable rigidity addresses the case where substitution exposes a lambda at an
application's function. This file does not assume arbitrary heterogeneous closure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

omit [Params] in
theorem IsLam.liftN_iff {e : VExpr} : IsLam (e.liftN n k) ↔ IsLam e := by
  cases e <;> simp [IsLam, liftN]

/-- Symmetry retains the application certificates and the index. -/
theorem HybridNormal.symm (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : HybridNormal n Γ a b) : HybridNormal n Γ b a := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF hs h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (hs.imp And.symm (fun ⟨_, H⟩ => ⟨_, H.symm hΓ⟩)) h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | projDF hproj hMajor ihMajor =>
    have ⟨_, whole⟩ := (HybridNormal.projDF hproj hMajor).defeq hΓ
    exact .projDF whole.hasType.2 (ihMajor hΓ)
  | lamDF h1 h2 _ ih => exact .lamDF h2 h1 (ih ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := ⟨hΓ, _, h1.hasType.1⟩
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaR h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaL h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaBoth h1 h2 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaBoth h2 h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

/-- Weakening preserves selective comparisons and their indices. -/
theorem HybridNormal.weakN (W : Ctx.LiftN k j Γ Γ') (H : HybridNormal n Γ a b) :
    HybridNormal n Γ' (a.liftN k j) (b.liftN k j) := by
  induction H generalizing j Γ' with
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF hs h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (hs.imp
      (fun ⟨h1, h2⟩ => ⟨fun h => h1 (IsLam.liftN_iff.1 h), fun h => h2 (IsLam.liftN_iff.1 h)⟩)
      (fun ⟨_, H⟩ => ⟨_, H.weakN W⟩))
      (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.weakN henv W) (ih W)
  | lamDF h1 h2 _ ih => exact .lamDF (h1.weakN henv W) (h2.weakN henv W) (ih W.succ)
  | forallEDF h1 _ h3 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN henv W) (ih1 W) (h3.weakN henv W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaBoth h1 h2 _ ih =>
    refine .etaBoth (h1.weakN henv W) (h2.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN', lift_liftN']
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)

/-- A non-proof variable can compare with a non-lambda only when the terms are
identical, even after arbitrary context extension and eta-spine expansion. -/
theorem HybridNormal.variable_inv_lift : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {i : Nat} {e T : VExpr},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Γ ⊢ .bvar i : T → ¬ IsProof Γ (.bvar i) → ¬ IsLam e →
    HybridNormal n Γ' ((.bvar i : VExpr).lift' ρ) (e.lift' ρ) → e = .bvar i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro ρ Γ Γ' i e T W hΓ hΓ' hv hnv hne H
  generalize hl : (.bvar i : VExpr).lift' ρ = l at H
  generalize hr : e.lift' ρ = r at H
  cases H with
  | refl => exact (lift'_inj.1 (hl.trans hr.symm)).symm
  | sortDF | constDF | appDF | projDF | lamDF | forallEDF | etaL => cases hl
  | etaR =>
    obtain ⟨_, _, rfl, _, _⟩ := lift'_eq_lam hr
    exact (hne trivial).elim
  | @etaBoth _ _ Ad Bd _ _ he he' Hb =>
    subst hl hr
    obtain ⟨⟨u, hAd⟩, -⟩ := (he.isType henv.ordered hΓ').forallE_inv henv.ordered
    have hΓA' : OnCtx (Ad :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hAd⟩
    have hn' : ¬ IsProof (Ad :: Γ') (varSpine ((.bvar i : VExpr).lift' ρ.skip) [0]) := by
      intro hp
      change IsProof (Ad :: Γ') (.app ((.bvar i : VExpr).lift' ρ.skip) (.bvar 0)) at hp
      rw [← lift_lift'_skip] at hp
      obtain ⟨P, hp, hP⟩ := IsProof.of_etaBody hΓ' he hp
      exact hnv (IsProof.of_lift hΓ hΓ' W hv hP hp)
    have Hb' := Hb
    rw [show ((.bvar i : VExpr).lift' ρ).lift.app (.bvar 0) =
        varSpine ((.bvar i : VExpr).lift' ρ.skip) [0] by simp only [varSpine, lift_lift'_skip],
      show (e.lift' ρ).lift.app (.bvar 0) = varSpine (e.lift' ρ.skip) [0] by
        simp [varSpine, lift_lift'_skip]] at Hb'
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := HybridNormal.spine_inv _ (W.skip (A := Ad)) hΓA' hn' Hb'
    exact ih k (by omega) W' hΓ hΓ'' hv hnv hne H'
  | proofIrrel hp hv' _ =>
    subst hl
    exact (hnv (IsProof.of_lift hΓ hΓ' W hv hp hv')).elim

/-- The unextended variable-rigidity case used when substitution exposes a lambda. -/
theorem HybridNormal.variable_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hv : Γ ⊢ .bvar i : T) (hnv : ¬ IsProof Γ (.bvar i)) (hne : ¬ IsLam e)
    (H : HybridNormal n Γ (.bvar i) e) : e = .bvar i :=
  variable_inv_lift n Ctx.Lift'.refl hΓ hΓ hv hnv hne (by simpa using H)

end Lean4Lean.VEnv.Strengthening
