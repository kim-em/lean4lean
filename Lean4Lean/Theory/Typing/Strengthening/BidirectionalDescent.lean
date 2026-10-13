import Lean4Lean.Theory.Typing.Strengthening.BidirectionalNormal

/-! # Descent of mode-indexed normal comparison

Common-type comparisons descend using equality of endpoint types below.
Independent comparisons descend for non-proof endpoints without that equality,
including matched lambdas whose domains have eta-aware common-type certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Peeling a nonempty variable spine reaches an independent-mode comparison.
Eta-both extends the spine; promotion and application decrease the index. -/
theorem BiNormal.spine_inv : ∀ n {mode : Bool} {ρ : Lift} {Γ Γ' : List VExpr}
    {e e' : VExpr} {vs : List Nat}, vs ≠ [] →
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ' (Params.env.IsType univs) →
    ¬ IsProof Γ' (varSpine (e.lift' ρ) vs) →
    BiNormal mode n Γ' (varSpine (e.lift' ρ) vs) (varSpine (e'.lift' ρ) vs) →
    ∃ k, ∃ Δ : List VExpr, k ≤ n ∧ Ctx.Lift' (ρ.skipN Δ.length) Γ (Δ ++ Γ') ∧
      OnCtx (Δ ++ Γ') (Params.env.IsType univs) ∧
      BiNormal false k (Δ ++ Γ') (e.lift' (ρ.skipN Δ.length)) (e'.lift' (ρ.skipN Δ.length)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mode ρ Γ Γ' e e' vs hvs W hΓ' hn H
  cases vs with
  | nil => exact (hvs rfl).elim
  | cons v vs =>
  simp only [varSpine] at H hn
  generalize hl : VExpr.app (varSpine (e.lift' ρ) vs) (.bvar v) = l at H
  generalize hr : VExpr.app (varSpine (e'.lift' ρ) vs) (.bvar v) = r at H
  cases H with
  | refl ht =>
    subst hl
    have hee : e.lift' ρ = e'.lift' ρ := (varSpine_inj (VExpr.app.inj hr).1).symm
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ'
    obtain ⟨_, ht⟩ := varSpine_fn_typed hΓ' hf
    refine ⟨0, [], Nat.zero_le _, W, hΓ', ?_⟩
    simp only [List.length_nil, Lift.skipN, List.nil_append]
    rw [← hee]
    exact .refl ht
  | appDF hf₁ _ ha₁ _ H₁ _ =>
    cases hl; cases hr
    cases vs with
    | nil => exact ⟨_, [], by omega, W, hΓ', H₁⟩
    | cons w ws =>
      obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := ih _ (by omega) (by simp) W hΓ'
        (not_isProof_fn hΓ' hf₁ ha₁ hn) H₁
      exact ⟨k, Δ, by omega, W', hΓ'', H'⟩
  | @etaBoth _ _ A B _ _ he _ Hb =>
    subst hl hr
    obtain ⟨⟨_, hA⟩, _⟩ := (he.isType henv hΓ').forallE_inv henv
    have hΓA : OnCtx (A :: Γ') (Params.env.IsType univs) := ⟨hΓ', _, hA⟩
    change BiNormal true _ (A :: Γ')
      ((varSpine (e.lift' ρ) (v :: vs)).lift.app (.bvar 0))
      ((varSpine (e'.lift' ρ) (v :: vs)).lift.app (.bvar 0)) at Hb
    rw [varSpine_lift, varSpine_lift] at Hb
    have hn' : ¬ IsProof (A :: Γ') (varSpine (e.lift' ρ.skip) (0 :: (v :: vs).map (· + 1))) := by
      intro hp
      change IsProof (A :: Γ') (.app (varSpine (e.lift' ρ.skip) ((v :: vs).map (· + 1))) (.bvar 0)) at hp
      rw [← varSpine_lift] at hp
      exact hn (IsProof.of_etaBody hΓ' he hp)
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := ih _ (by omega) (by simp) (W.skip (A := A)) hΓA hn'
      (show BiNormal true _ (A :: Γ')
        (varSpine (e.lift' ρ.skip) (0 :: (v :: vs).map (· + 1)))
        (varSpine (e'.lift' ρ.skip) (0 :: (v :: vs).map (· + 1))) from Hb)
    refine ⟨k, Δ ++ [A], by omega, ?_, ?_, ?_⟩
    all_goals simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append, ← Lift.skipN_succ']
    · exact W'
    · exact hΓ''
    · exact H'
  | promote H =>
    subst hl hr
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := ih _ (by omega) (vs := v :: vs)
      (e := e) (e' := e') (by simp) W hΓ' hn H
    exact ⟨k, Δ, by omega, W', hΓ'', H'⟩
  | proofIrrel hp ht _ => subst hl; exact (hn ⟨_, ht, hp⟩).elim
  | sortDF | constDF | projDF | lamIndependent | lamCommon | forallEDF | etaL => cases hl
  | etaR => cases hr

private theorem lifted_sort_types (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : Γ ⊢ a : .sort u) (hb : Γ ⊢ b : .sort v) (H : Γ' ⊢ a.lift' ρ ≡ b.lift' ρ) :
    Γ ⊢ .sort u ≡ .sort v := by
  have huv := ((H.of_l henv hΓ' (ha.weak' henv W)).uniqU henv hΓ' (hb.weak' henv W)).sort_inv henv hΓ'
  exact ⟨_, IsDefEq.sortDF (ha.sort_r henv hΓ) (hb.sort_r henv hΓ) huv⟩

/-- The two modes have their advertised descent property. In common-type mode,
the endpoint types must be convertible below. Independent mode instead requires
that the left endpoint is not a proof, and admits lambdas with certified domains. -/
theorem BiNormal.descend : ∀ n {mode ρ Γ Γ' a b A B},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    (Γ ⊢ a : A) → (Γ ⊢ b : B) → BiNormal mode n Γ' (a.lift' ρ) (b.lift' ρ) →
    (if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ a) → Γ ⊢ a ≡ b := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mode ρ Γ Γ' a b A B W hΓ hΓ' ha hb H hmode
  by_cases hp : IsProof Γ a
  · cases mode with
    | false => exact (hmode hp).elim
    | true => exact IsProof.descend hΓ hp ha hb hmode
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  cases H with
  | refl _ =>
    cases lift'_inj.1 (hl.trans hr.symm)
    exact ⟨_, ha⟩
  | sortDF h1 h2 h3 =>
    cases lift'_eq_sort hl; cases lift'_eq_sort hr
    exact ⟨_, IsDefEq.sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    cases lift'_eq_const hl; cases lift'_eq_const hr
    exact ⟨_, IsDefEq.constDF h1 h2 h3 h4 h5⟩
  | appDF _ _ _ _ Hf Hx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have Hff := ih _ (by omega) W hΓ hΓ' hf hf' Hf (not_isProof_fn hΓ hf hx hp)
    have hfPi := Hff.of_l henv hΓ hf
    obtain ⟨⟨_, hD⟩, _⟩ := (hfPi.uniqU henv hΓ hf').forallE_inv henv hΓ
    have Hxx := ih _ (by omega) W hΓ hΓ' hx hx' Hx ⟨_, hD⟩
    exact ⟨_, IsDefEq.appDF hfPi (Hxx.of_l henv hΓ hx)⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel, hinfo, hlevels,
      huvars, hparams, hindices, hfield, hfieldTyping, hmajor, hclosed, hguard⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor', _, _⟩ := hb.proj_inv henv hΓ
    have Hm' := ih _ (by omega) W hΓ hΓ' hmajor.hasType.2 hmajor'.hasType.2 Hm
      (not_isProof_major hΓ ha hp)
    exact ⟨_, IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping hmajor
      (hmajor.trans_l henv hΓ (Hm'.of_l henv hΓ hmajor.hasType.2)) hclosed hguard⟩
  | lamIndependent _ HD HB =>
    obtain ⟨D, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨⟨u, hD⟩, _, hb₁⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hb₂⟩ := hb.lam_inv henv hΓ
    have hDD := (ih _ (by omega) W hΓ hΓ' hD hD' HD
      (lifted_sort_types hΓ hΓ' W hD hD' (HD.defeq hΓ'))).of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.lift' ρ :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hD.weak' henv W⟩
    have hb₂' := hb₂.defeqDFC henv (.succ .zero hDD.symm)
    have Hbb := ih _ (by omega) W.cons hΓD hΓD' hb₁ hb₂' HB (fun h => hp (h.lam hΓ hD))
    exact ⟨_, IsDefEq.lamDF hDD (Hbb.of_l henv hΓD hb₁)⟩
  | lamCommon hD _ HB =>
    obtain ⟨D, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨B₁, hPi₁, hb₁⟩ := ha.lam_inv_forallE henv hΓ
    obtain ⟨B₂, hPi₂, hb₂⟩ := hb.lam_inv_forallE henv hΓ
    have hPiPi := (hPi₁.trans henv hΓ hmode).trans henv hΓ hPi₂.symm
    obtain ⟨⟨u, hDD⟩, _, hBB⟩ := hPiPi.forallE_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hDD.hasType.1⟩
    have hΓD' : OnCtx (D.lift' ρ :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hDD.hasType.1.weak' henv W⟩
    have hb₂' := hb₂.defeqDFC henv (.succ .zero hDD.symm)
    have HB' := HB.defeqDFC hΓ' (.succ .zero hD)
    have Hbb := ih _ (by omega) W.cons hΓD hΓD' hb₁ hb₂' HB' ⟨_, hBB⟩
    exact ⟨_, IsDefEq.lamDF hDD (Hbb.of_l henv hΓD hb₁)⟩
  | forallEDF _ HD _ HB =>
    obtain ⟨D, B₁, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨D', B₂, rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨u, hD⟩, _, hB₁⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hB₂⟩ := hb.forallE_inv henv
    have hDD := (ih _ (by omega) W hΓ hΓ' hD hD' HD
      (lifted_sort_types hΓ hΓ' W hD hD' (HD.defeq hΓ'))).of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.lift' ρ :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hD.weak' henv W⟩
    have hB₂' := hB₂.defeqDFC henv (.succ .zero hDD.symm)
    have HBB := ih _ (by omega) W.cons hΓD hΓD' hB₁ hB₂' HB
      (lifted_sort_types hΓD hΓD' W.cons hB₁ hB₂' (HB.defeq hΓD'))
    exact ⟨_, IsDefEq.forallEDF hDD (HBB.of_l henv hΓD hB₁)⟩
  | etaL he' Hb =>
    obtain ⟨A₀, e₀, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    subst hr
    have hAB := hmode
    obtain ⟨B₁, hPi₁, he₀⟩ := ha.lam_inv_forallE henv hΓ
    have hbPi : Γ ⊢ b : .forallE A₀ B₁ := hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hPi₁.symm)
    obtain ⟨⟨u, hA₀⟩, -⟩ := (hbPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA₀.weak' henv W⟩
    have hbody : A₀ :: Γ ⊢ .app b.lift (.bvar 0) : B₁ := by
      have := HasType.app (hbPi.weak henv.ordered (B := A₀)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using this
    have Hb' := Hb
    rw [show (b.lift' ρ).lift.app (.bvar 0) = (VExpr.app b.lift (.bvar 0)).lift' ρ.cons by
      simp [lift', lift_lift'_cons]] at Hb'
    obtain ⟨w, hB₁s⟩ := he₀.isType henv.ordered hΓA
    have hee := (ih _ (by omega) W.cons hΓA hΓA' he₀ hbody Hb') ⟨_, hB₁s⟩
    have h1 : Γ ⊢ .lam A₀ e₀ ≡ .lam A₀ (.app b.lift (.bvar 0)) : .forallE A₀ B₁ :=
      .lamDF hA₀ (hee.of_l henv hΓA he₀)
    exact ⟨_, h1.trans (IsDefEq.eta hbPi)⟩
  | etaR he Hb =>
    obtain ⟨A₂, e₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    subst hl
    have hAB := hmode
    obtain ⟨B₂, hPi₂, he₂⟩ := hb.lam_inv_forallE henv hΓ
    have haPi : Γ ⊢ a : .forallE A₂ B₂ := ha.defeqU_r henv hΓ (hAB.trans henv hΓ hPi₂.symm)
    obtain ⟨⟨u, hA₂⟩, -⟩ := (haPi.isType henv.ordered hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A₂ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA₂⟩
    have hΓA' : OnCtx (A₂.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA₂.weak' henv W⟩
    have hbody : A₂ :: Γ ⊢ .app a.lift (.bvar 0) : B₂ := by
      have := HasType.app (haPi.weak henv.ordered (B := A₂)) (.bvar .zero)
      simpa only [lift, liftN, inst_liftN_bvar] using this
    have Hb' := Hb
    rw [show (a.lift' ρ).lift.app (.bvar 0) = (VExpr.app a.lift (.bvar 0)).lift' ρ.cons by
      simp [lift', lift_lift'_cons]] at Hb'
    obtain ⟨w, hB₂s⟩ := he₂.isType henv.ordered hΓA
    have hnb : ¬ IsProof (A₂ :: Γ) (.app a.lift (.bvar 0)) := fun hproof =>
      hp (IsProof.of_etaBody hΓ haPi hproof)
    have hee := (ih _ (by omega) W.cons hΓA hΓA' hbody he₂ Hb') ⟨_, hB₂s⟩
    have h1 : Γ ⊢ .lam A₂ (.app a.lift (.bvar 0)) ≡ .lam A₂ e₂ : .forallE A₂ B₂ :=
      .lamDF hA₂ (hee.of_l henv hΓA hbody)
    exact ⟨_, (IsDefEq.eta haPi).symm.trans h1⟩
  | @etaBoth _ _ Ad Bd _ _ he he' Hb =>
    subst hl hr
    obtain ⟨⟨u, hAd⟩, -⟩ := (he.isType henv.ordered hΓ').forallE_inv henv.ordered
    have hΓA' : OnCtx (Ad :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hAd⟩
    have hn' : ¬ IsProof (Ad :: Γ') (varSpine (a.lift' ρ.skip) [0]) := by
      intro hproof
      change IsProof (Ad :: Γ') (.app (a.lift' ρ.skip) (.bvar 0)) at hproof
      rw [← lift_lift'_skip] at hproof
      obtain ⟨P, hproof, hP⟩ := IsProof.of_etaBody hΓ' he hproof
      exact hp (IsProof.of_lift hΓ hΓ' W ha hP hproof)
    have Hb' := Hb
    rw [show (a.lift' ρ).lift.app (.bvar 0) = varSpine (a.lift' ρ.skip) [0] by
        simp [varSpine, lift_lift'_skip],
      show (b.lift' ρ).lift.app (.bvar 0) = varSpine (b.lift' ρ.skip) [0] by
        simp [varSpine, lift_lift'_skip]] at Hb'
    obtain ⟨k, Δ, hk, W', hΓ'', H'⟩ := BiNormal.spine_inv _ (by simp) (W.skip (A := Ad)) hΓA' hn' Hb'
    exact ih k (by omega) W' hΓ hΓ'' ha hb H' hp
  | proofIrrel hP hl' _ =>
    subst hl
    exact (hp (IsProof.of_lift hΓ hΓ' W ha hP hl')).elim
  | promote H =>
    subst hl hr
    exact ih _ (by omega) W hΓ hΓ' ha hb H hp

end Lean4Lean.VEnv.Strengthening
