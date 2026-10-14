import Lean4Lean.Theory.Typing.Strengthening.SuspendedBidirectional

/-! # Comparing independently typed substitution instances

A raw template need not have a typing in an open smaller context. If two of its
instances are independently typed, pointwise convertible substitution values may
be mixed with arbitrary pairs of proofs. The propositions of those proof pairs
need not align in advance. Typing of the surrounding application aligns them at
each use. Lambda annotations are traversed, not erased.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Substitution entries either coincide literally, are already convertible
below, or are both proofs.
Literal equality permits unused untyped entries beyond the context. The proof
alternative requires no conversion of the two propositions. -/
def DefEqProofSubstRel (Γ : List VExpr) (σ τ : Subst) : Prop :=
  ∀ i, σ i = τ i ∨ (Γ ⊢ σ i ≡ τ i) ∨
    (IsProof Γ (σ i) ∧ IsProof Γ (τ i))

/-- Identical substitutions need no typing of their unused entries. -/
theorem DefEqProofSubstRel.refl (σ : Subst) : DefEqProofSubstRel Γ σ σ :=
  fun _ => .inl rfl

/-- Add a pair of proof arguments, even at unrelated propositions. -/
theorem DefEqProofSubstRel.cons_proofs (H : DefEqProofSubstRel Γ σ τ)
    (hp : IsProof Γ p) (hq : IsProof Γ q) : DefEqProofSubstRel Γ (σ.cons p) (τ.cons q) := by
  intro i
  cases i with
  | zero => exact .inr (.inr ⟨hp, hq⟩)
  | succ i => exact H i

/-- Opening a binder preserves the relation, independently of its domain. -/
theorem DefEqProofSubstRel.lift (H : DefEqProofSubstRel Γ σ τ) :
    DefEqProofSubstRel (D :: Γ) σ.lift τ.lift := by
  intro i
  cases i with
  | zero => exact .inl rfl
  | succ i =>
    rcases H i with h | h | ⟨⟨P, hp, hP⟩, ⟨Q, hq, hQ⟩⟩
    · exact .inl (congrArg VExpr.lift h)
    · exact .inr (.inl (h.weak henv))
    · exact .inr (.inr ⟨⟨P.lift, hp.weak henv, hP.weak henv⟩,
        ⟨Q.lift, hq.weak henv, hQ.weak henv⟩⟩)

/-- Independently typed non-proof instances are convertible under pointwise
convertible entries and arbitrary proof pairs. No open typing for the template
or common type for its instances is assumed. Arbitrary lambda arguments can be
kept as entries once their conversion has been established below. -/
theorem subst_defeq_nonproof (e : VExpr) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DefEqProofSubstRel Γ σ τ) (ha : Γ ⊢ e.subst σ : A) (hb : Γ ⊢ e.subst τ : B)
    (hn : ¬ IsProof Γ (e.subst σ)) : Γ ⊢ e.subst σ ≡ e.subst τ := by
  induction e generalizing Γ σ τ A B with
  | bvar i =>
    rcases H i with h | h | h
    · simpa only [subst_bvar, h] using
        (show Γ ⊢ σ i ≡ σ i from ⟨_, ha⟩)
    · exact h
    · exact (hn h.1).elim
  | sort | const => exact ⟨_, ha⟩
  | app f x ihf ihx =>
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have HF := ihf hΓ H hf hf' (not_isProof_fn hΓ hf hx hn)
    have hff := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX : Γ ⊢ x.subst σ ≡ x.subst τ := by
      by_cases hp : IsProof Γ (x.subst σ)
      · obtain ⟨P, hxP, hP⟩ := hp
        have hAP := hx.uniqU henv hΓ hxP
        have hx'P := hx'.defeqU_r henv hΓ
          ((show Γ ⊢ _ ≡ _ from ⟨_, hDD⟩).symm.trans henv hΓ hAP)
        exact ⟨_, .proofIrrel hP hxP hx'P⟩
      · exact ihx hΓ H hx hx' hp
    exact ⟨_, IsDefEq.appDF hff (HX.of_l henv hΓ hx)⟩
  | proj s i m ih =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel, hinfo, hlevels,
      huvars, hparams, hindices, hfield, hfieldTyping, hm, hclosed, hguard⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := ih hΓ H hm.hasType.2 hm'.hasType.2 (not_isProof_major hΓ ha hn)
    exact ⟨_, IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping hm
      (hm.trans_l henv hΓ (HM.of_l henv hΓ hm.hasType.2)) hclosed hguard⟩
  | lam D body ihD ihb =>
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    have HD := ihD hΓ H hD hD' (not_isProof_of_sort hΓ hD)
    have hDD := HD.of_l henv hΓ hD
    have W := IsDefEqCtx.succ .zero hDD.symm
    have hbody'' := hbody'.defeqDFC henv W
    have HB := ihb (Γ := D.subst σ :: Γ) ⟨hΓ, _, hD⟩ H.lift hbody hbody''
      (fun hp => hn (hp.lam hΓ hD))
    exact ⟨_, IsDefEq.lamDF hDD (HB.of_l henv ⟨hΓ, _, hD⟩ hbody)⟩
  | forallE D body ihD ihb =>
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.forallE_inv henv
    have HD := ihD hΓ H hD hD' (not_isProof_of_sort hΓ hD)
    have hDD := HD.of_l henv hΓ hD
    have W := IsDefEqCtx.succ .zero hDD.symm
    have hbody'' := hbody'.defeqDFC henv W
    have HB := ihb (Γ := D.subst σ :: Γ) ⟨hΓ, _, hD⟩ H.lift hbody hbody''
      (not_isProof_of_sort ⟨hΓ, _, hD⟩ hbody)
    exact ⟨_, IsDefEq.forallEDF hDD (HB.of_l henv ⟨hΓ, _, hD⟩ hbody)⟩

/-- At convertible endpoint types, proof instances are covered as well. -/
theorem subst_defeq_common (e : VExpr) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DefEqProofSubstRel Γ σ τ) (ha : Γ ⊢ e.subst σ : A) (hb : Γ ⊢ e.subst τ : B)
    (hAB : Γ ⊢ A ≡ B) : Γ ⊢ e.subst σ ≡ e.subst τ := by
  by_cases hp : IsProof Γ (e.subst σ)
  · obtain ⟨P, haP, hP⟩ := hp
    have hAP := ha.uniqU henv hΓ haP
    exact ⟨_, .proofIrrel hP haP (hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP))⟩
  · exact subst_defeq_nonproof e hΓ H ha hb hp

/-- Any already established lower conversion can be suspended as one entry;
its certificate shape and the syntactic form of its endpoints are irrelevant. -/
theorem DefEqProofSubstRel.cons_defeq (H : DefEqProofSubstRel Γ σ τ)
    (hpq : Γ ⊢ p ≡ q) : DefEqProofSubstRel Γ (σ.cons p) (τ.cons q) := by
  intro i
  cases i with
  | zero => exact .inr (.inl hpq)
  | succ i => exact H i

/-- Mode-indexed comparisons remain convertible after suspending arbitrary
already-convertible arguments and unrelated proof pairs. Separate ambient
realizations handle eta prefixes without open smaller template typings. Unlike
certificate preservation, this can use opaque lower equalities at variable leaves. -/
theorem BiNormal.suspended_defeq : ∀ n {mode : Bool} {Γ Γ₁ Γ₂ Δ : List VExpr}
    {ρ κ₁ κ₂ : Lift} {σ₁ σ₂ τ₁ τ₂ : Subst} {a b A B : VExpr},
    OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ₁ (Params.env.IsType univs) → OnCtx Γ₂ (Params.env.IsType univs) →
    SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁ → SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂ →
    DefEqProofSubstRel Γ σ₁ σ₂ → (Γ ⊢ a.subst σ₁ : A) → (Γ ⊢ b.subst σ₂ : B) →
    BiNormal mode n Δ (a.lift' ρ) (b.lift' ρ) →
    (if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a.subst σ₁)) →
    Γ ⊢ a.subst σ₁ ≡ b.subst σ₂ := by
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
    exact subst_defeq_nonproof a hΓ Hσ ha hb hp
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
    have HF := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hf hf' Hf
      (not_isProof_fn hΓ hf hx hp)
    have hff := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hx hx' Hx ⟨_, hDD⟩
    exact ⟨_, IsDefEq.appDF hff (HX.of_l henv hΓ hx)⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel, hinfo, hlevels,
      huvars, hparams, hindices, hfield, hfieldTyping, hm, hclosed, hguard⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hm.hasType.2 hm'.hasType.2 Hm
      (not_isProof_major hΓ ha hp)
    exact ⟨_, IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping hm
      (hm.trans_l henv hΓ (HM.of_l henv hΓ hm.hasType.2)) hclosed hguard⟩
  | lamIndependent hD HD HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.lam_inv henv hΓ
    have HC := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hD₀ hD₁ HD
      (suspended_sort_types hΓ hΓ₁ hΓ₂ S₁ S₂ hD (HD.defeq hΔ) hD₀ hD₁)
    have hDD := HC.of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ₁ hD
    have SS₂ := S₂.lift_via_template hΓ₂ hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    have HB₀ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB
      (fun h => hp (h.lam hΓ hD₀))
    exact ⟨_, IsDefEq.lamDF hDD (HB₀.of_l henv hΓD hb₀)⟩
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
    have HB₀ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₁ hb₂' HB ⟨_, hBB⟩
    exact ⟨_, IsDefEq.lamDF hDD (HB₀.of_l henv hΓD hb₁)⟩
  | forallEDF hD HD hBody HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.forallE_inv henv
    have HC := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ hD₀ hD₁ HD
      (suspended_sort_types hΓ hΓ₁ hΓ₂ S₁ S₂ hD (HD.defeq hΔ) hD₀ hD₁)
    have hDD := HC.of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ₁ hD
    have SS₂ := S₂.lift_via_template hΓ₂ hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ₁D : OnCtx ((D.subst σ₁).lift' κ₁ :: Γ₁) (Params.env.IsType univs) :=
      ⟨hΓ₁, _, hD₀.weak' henv S₁.context⟩
    have hΓ₂D : OnCtx ((D.subst σ₁).lift' κ₂ :: Γ₂) (Params.env.IsType univs) :=
      ⟨hΓ₂, _, hD₀.weak' henv S₂.context⟩
    have HB₀ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB
      (suspended_sort_types hΓD hΓ₁D hΓ₂D SS₁ SS₂ hBody (HB.defeq ⟨hΔ, _, hD⟩) hb₀ hb₁')
    exact ⟨_, IsDefEq.forallEDF hDD (HB₀.of_l henv hΓD hb₀)⟩
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
    have HB₀ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hbody hright' H' ⟨_, hB₁⟩
    simp only [subst, Subst.lift, lift_subst_lift] at HB₀
    exact ⟨_, (IsDefEq.lamDF hD₀ (HB₀.of_l henv hΓD hbody)).trans (IsDefEq.eta hbPi)⟩
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
    have HB₀ := ih _ (by omega) hΓD hΓ₁D hΓ₂D SS₁ SS₂ Hσ.lift hleft' hbody H' ⟨_, hB₂⟩
    simp only [subst, Subst.lift, lift_subst_lift] at HB₀
    exact ⟨_, (IsDefEq.eta haPi).symm.trans (IsDefEq.lamDF hD₀ (HB₀.of_l henv hΓD hleft))⟩
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
    have H₀ := ih k (by omega) hΓ hΓ₁' hΓ₂' SS₁ SS₂ Hσ ha hb H''' hp
    exact H₀
  | proofIrrel hP ht _ =>
    subst hl
    exact (hp (S₁.proof_reflect hΓ hΓ₁ ha ⟨_, ht, hP⟩)).elim
  | promote H =>
    subst hl hr
    have H₀ := ih _ (by omega) hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ ha hb H hp
    exact H₀



/-- A delayed beta pair preserves equality once its arguments are already
convertible below, regardless of whether those arguments are lambdas. This does
not derive argument conversion from unrelated lambda typings: that missing
comparison remains a separate obligation. -/
theorem suspended_beta_eq {body₁ body₂ D₁ D₂ : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂) (Hσ : DefEqProofSubstRel Γ σ₁ σ₂)
    (hD : Δ ⊢ D : .sort u) (hpq : Γ ⊢ p ≡ q)
    (hp' : Γ₁ ⊢ p.lift' κ₁ : D.subst τ₁) (hq' : Γ₂ ⊢ q.lift' κ₂ : D.subst τ₂)
    (ha : Γ ⊢ .app (.lam D₁ (body₁.subst σ₁.lift)) p : A)
    (hb : Γ ⊢ .app (.lam D₂ (body₂.subst σ₂.lift)) q : B)
    (H : BiNormal true n (D :: Δ) (body₁.lift' ρ.cons) (body₂.lift' ρ.cons))
    (hAB : Γ ⊢ A ≡ B) :
    Γ ⊢ .app (.lam D₁ (body₁.subst σ₁.lift)) p ≡
      .app (.lam D₂ (body₂.subst σ₂.lift)) q := by
  have ra : BetaRed (.app (.lam D₁ (body₁.subst σ₁.lift)) p) (body₁.subst (σ₁.cons p)) := by
    rw [← inst_lift_cons]
    exact .beta
  have rb : BetaRed (.app (.lam D₂ (body₂.subst σ₂.lift)) q) (body₂.subst (σ₂.cons q)) := by
    rw [← inst_lift_cons]
    exact .beta
  have ha' := ra.simAt henv.orderedStrong henv.betaSubjectReduction hΓ A ha
  have hb' := rb.simAt henv.orderedStrong henv.betaSubjectReduction hΓ B hb
  have H₀ := BiNormal.suspended_defeq n hΓ hΓ₁ hΓ₂ (S₁.cons hD hp') (S₂.cons hD hq')
    (Hσ.cons_defeq hpq) ha'.hasType.2 hb'.hasType.2 H hAB
  exact (show Γ ⊢ _ ≡ _ from ⟨_, ha'⟩).trans henv hΓ
    (H₀.trans henv hΓ ⟨_, hb'.symm⟩)

end Lean4Lean.VEnv.Strengthening
