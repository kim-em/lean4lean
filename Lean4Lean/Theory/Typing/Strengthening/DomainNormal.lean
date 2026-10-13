import Lean4Lean.Theory.Typing.Strengthening.DescentSupport

/-! # Normal comparisons with explicit lambda-domain comparisons

`DomainNormal` is the eta-free normal comparison with recursive domain comparisons
at lambda nodes. Unlike `NormalEqN.lamDF`, it cannot hide an arbitrary declarative
domain conversion at index one. Both the domain and body contribute to the index.
Unlike route A's strict relation, it permits beta-redexes in function position.

This is a comparison relation, not a new presentation of all definitional equality.
Completeness for the full calculus, including eta, is not assumed.
-/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Eta-free normal equality with structurally compared lambda domains.
Opaque typing witnesses remain, but the displayed domain equality is a subderivation. -/
inductive DomainNormal : Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → DomainNormal 0 Γ e e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ →
      DomainNormal 0 Γ (.sort l₁) (.sort l₂)
  | constDF : Params.env.constants c = some ci →
      (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → DomainNormal 0 Γ (.const c ls) (.const c ls')
  | appDF : Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
      Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
      DomainNormal nf Γ f₁ f₂ → DomainNormal na Γ a₁ a₂ →
      DomainNormal (nf + na + 1) Γ (.app f₁ a₁) (.app f₂ a₂)
  | projDF : Γ ⊢ .proj S i m : T → DomainNormal n Γ m m' →
      DomainNormal (n + 1) Γ (.proj S i m) (.proj S i m')
  | lamDF : Γ ⊢ A₁ : .sort u → DomainNormal nd Γ A₁ A₂ →
      DomainNormal nb (A₁ :: Γ) b₁ b₂ →
      DomainNormal (nd + nb + 1) Γ (.lam A₁ b₁) (.lam A₂ b₂)
  | forallEDF : Γ ⊢ A₁ : .sort u → DomainNormal nd Γ A₁ A₂ →
      A₁ :: Γ ⊢ B₁ : .sort v → DomainNormal nb (A₁ :: Γ) B₁ B₂ →
      DomainNormal (nd + nb + 1) Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | proofIrrel : Γ ⊢ P : .sort .zero → Γ ⊢ a : P → Γ ⊢ b : P → DomainNormal 0 Γ a b

/-- Forget the extra domain structure, obtaining the existing normal equality. -/
theorem DomainNormal.toNormal (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DomainNormal n Γ a b) : NormalEqF false Γ a b := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 (ih1 hΓ) (ih2 hΓ)
  | projDF h _ ih => exact .projDF h (ih hΓ)
  | lamDF hA _ _ ihA ihb =>
    exact .lamDF hA (((ihA hΓ).defeq hΓ).of_l henv hΓ hA) (ihb ⟨hΓ, _, hA⟩)
  | forallEDF hA _ hB _ ihA ihB => exact .forallEDF hA (ihA hΓ) hB (ihB ⟨hΓ, _, hA⟩)
  | proofIrrel hP ha hb => exact .proofIrrel hP ha hb

theorem DomainNormal.defeq (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DomainNormal n Γ a b) : Γ ⊢ a ≡ b := (H.toNormal hΓ).defeq hΓ

/-- Context conversion preserves the comparison index, including domain nodes. -/
theorem DomainNormal.defeqDFC (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (H : DomainNormal n Γ₁ a b) : DomainNormal n Γ₂ a b := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (h.defeqDFC henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.defeqDFC henv W) (h2.defeqDFC henv W)
      (h3.defeqDFC henv W) (h4.defeqDFC henv W) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.defeqDFC henv W) (ih W)
  | lamDF hA _ _ ihA ihb => exact .lamDF (hA.defeqDFC henv W) (ihA W) (ihb (.succ W hA))
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.defeqDFC henv W) (ihA W) (hB.defeqDFC henv (.succ W hA))
      (ihB (.succ W hA))
  | proofIrrel hP ha hb =>
    exact .proofIrrel (hP.defeqDFC henv W) (ha.defeqDFC henv W) (hb.defeqDFC henv W)

/-- Homogeneous substitution retains every recursively recorded domain comparison.
Its index is unchanged even when a substituted lambda creates a beta redex. -/
theorem DomainNormal.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ₂) (he₀ : Γ₀ ⊢ e₀ : A₀)
    (H : DomainNormal n Γ₁ a b) : DomainNormal n Γ₂ (a.inst e₀ k) (b.inst e₀ k) := by
  induction H generalizing k Γ₂ with
  | refl h => exact .refl (h.instN henv.ordered W he₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv.ordered W he₀) (h2.instN henv.ordered W he₀)
      (h3.instN henv.ordered W he₀) (h4.instN henv.ordered W he₀) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.instN henv.ordered W he₀) (ih W)
  | lamDF hA _ _ ihA ihb => exact .lamDF (hA.instN henv.ordered W he₀) (ihA W) (ihb W.succ)
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.instN henv.ordered W he₀) (ihA W)
      (hB.instN henv.ordered W.succ he₀) (ihB W.succ)
  | proofIrrel hP ha hb =>
    exact .proofIrrel (hP.instN henv.ordered W he₀) (ha.instN henv.ordered W he₀)
      (hb.instN henv.ordered W he₀)

/-- Recursive domain certificates reflect along lifts in common-type mode, or
independently for a non-proof endpoint. Unlike `descend`, the conclusion preserves
the syntactic comparison invariant. It does not strengthen arbitrary typings. -/
theorem DomainNormal.reflect : ∀ n {ρ : Lift} {Γ Γ' : List VExpr} {a b A B : VExpr},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Γ ⊢ a : A → Γ ⊢ b : B → DomainNormal n Γ' (a.lift' ρ) (b.lift' ρ) →
    (Γ ⊢ A ≡ B → ∃ m, DomainNormal m Γ a b) ∧
    (¬ IsProof Γ a → ∃ m, DomainNormal m Γ a b) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro ρ Γ Γ' a b A B W hΓ hΓ' ha hb H
  suffices core : ¬ IsProof Γ a → ∃ m, DomainNormal m Γ a b by
    refine ⟨fun hAB => ?_, core⟩
    by_cases hp : IsProof Γ a
    · obtain ⟨P, haP, hP⟩ := hp
      have hAP := ha.uniqU henv hΓ haP
      have hbP := hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP)
      exact ⟨_, .proofIrrel hP haP hbP⟩
    · exact core hp
  intro hna
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  cases H with
  | refl _ =>
    cases lift'_inj.1 (hl.trans hr.symm)
    exact ⟨_, .refl ha⟩
  | sortDF h1 h2 h3 =>
    cases lift'_eq_sort hl; cases lift'_eq_sort hr
    exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    cases lift'_eq_const hl; cases lift'_eq_const hr
    exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF _ _ _ _ Hf Hx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f', x', rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨A₁, B₁, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨A₂, B₂, hf', hx'⟩ := hb.app_inv henv hΓ
    obtain ⟨_, HF⟩ := (ih _ (by omega) W hΓ hΓ' hf hf' Hf).2 (not_isProof_fn hΓ hf hx hna)
    have hfPi := (HF.defeq hΓ).of_l henv hΓ hf
    obtain ⟨⟨u, hA₁₂⟩, -⟩ := (hfPi.uniqU henv hΓ hf').forallE_inv henv hΓ
    obtain ⟨_, HX⟩ := (ih _ (by omega) W hΓ hΓ' hx hx' Hx).1 ⟨_, hA₁₂⟩
    exact ⟨_, .appDF hf hfPi.hasType.2 hx ((HX.defeq hΓ).of_l henv hΓ hx).hasType.2 HF HX⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor', _, _⟩ := hb.proj_inv henv hΓ
    obtain ⟨_, HM⟩ := (ih _ (by omega) W hΓ hΓ' hmajor.hasType.2 hmajor'.hasType.2 Hm).2
      (not_isProof_major hΓ ha hna)
    exact ⟨_, .projDF ha HM⟩
  | lamDF _ HA Hb =>
    obtain ⟨A₀, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨A₂, b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨⟨u₀, hA₀⟩, _, hb₁⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨u₂, hA₂⟩, _, hb₂⟩ := hb.lam_inv henv hΓ
    obtain ⟨_, HD⟩ := (ih _ (by omega) W hΓ hΓ' hA₀ hA₂ HA).2 (not_isProof_of_sort hΓ hA₀)
    have hA₀₂ := (HD.defeq hΓ).of_l henv hΓ hA₀
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u₀, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u₀, hA₀.weak' henv W⟩
    have hb₂' := hb₂.defeqDFC henv (.succ .zero hA₀₂.symm)
    have hnb : ¬ IsProof (A₀ :: Γ) b₁ := fun hp => hna (hp.lam hΓ hA₀)
    obtain ⟨_, HB⟩ := (ih _ (by omega) W.cons hΓA hΓA' hb₁ hb₂' Hb).2 hnb
    exact ⟨_, .lamDF hA₀ HD HB⟩
  | forallEDF _ HA _ HB =>
    obtain ⟨A₀, B₁, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨A₂, B₂, rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨u₀, hA₀⟩, v₀, hB₁⟩ := ha.forallE_inv henv.ordered
    obtain ⟨⟨u₂, hA₂⟩, v₂, hB₂⟩ := hb.forallE_inv henv.ordered
    obtain ⟨_, HD⟩ := (ih _ (by omega) W hΓ hΓ' hA₀ hA₂ HA).2 (not_isProof_of_sort hΓ hA₀)
    have hA₀₂ := (HD.defeq hΓ).of_l henv hΓ hA₀
    have hΓA : OnCtx (A₀ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u₀, hA₀⟩
    have hΓA' : OnCtx (A₀.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u₀, hA₀.weak' henv W⟩
    have hB₂' := hB₂.defeqDFC henv (.succ .zero hA₀₂.symm)
    obtain ⟨_, HB⟩ := (ih _ (by omega) W.cons hΓA hΓA' hB₁ hB₂' HB).2 (not_isProof_of_sort hΓA hB₁)
    exact ⟨_, .forallEDF hA₀ HD hB₁ HB⟩
  | proofIrrel hp hl' _ =>
    subst hl
    exact (hna (IsProof.of_lift hΓ hΓ' W ha hp hl')).elim

/-- Descent in two modes: convertible endpoint types, or a non-proof left endpoint.
The independent mode includes lambdas because their domains are recursively compared.
No canonical-Eq hypothesis or strengthening principle is used. -/
theorem DomainNormal.descend (n : Nat) {ρ : Lift} {Γ Γ' : List VExpr} {a b A B : VExpr}
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B)
    (H : DomainNormal n Γ' (a.lift' ρ) (b.lift' ρ)) :
    (Γ ⊢ A ≡ B → Γ ⊢ a ≡ b) ∧ (¬ IsProof Γ a → Γ ⊢ a ≡ b) := by
  have hs := DomainNormal.reflect n W hΓ hΓ' ha hb H
  exact ⟨fun h => let ⟨_, H⟩ := hs.1 h; H.defeq hΓ,
    fun h => let ⟨_, H⟩ := hs.2 h; H.defeq hΓ⟩

end Lean4Lean.VEnv.Strengthening
