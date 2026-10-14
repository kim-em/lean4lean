import Lean4Lean.Theory.Typing.Strengthening.HeterogeneousProofSubstitution

/-! # Ambient typing for delayed substitutions

The raw template context need not exist as a typed smaller context. A typed
ambient substitution, commuting with the template renaming and target weakening,
supplies proofness information for each independently typed smaller instance.
The square extends under any binder whose ambient image has the chosen type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {e a b A D : VExpr}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- A typed ambient realization of a raw substitution into a smaller context.
`ρ` embeds raw template variables into `Δ`; `κ` inserts binders into the actual
smaller context. No context or typing is supplied for the raw template itself. -/
structure SubstLiftSquare (Γ Γ' Δ : List VExpr) (ρ κ : Lift) (σ τ : Subst) : Prop where
  context : Ctx.Lift' κ Γ Γ'
  typed : Ctx.SubstEq Params.env univs Γ' τ τ Δ
  commute : ∀ i, τ (ρ.liftVar i) = (σ i).lift' κ

/-- Ordinary weakening starts a suspension with identity substitutions. -/
theorem SubstLiftSquare.initial (W : Ctx.Lift' ρ Γ Γ')
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) :
    SubstLiftSquare Γ Γ' Γ' ρ ρ .id .id where
  context := W
  typed := Ctx.SubstEq.id henv.ordered hΓ'
  commute := fun _ => rfl

/-- Delay a new argument by extending the substitutions. Its type is checked
only in the ambient target; no open smaller-context domain is required. -/
theorem SubstLiftSquare.cons (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hA : Δ ⊢ A : .sort u) (hp : Γ' ⊢ p.lift' κ : A.subst τ) :
    SubstLiftSquare Γ Γ' (A :: Δ) ρ.cons κ
      (σ.cons p) (τ.cons (p.lift' κ)) where
  context := S.context
  typed := .cons S.typed hA hp
  commute := by
    intro i
    cases i with
    | zero => rfl
    | succ i => exact S.commute i

/-- The variable square commutes on every raw template, including annotations. -/
theorem SubstLiftSquare.apply (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ) (e : VExpr) :
    (e.lift' ρ).subst τ = (e.subst σ).lift' κ := by
  rw [subst_lift', lift'_subst]
  congr 1
  funext i
  exact S.commute i

/-- An ambient proof remains a proof of the smaller instantiated term whenever
that term is typed below. This is the proofness bridge for suspended comparisons. -/
theorem SubstLiftSquare.proof_reflect (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Γ ⊢ e.subst σ : A) (hp : IsProof Δ (e.lift' ρ)) :
    IsProof Γ (e.subst σ) := by
  obtain ⟨P, ht, hP⟩ := hp
  have ht' := ht.subst henv S.typed hΓ'
  rw [S.apply] at ht'
  exact IsProof.of_lift hΓ hΓ' S.context he (hP.subst henv S.typed hΓ') ht'

/-- A suspension extends under a chosen smaller binder using only ambient
alignment of the original binder's substituted domain with that choice. -/
theorem SubstLiftSquare.lift_at (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hA : Δ ⊢ A : .sort u) (hAD : Γ' ⊢ A.subst τ ≡ D.lift' κ) :
    SubstLiftSquare (D :: Γ) (D.lift' κ :: Γ') (A :: Δ)
      ρ.cons κ.cons σ.lift τ.lift where
  context := S.context.cons
  typed := S.typed.lift_at henv hA (hAD.of_l henv hΓ' (hA.subst henv S.typed hΓ'))
  commute := by
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      change (τ (ρ.liftVar i)).lift = (σ i).lift.lift' κ.cons
      rw [S.commute, lift_lift'_cons]

/-- Add a fresh variable only to the ambient target. This is useful for eta
spines whose domain need not be expressible in the smaller context. -/
theorem SubstLiftSquare.skip_at (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hA : Δ ⊢ A : .sort u) (hAX : Γ' ⊢ A.subst τ ≡ X) :
    SubstLiftSquare Γ (X :: Γ') (A :: Δ) ρ.skip κ.skip σ τ.lift where
  context := S.context.skip
  typed := S.typed.lift_at henv hA (hAX.of_l henv hΓ' (hA.subst henv S.typed hΓ'))
  commute := by
    intro i
    change (τ (ρ.liftVar i)).lift = (σ i).lift' κ.skip
    rw [S.commute, lift_eq_lift', ← lift'_comp]
    rfl

/-- The left template domain supplies its own binder alignment by commutation;
it need not be typed in an open smaller context. -/
theorem SubstLiftSquare.lift_template (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (hA : Δ ⊢ A.lift' ρ : .sort u) :
    SubstLiftSquare (A.subst σ :: Γ) ((A.subst σ).lift' κ :: Γ')
      (A.lift' ρ :: Δ) ρ.cons κ.cons σ.lift τ.lift := by
  apply S.lift_at hΓ' hA
  rw [← S.apply]
  exact ⟨_, hA.subst henv S.typed hΓ'⟩

/-- The original binder may be aligned to another template before choosing the
smaller domain. This includes opaque common-domain witnesses in comparisons. -/
theorem SubstLiftSquare.lift_via_template (S : SubstLiftSquare Γ Γ' Δ ρ κ σ τ)
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (hA : Δ ⊢ A : .sort u)
    (hAE : Δ ⊢ A ≡ e.lift' ρ) (heD : Γ ⊢ e.subst σ ≡ D) :
    SubstLiftSquare (D :: Γ) (D.lift' κ :: Γ') (A :: Δ)
      ρ.cons κ.cons σ.lift τ.lift := by
  apply S.lift_at hΓ' hA
  have h := hAE.subst henv S.typed hΓ'
  rw [S.apply] at h
  exact h.trans henv hΓ' (heD.weak' henv S.context)

/-- Recursive domain comparisons reflect through independently typed suspended
instances. The two ambient substitutions are separately typed, and smaller proof
arguments need not share propositions. This is not completeness for arbitrary
normal comparison: recursive lambda-domain certificates are still required. -/
theorem DomainNormal.suspended_reflect : ∀ n {Γ Γ' Δ : List VExpr} {ρ κ : Lift}
    {σ₁ σ₂ τ₁ τ₂ : Subst} {a b A B : VExpr},
    OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    SubstLiftSquare Γ Γ' Δ ρ κ σ₁ τ₁ → SubstLiftSquare Γ Γ' Δ ρ κ σ₂ τ₂ →
    ProofSubstRel Γ σ₁ σ₂ → (Γ ⊢ a.subst σ₁ : A) → (Γ ⊢ b.subst σ₂ : B) →
    DomainNormal n Δ (a.lift' ρ) (b.lift' ρ) →
    (Γ ⊢ A ≡ B → ∃ m, DomainNormal m Γ (a.subst σ₁) (b.subst σ₂)) ∧
    (¬ IsProof Γ (a.subst σ₁) → ∃ m, DomainNormal m Γ (a.subst σ₁) (b.subst σ₂)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro Γ Γ' Δ ρ κ σ₁ σ₂ τ₁ τ₂ a b A B hΓ hΓ' S₁ S₂ Hσ ha hb H
  suffices core : ¬ IsProof Γ (a.subst σ₁) →
      ∃ m, DomainNormal m Γ (a.subst σ₁) (b.subst σ₂) by
    refine ⟨fun hAB => ?_, core⟩
    by_cases hp : IsProof Γ (a.subst σ₁)
    · obtain ⟨P, haP, hP⟩ := hp
      have hAP := ha.uniqU henv hΓ haP
      exact ⟨_, .proofIrrel hP haP (hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP))⟩
    · exact core hp
  intro hn
  have hΔ := S₁.typed.wf
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  cases H with
  | refl _ =>
    cases lift'_inj.1 (hl.trans hr.symm)
    exact subst_certificate_nonproof a hΓ Hσ ha hb hn
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
    obtain ⟨_, HF⟩ := (ih _ (by omega) hΓ hΓ' S₁ S₂ Hσ hf hf' Hf).2
      (not_isProof_fn hΓ hf hx hn)
    have hff := (HF.defeq hΓ).of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
    obtain ⟨_, HX⟩ := (ih _ (by omega) hΓ hΓ' S₁ S₂ Hσ hx hx' Hx).1 ⟨_, hDD⟩
    exact ⟨_, .appDF hf hff.hasType.2 hx ((HX.defeq hΓ).of_l henv hΓ hx).hasType.2 HF HX⟩
  | projDF _ Hm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨m', rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    obtain ⟨_, HM⟩ := (ih _ (by omega) hΓ hΓ' S₁ S₂ Hσ hm.hasType.2 hm'.hasType.2 Hm).2
      (not_isProof_major hΓ ha hn)
    exact ⟨_, .projDF ha HM⟩
  | lamDF hD HD HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.lam_inv henv hΓ
    obtain ⟨_, HC⟩ := (ih _ (by omega) hΓ hΓ' S₁ S₂ Hσ hD₀ hD₁ HD).2
      (not_isProof_of_sort hΓ hD₀)
    have hDD := (HC.defeq hΓ).of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ' hD
    have SS₂ := S₂.lift_via_template hΓ' hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ'D : OnCtx ((D.subst σ₁).lift' κ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', _, hD₀.weak' henv S₁.context⟩
    obtain ⟨_, HB₀⟩ := (ih _ (by omega) hΓD hΓ'D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB).2
      (fun hp => hn (hp.lam hΓ hD₀))
    exact ⟨_, .lamDF hD₀ HC HB₀⟩
  | forallEDF hD HD _ HB =>
    obtain ⟨D, body, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨D', body', rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨⟨_, hD₀⟩, _, hb₀⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD₁⟩, _, hb₁⟩ := hb.forallE_inv henv
    obtain ⟨_, HC⟩ := (ih _ (by omega) hΓ hΓ' S₁ S₂ Hσ hD₀ hD₁ HD).2
      (not_isProof_of_sort hΓ hD₀)
    have hDD := (HC.defeq hΓ).of_l henv hΓ hD₀
    have hb₁' := hb₁.defeqDFC henv (.succ .zero hDD.symm)
    have SS₁ := S₁.lift_template hΓ' hD
    have SS₂ := S₂.lift_via_template hΓ' hD (HD.defeq hΔ) ⟨_, hDD.symm⟩
    have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
    have hΓ'D : OnCtx ((D.subst σ₁).lift' κ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', _, hD₀.weak' henv S₁.context⟩
    obtain ⟨_, HB₀⟩ := (ih _ (by omega) hΓD hΓ'D SS₁ SS₂ Hσ.lift hb₀ hb₁' HB).2
      (not_isProof_of_sort hΓD hb₀)
    exact ⟨_, .forallEDF hD₀ HC hb₀ HB₀⟩
  | proofIrrel hp ht _ =>
    subst hl
    exact (hn (S₁.proof_reflect hΓ hΓ' ha ⟨_, ht, hp⟩)).elim

/-- A proof-argument pair can be pushed onto a delayed comparison without
aligning the proof types below. Both ambient instantiations are checked at the
original binder; the resulting lower instances provide their own typings. -/
theorem DomainNormal.suspended_proof_inst
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ' Δ ρ κ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ' Δ ρ κ σ₂ τ₂) (Hσ : ProofSubstRel Γ σ₁ σ₂)
    (hD : Δ ⊢ D : .sort u) (hp : IsProof Γ p) (hq : IsProof Γ q)
    (hp' : Γ' ⊢ p.lift' κ : D.subst τ₁) (hq' : Γ' ⊢ q.lift' κ : D.subst τ₂)
    (ha : Γ ⊢ a.subst (σ₁.cons p) : A) (hb : Γ ⊢ b.subst (σ₂.cons q) : B)
    (H : DomainNormal n (D :: Δ) (a.lift' ρ.cons) (b.lift' ρ.cons))
    (hAB : Γ ⊢ A ≡ B) :
    ∃ m, DomainNormal m Γ (a.subst (σ₁.cons p)) (b.subst (σ₂.cons q)) :=
  (DomainNormal.suspended_reflect n hΓ hΓ' (S₁.cons hD hp') (S₂.cons hD hq')
    (Hσ.cons_proofs hp hq) ha hb H).1 hAB

/-- A left eta comparison with a recursively certified body can also be lowered
through suspensions. The short function needs a Pi typing only after substitution
below. Its original ambient typing aligns the right substitution under the chosen
left domain; no Pi exposure in an open smaller template context is assumed. -/
theorem suspended_eta_left {D body f : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ' Δ ρ κ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ' Δ ρ κ σ₂ τ₂) (Hσ : ProofSubstRel Γ σ₁ σ₂)
    (hf : Δ ⊢ f.lift' ρ : .forallE (D.lift' ρ) C)
    (H : DomainNormal n (D.lift' ρ :: Δ) (body.lift' ρ.cons)
      (.app (f.lift' ρ).lift (.bvar 0)))
    (ha : Γ ⊢ (VExpr.lam D body).subst σ₁ : A) (hb : Γ ⊢ f.subst σ₂ : B)
    (hAB : Γ ⊢ A ≡ B) :
    ∃ m, BiNormal true m Γ ((VExpr.lam D body).subst σ₁) (f.subst σ₂) := by
  have hΔ := S₁.typed.wf
  obtain ⟨⟨_, hD⟩, _⟩ := (hf.isType henv.ordered hΔ).forallE_inv henv.ordered
  obtain ⟨B₁, hPi, hbody⟩ := ha.lam_inv_forallE henv hΓ
  have hbPi : Γ ⊢ f.subst σ₂ : .forallE (D.subst σ₁) B₁ :=
    hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hPi.symm)
  obtain ⟨⟨_, hD₀⟩, _⟩ := (hbPi.isType henv.ordered hΓ).forallE_inv henv.ordered
  have hΓD : OnCtx (D.subst σ₁ :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hD₀⟩
  have hΓ'D : OnCtx ((D.subst σ₁).lift' κ :: Γ') (Params.env.IsType univs) :=
    ⟨hΓ', _, hD₀.weak' henv S₁.context⟩
  have hfAmbient := hf.subst henv S₂.typed hΓ'
  rw [S₂.apply] at hfAmbient
  have hfBelow := hbPi.weak' henv S₂.context
  obtain ⟨hdomains, _⟩ := (hfAmbient.uniqU henv hΓ' hfBelow).forallE_inv henv hΓ'
  have SS₁ := S₁.lift_template hΓ' hD
  obtain ⟨_, hdomains⟩ := hdomains
  have SS₂ := S₂.lift_at (D := D.subst σ₁) hΓ' hD ⟨_, hdomains⟩
  have hright : D.subst σ₁ :: Γ ⊢ .app (f.subst σ₂).lift (.bvar 0) : B₁ := by
    have h := HasType.app (hbPi.weak henv.ordered (B := D.subst σ₁)) (.bvar .zero)
    simpa only [lift, liftN, inst_liftN_bvar] using h
  have H' : DomainNormal n (D.lift' ρ :: Δ) (body.lift' ρ.cons)
      ((VExpr.app f.lift (.bvar 0)).lift' ρ.cons) := by
    simpa only [lift', Lift.liftVar, lift_lift'_cons] using H
  have hright' : D.subst σ₁ :: Γ ⊢ (VExpr.app f.lift (.bvar 0)).subst σ₂.lift : B₁ := by
    simpa only [subst, Subst.lift, lift_subst_lift] using hright
  obtain ⟨_, hB₁⟩ := hbody.isType henv.ordered hΓD
  obtain ⟨_, HB⟩ := (DomainNormal.suspended_reflect n hΓD hΓ'D SS₁ SS₂
    Hσ.lift hbody hright' H').1 ⟨_, hB₁⟩
  obtain ⟨_, HB⟩ := HB.toBiNormal
  simp only [subst, Subst.lift, lift_subst_lift] at HB
  exact ⟨_, .etaL hbPi (.promote HB)⟩

end Lean4Lean.VEnv.Strengthening
