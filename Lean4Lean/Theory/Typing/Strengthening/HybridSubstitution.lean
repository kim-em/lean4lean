import Lean4Lean.Theory.Typing.Strengthening.HybridAlgebra

/-! # Substitution with certified arguments

A selective comparison survives heterogeneous substitution when the arguments have
a recursive domain certificate. Unrestricted hybrid arguments are not assumed to
satisfy this requirement. The homogeneous case follows from a reflexive certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

private theorem retype_certified_inst (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (Harg : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h : Γ₁ ⊢ e : T) : Γ ⊢ e.inst e₀' k : T.inst e₀ k := by
  have hΓ := (W.wf henv h₀ hΓ₁).2
  obtain ⟨_, H⟩ := DomainNormal.instN_r hΓ₁ h₀ Harg W h
  exact ((H.defeq hΓ).of_l henv hΓ (h.instN henv W h₀)).hasType.2

private theorem HybridNormal.instN_proof (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (Harg : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : HybridNormal m Γ₁ a b) (hp : IsProof Γ₁ a) :
    HybridNormal 0 Γ (a.inst e₀ k) (b.inst e₀' k) := by
  obtain ⟨P, ha, hP⟩ := hp
  have hb := ((H.defeq hΓ₁).of_l henv hΓ₁ ha).hasType.2
  exact .proofIrrel (hP.instN henv W h₀) (ha.instN henv W h₀)
    (retype_certified_inst hΓ₁ h₀ Harg W hb)

private theorem HybridNormal.inst_fn_side (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (Harg : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hf : Γ₁ ⊢ f : T)
    (Hf : HybridNormal m Γ₁ f f') (hnp : ¬ IsProof Γ₁ f)
    (hs : (¬ IsLam f ∧ ¬ IsLam f') ∨ ∃ j, DomainNormal j Γ₁ f f') :
    (¬ IsLam (f.inst e₀ k) ∧ ¬ IsLam (f'.inst e₀' k)) ∨
      ∃ j, DomainNormal j Γ (f.inst e₀ k) (f'.inst e₀' k) := by
  rcases hs with ⟨hnf, hnf'⟩ | ⟨j, Hcert⟩
  · by_cases hl : IsLam (f.inst e₀ k)
    · cases f with
      | bvar i =>
        have h := Hf.variable_inv hΓ₁ hf hnp hnf'
        subst f'
        exact .inr (DomainNormal.instN_r hΓ₁ h₀ Harg W hf)
      | lam => exact (hnf trivial).elim
      | sort | const | app | forallE | proj => simp [inst, IsLam] at hl
    · by_cases hr : IsLam (f'.inst e₀' k)
      · have hf' := ((Hf.defeq hΓ₁).of_l henv hΓ₁ hf).hasType.2
        have hnp' : ¬ IsProof Γ₁ f' := by
          rintro ⟨P, hp, hP⟩
          exact hnp ⟨P, (((Hf.defeq hΓ₁).symm).of_l henv hΓ₁ hp).hasType.2, hP⟩
        cases f' with
        | bvar i =>
          have h := (Hf.symm hΓ₁).variable_inv hΓ₁ hf' hnp' hnf
          subst f
          exact .inr (DomainNormal.instN_r hΓ₁ h₀ Harg W hf)
        | lam => exact (hnf' trivial).elim
        | sort | const | app | forallE | proj => simp [inst, IsLam] at hr
      · exact .inl ⟨hl, hr⟩
  · exact .inr (DomainNormal.instN_lr hΓ₁ h₀ Harg W Hcert)

/-- Heterogeneous substitution preserves selective comparisons when the argument
comparison is recursively domain-certified. Variable rigidity supplies certificates
for newly exposed function lambdas; proof applications use proof irrelevance. -/
theorem HybridNormal.instN_lr (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (Harg : DomainNormal n Γ₀ e₀ e₀')
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : HybridNormal m Γ₁ e1 e2) :
    ∃ j, HybridNormal j Γ (e1.inst e₀ k) (e2.inst e₀' k) := by
  induction H generalizing Γ k with
  | refl h =>
    obtain ⟨_, H⟩ := DomainNormal.instN_r hΓ₁ h₀ Harg W h
    exact H.toHybrid (W.wf henv h₀ hΓ₁).2
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF hs h1 h2 h3 h4 Hf Ha ih1 ih2 =>
    rename_i f1 f2 Γs A B a1 a2 nf na
    by_cases hp : IsProof Γs f1
    · exact ⟨_, (HybridNormal.appDF hs h1 h2 h3 h4 Hf Ha).instN_proof hΓ₁ h₀ Harg W
        (IsProof.app_fn hΓ₁ h1 h3 hp)⟩
    · obtain ⟨_, HF⟩ := ih1 hΓ₁ W
      obtain ⟨_, HA⟩ := ih2 hΓ₁ W
      exact ⟨_, .appDF (Hf.inst_fn_side hΓ₁ h₀ Harg W h1 hp hs)
        (h1.instN henv W h₀) (retype_certified_inst hΓ₁ h₀ Harg W h2)
        (h3.instN henv W h₀) (retype_certified_inst hΓ₁ h₀ Harg W h4) HF HA⟩
  | projDF hproj _ ih =>
    obtain ⟨_, H⟩ := ih hΓ₁ W
    exact ⟨_, .projDF (hproj.instN henv W h₀) H⟩
  | lamDF h1 h2 _ ih =>
    have hΓ := (W.wf henv h₀ hΓ₁).2
    have hΓ₁' : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ₁, _, h1.hasType.1⟩
    obtain ⟨_, H⟩ := ih hΓ₁' W.succ
    obtain ⟨_, HD⟩ := DomainNormal.instN_r hΓ₁ h₀ Harg W h2.hasType.2
    have h2i := h2.instN henv h₀ W
    exact ⟨_, .lamDF (h1.instN henv h₀ W)
      (h2i.trans ((HD.defeq hΓ).of_l henv hΓ h2i.hasType.2)) H⟩
  | forallEDF h1 _ h3 _ ihA ihB =>
    have hΓ₁' : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ₁, _, h1.hasType.1⟩
    obtain ⟨_, HA⟩ := ihA hΓ₁ W
    obtain ⟨_, HB⟩ := ihB hΓ₁' W.succ
    exact ⟨_, .forallEDF (h1.instN henv h₀ W) HA (h3.instN henv W.succ h₀) HB⟩
  | etaL h1 _ ih =>
    have hΓ₁' : OnCtx (_ :: _) (Params.env.IsType univs) :=
      ⟨hΓ₁, ((h1.isType henv hΓ₁).forallE_inv henv).1⟩
    obtain ⟨_, H⟩ := ih hΓ₁' W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H
    rw [← lift_instN_lo] at H
    exact ⟨_, .etaL (retype_certified_inst hΓ₁ h₀ Harg W h1) H⟩
  | @etaR Γ₁ e' A B _ _ h1 _ ih =>
    have hΓ := (W.wf henv h₀ hΓ₁).2
    obtain ⟨u, hAB⟩ := h1.isType henv hΓ₁
    obtain ⟨w, hA'⟩ := (hAB.forallE_inv henv).1
    have hΓ₁' : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, _, hA'⟩
    obtain ⟨_, H⟩ := ih hΓ₁' W.succ
    obtain ⟨_, HA⟩ := DomainNormal.instN_r hΓ₁ h₀ Harg W hA'
    have hAA := (HA.defeq hΓ).of_l henv hΓ (hA'.instN henv W h₀)
    obtain ⟨_, HT⟩ := DomainNormal.instN_r hΓ₁ h₀ Harg W hAB
    have he' : Γ ⊢ e'.inst e₀ k : .forallE (A.inst e₀' k) (B.inst e₀' (k + 1)) :=
      (h1.instN henv W h₀).defeqU_r henv hΓ (HT.defeq hΓ)
    have H' := H.defeqDFC hΓ (.succ .zero hAA)
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H'
    rw [← lift_instN_lo] at H'
    exact ⟨_, .etaR he' H'⟩
  | etaBoth h1 h2 _ ih =>
    have hΓ₁' : OnCtx (_ :: _) (Params.env.IsType univs) :=
      ⟨hΓ₁, ((h1.isType henv hΓ₁).forallE_inv henv).1⟩
    obtain ⟨_, H⟩ := ih hΓ₁' W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H
    rw [← lift_instN_lo, ← lift_instN_lo] at H
    exact ⟨_, .etaBoth (h1.instN henv W h₀) (retype_certified_inst hΓ₁ h₀ Harg W h2) H⟩
  | proofIrrel h1 h2 h3 =>
    exact ⟨_, .proofIrrel (h1.instN henv W h₀) (h2.instN henv W h₀)
      (retype_certified_inst hΓ₁ h₀ Harg W h3)⟩

/-- Homogeneous substitution needs only the argument's typing; its recursive
certificate is reflexive. The output comparison index may change. -/
theorem HybridNormal.instN (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ e₀ : A₀) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : HybridNormal m Γ₁ e1 e2) : ∃ j, HybridNormal j Γ (e1.inst e₀ k) (e2.inst e₀ k) :=
  H.instN_lr hΓ₁ h₀ (.refl h₀) W

end Lean4Lean.VEnv.Strengthening
