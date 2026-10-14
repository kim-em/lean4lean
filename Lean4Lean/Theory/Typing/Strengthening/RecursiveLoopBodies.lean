import Lean4Lean.Theory.Typing.Strengthening.RecursiveLoopTypes
import Lean4Lean.Theory.Typing.Strengthening.PureBodyComputation
import Lean4Lean.Theory.Typing.Strengthening.PureHeadExposure

/-! # Hereditary computational roles for recursive loops

The body grammar records a role typing at every computational node, while
leaving lambda annotations unrestricted. Unlike raw purity, these witnesses
exclude structure eta and supply the roles of binders introduced by function eta.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

def HasLoopRole (c : Name) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ r : LoopRole, env.HasType univs Γ e (r.type c)

inductive LoopBody (c : Name) : List VExpr → VExpr → Prop where
  | bvar : HasLoopRole c Γ (.bvar i) → LoopBody c Γ (.bvar i)
  | app : HasLoopRole c Γ (.app f a) → LoopBody c Γ f → LoopBody c Γ a →
      LoopBody c Γ (.app f a)
  | lam : HasLoopRole c Γ (.lam A b) → LoopBody c (A :: Γ) b →
      LoopBody c Γ (.lam A b)

theorem LoopBody.role (H : LoopBody c Γ e) : HasLoopRole c Γ e := by
  cases H <;> assumption

theorem LoopBody.pure (H : LoopBody c Γ e) : PureBody e := by
  induction H with
  | bvar => exact .bvar
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ ih => exact .lam ih

theorem HasLoopRole.weakN (H : HasLoopRole c Γ e) (W : Ctx.LiftN n k Γ Γ') :
    HasLoopRole c Γ' (e.liftN n k) := by
  obtain ⟨r, ht⟩ := H
  exact ⟨r, by simpa only [r.type_closed.liftN_eq (Nat.zero_le k)] using ht.weakN henv W⟩

theorem LoopBody.weakN (H : LoopBody c Γ e) (W : Ctx.LiftN n k Γ Γ') :
    LoopBody c Γ' (e.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar ht => exact .bvar (ht.weakN W)
  | app ht _ _ ihf iha => exact .app (ht.weakN W) (ihf W) (iha W)
  | lam ht _ ih => exact .lam (ht.weakN W) (ih W.succ)

theorem HasLoopRole.instN (H : HasLoopRole c Γ₁ e)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (hx : env.HasType univs Γ₀ x A₀) :
    HasLoopRole c Γ (e.inst x k) := by
  obtain ⟨r, ht⟩ := H
  exact ⟨r, by simpa only [r.type_closed.instN_eq (Nat.zero_le k)] using ht.instN henv W hx⟩

theorem LoopBody.instN (H : LoopBody c Γ₁ e)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (hx : env.HasType univs Γ₀ x A₀)
    (Hx : LoopBody c Γ₀ x) : LoopBody c Γ (e.inst x k) := by
  have target_lift : ∀ {k Γ₁ Γ}, Ctx.InstN Γ₀ x A₀ k Γ₁ Γ → Ctx.LiftN k 0 Γ₀ Γ := by
    intro k Γ₁ Γ W
    apply Ctx.liftN_iff_lift'.2
    change Ctx.Lift' (Lift.skipN .refl k) Γ₀ Γ
    induction W with
    | zero => exact .refl
    | succ _ ih => exact .skip ih
  induction H generalizing k Γ with
  | bvar ht =>
    have ht' := ht.instN W hx
    simp only [inst, instVar] at ht' ⊢
    split at ht' <;> simp only [*, if_true, if_false]
    · exact .bvar ht'
    · split at ht' <;> simp only [*, if_true, if_false]
      · exact Hx.weakN (target_lift W)
      · exact .bvar ht'
  | app ht _ _ ihf iha => exact .app (ht.instN W hx) (ihf W) (iha W)
  | lam ht _ ih => exact .lam (ht.instN W hx) (ih W.succ)

theorem HasLoopRole.defeqDFC (H : HasLoopRole c Γ₁ e)
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) : HasLoopRole c Γ₂ e :=
  H.imp fun _ ht => ht.defeqDFC henv W

theorem LoopBody.defeqDFC (H : LoopBody c Γ₁ e)
    (hΓ : OnCtx Γ₁ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) : LoopBody c Γ₂ e := by
  induction H generalizing Γ₂ with
  | bvar ht => exact .bvar (ht.defeqDFC W)
  | app ht _ _ ihf iha => exact .app (ht.defeqDFC W) (ihf hΓ W) (iha hΓ W)
  | lam ht _ ih =>
    obtain ⟨_, he⟩ := ht
    obtain ⟨⟨_, hA⟩, _, _⟩ := he.lam_inv henv hΓ
    exact .lam (HasLoopRole.defeqDFC ⟨_, he⟩ W) (ih ⟨hΓ, _, hA⟩ (.succ W hA))

theorem HasLoopRole.parRed (H : HasLoopRole c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : ParRed Γ e out) : HasLoopRole c Γ out :=
  H.imp fun _ ht => (R.defeq hΓ ht).hasType.2

/-- Core computation preserves all computational role typings, including when
beta duplicates an argument containing recursive self-application. -/
theorem LoopBody.parRed (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : ParRed Γ e out) : LoopBody c Γ out := by
  induction R with
  | bvar => exact H
  | sort | const | proj | forallE => cases H
  | app Rf Ra ihf iha =>
    cases H with
    | app ht Hf Ha => exact .app (ht.parRed hΓ (.app Rf Ra)) (ihf Hf hΓ) (iha Ha hΓ)
  | lam RA Rb _ ihb =>
    cases H with
    | lam ht Hb =>
      obtain ⟨_, he⟩ := ht
      obtain ⟨⟨_, hA⟩, _, _⟩ := he.lam_inv henv hΓ
      have hb' := ihb Hb ⟨hΓ, _, hA⟩
      exact .lam (HasLoopRole.parRed ⟨_, he⟩ hΓ (.lam RA Rb))
        (hb'.defeqDFC ⟨hΓ, _, hA⟩ (.succ .zero (RA.defeq hΓ hA)))
  | beta Rb Ra ihb iha =>
    cases H with
    | app ht Hf Ha =>
      obtain ⟨_, he⟩ := ht
      obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
      cases Hf with
      | lam ht Hb =>
        obtain ⟨_, hfl⟩ := ht
        obtain ⟨⟨_, hA⟩, _, _⟩ := hfl.lam_inv henv hΓ
        obtain ⟨_, hpi, _⟩ := hf.lam_inv_forallE henv hΓ
        obtain ⟨_, harg⟩ := (hpi.forallE_inv henv hΓ).1
        exact (ihb Hb ⟨hΓ, _, hA⟩).instN .zero
          ((Ra.defeq hΓ (harg.symm.defeq ha)).hasType.2) (iha Ha hΓ)
  | extra _ hm => exact (H.pure.no_match hm).elim

theorem HasLoopRole.fullStep (H : HasLoopRole c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : FullStep Γ e out) : HasLoopRole c Γ out :=
  H.imp fun _ ht => R.hasType hΓ ht

/-- Function eta introduces only role-typed computational nodes. The annotation
can be arbitrary syntax convertible to the domain selected by the source role. -/
theorem LoopBody.eta
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) :
    LoopBody c Γ (.lam A (.app e.lift (.bvar 0))) := by
  obtain ⟨r, ht⟩ := H.role
  obtain ⟨a, b, _, hA, hB⟩ := LoopRole.pi_typing hδ hΓ ht hf
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ |>.forallE_inv henv |>.1⟩
  have hv : env.HasType univs (A :: Γ) (.bvar 0) (a.type c) := by
    have hAv := hA.weakN henv (Ctx.LiftN.one (A := A))
    rw [a.type_closed.liftN_eq (Nat.zero_le 0)] at hAv
    exact HasType.defeqU_r henv hΓA hAv (.bvar .zero)
  have hb : env.HasType univs (A :: Γ) (.app e.lift (.bvar 0)) B := by
    simpa only [lift, liftN, inst_liftN_bvar] using
      (hf.weakN henv (Ctx.LiftN.one (A := A))).app (.bvar .zero)
  exact .lam (H.role.fullStep hΓ (.funEta hf))
    (.app ⟨b, hb.defeqU_r henv hΓA hB⟩ (H.weakN .one) (.bvar ⟨a, hv⟩))

/-- No full reduction starting in the role grammar can introduce declarations,
projections, sorts or Pis into a computational body. Those operations can still
appear and compute inside annotations. -/
theorem LoopBody.fullStep
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : FullStep Γ e out) : LoopBody c Γ out := by
  induction R with
  | core R => exact H.parRed hΓ R
  | delta | quotDelta => exact H.pure.no_const_spine.elim
  | projIota | proj | forallE => cases H
  | structEta hi _ _ hm _ =>
    obtain ⟨r, ht⟩ := H.role
    exact (LoopRole.not_structure hδ hΓ ht hi hm).elim
  | funEta hf => exact H.eta hδ hΓ hf
  | app Rf Ra ihf iha =>
    cases H with
    | app ht Hf Ha => exact .app (ht.fullStep hΓ (.app Rf Ra)) (ihf Hf hΓ) (iha Ha hΓ)
  | lam RA Rb _ ihb =>
    cases H with
    | lam ht Hb =>
      obtain ⟨r, he⟩ := ht
      obtain ⟨⟨_, hA⟩, _, _⟩ := he.lam_inv henv hΓ
      exact .lam (HasLoopRole.fullStep ⟨r, he⟩ hΓ (.lam RA Rb))
        ((ihb Hb ⟨hΓ, _, hA⟩).defeqDFC ⟨hΓ, _, hA⟩ (.succ .zero (RA.defeq hΓ hA)))

theorem LoopBody.fullReduction
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : FullReduction Γ e out) : LoopBody c Γ out := by
  induction R with
  | rfl => exact H
  | tail _ R ih => exact ih.fullStep hδ hΓ R

/-- The actual self-application loop starts in the hereditary role grammar. -/
theorem omega_loopBody
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero))) :
    LoopBody c Γ (omegaTerm c) := by
  have hv : env.HasType univs (domain c :: Γ) (.bvar 0) (domain c) := .bvar .zero
  have hb : env.HasType univs (domain c :: Γ) selfBody resultType := ((hδ _).defeq hv).app hv
  have hd : env.HasType univs Γ (diagonal c) (domain c) :=
    (hδ Γ).symm.defeq (.lam (domain_typed hc univs Γ) hb)
  have Hd : LoopBody c Γ (diagonal c) :=
    .lam ⟨.recursive, hd⟩ (.app ⟨.function, hb⟩ (.bvar ⟨.recursive, hv⟩) (.bvar ⟨.recursive, hv⟩))
  exact .app ⟨.function, omega_typed hc hδ⟩ Hd Hd

/-- Erasing annotations from a pure body turns core parallel computation into
ordinary finite beta reduction. Pattern rules cannot have a body redex. -/
theorem pure_parRed_erases (R : ParRed Γ e out) (H : PureBody e) :
    PureBody out ∧ BetaRed (eraseLamDomains e) (eraseLamDomains out) := by
  induction R with
  | bvar => exact ⟨H, .refl⟩
  | sort | const | proj | forallE => cases H
  | app _ _ ihf iha =>
    cases H with
    | app Hf Ha =>
      obtain ⟨Hf, Rf⟩ := ihf Hf
      obtain ⟨Ha, Ra⟩ := iha Ha
      exact ⟨.app Hf Ha, .app Rf Ra⟩
  | lam _ _ _ ihb =>
    cases H with
    | lam Hb =>
      obtain ⟨Hb, Rb⟩ := ihb Hb
      exact ⟨.lam Hb, .lam .refl Rb⟩
  | beta _ _ ihb iha =>
    cases H with
    | app Hf Ha =>
      cases Hf with
      | lam Hb =>
        obtain ⟨Hb, Rb⟩ := ihb Hb
        obtain ⟨Ha, Ra⟩ := iha Ha
        exact ⟨Hb.inst Ha, by
          simpa only [eraseLamDomains, eraseLamDomains_inst] using
            (BetaRed.app (BetaRed.lam (d := .sort .zero) .refl Rb) Ra).trans .beta⟩
  | extra _ hm => exact (H.no_match hm).elim

/-- Along arbitrary full steps of a role body, the erased computational syntax
uses only beta and function eta; all declaration computation stays in annotations. -/
theorem LoopBody.fullStep_erases
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : FullStep Γ e out) : PureObservation.BetaEta (eraseLamDomains e) (eraseLamDomains out) := by
  induction R with
  | core R => exact .of_beta (pure_parRed_erases R H.pure).2
  | delta | quotDelta => exact H.pure.no_const_spine.elim
  | projIota | proj | forallE => cases H
  | structEta hi _ _ hm _ =>
    obtain ⟨r, ht⟩ := H.role
    exact (LoopRole.not_structure hδ hΓ ht hi hm).elim
  | funEta =>
    simpa only [eraseLamDomains, lift, eraseLamDomains_liftN] using
      (PureObservation.BetaEta.eta (e := eraseLamDomains _) (A := .sort .zero))
  | app _ _ ihf iha =>
    cases H with
    | app _ Hf Ha => exact .app (ihf Hf hΓ) (iha Ha hΓ)
  | lam _ _ _ ihb =>
    cases H with
    | lam ht Hb =>
      obtain ⟨_, he⟩ := ht
      obtain ⟨hA, _, _⟩ := he.lam_inv henv hΓ
      exact .lam .refl (ihb Hb ⟨hΓ, hA⟩)

theorem LoopBody.fullReduction_erases
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (H : LoopBody c Γ e) (hΓ : OnCtx Γ (env.IsType univs))
    (R : FullReduction Γ e out) : PureObservation.BetaEta (eraseLamDomains e) (eraseLamDomains out) := by
  induction R with
  | rfl => exact .refl
  | tail R S ih => exact ih.trans ((H.fullReduction hδ hΓ R).fullStep_erases hδ hΓ S)

end Lean4Lean.VEnv.Strengthening.GuardedEta
