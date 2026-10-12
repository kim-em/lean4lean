import Lean4Lean.Theory.Typing.Strengthening.TypingFront

/-! # The inhabited Prop front is the Prop front

`InhabitedPropFront`: descent of a conversion between two propositions typed below that are
both *inhabited* below. It is the obligation left by the descent of a normal-equality join
through a matched pair of head β-redexes whose arguments are proofs: the two abstractions'
domains are propositions inhabited (by the arguments) below, with lifts convertible above.

It is equivalent to `PropFront` (`inhabitedPropFront_iff_propFront`): a proposition `P` is
turned into the inhabited proposition `P → P` (inhabited by the identity), lifts stay convertible
by congruence, and the result is read back by injectivity of `Π`. So inhabitation of the
compared propositions is not a weakening of the open statement. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr

variable {env : VEnv} {U : Nat}

/-- Descent of conversions between propositions typed below and inhabited below. -/
def InhabitedPropFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q P₁ P₂ x y⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U Γ P₁ (.sort .zero) → env.HasType U Γ P₂ (.sort .zero) →
    env.HasType U Γ x P₁ → env.HasType U Γ y P₂ →
    env.IsDefEqU U (Q :: Γ) P₁.lift P₂.lift → env.IsDefEqU U Γ P₁ P₂

theorem InhabitedPropFront.of_propFront (H : PropFront env) : InhabitedPropFront env :=
  fun _ _ _ _ _ _ _ hΓ h₁ h₂ _ _ he => H hΓ h₁ h₂ he

/-- `P → P`, a proposition inhabited by the identity. -/
def selfArrow (P : VExpr) : VExpr := .forallE P P.lift

theorem selfArrow_typed (henv : env.Ordered) (hP : env.HasType U Γ P (.sort .zero)) :
    env.HasType U Γ (selfArrow P) (.sort .zero) :=
  .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero) ⟨trivial, trivial⟩ trivial rfl)
    (HasType.forallE hP (hP.weak henv))

theorem selfArrow_inhabited (hP : env.HasType U Γ P (.sort .zero)) :
    env.HasType U Γ (.lam P (.bvar 0)) (selfArrow P) :=
  HasType.lam hP (.bvar .zero)

theorem selfArrow_lift (P : VExpr) : (selfArrow P).lift = selfArrow P.lift := by
  simp only [selfArrow, lift, liftN]
  exact congrArg (VExpr.forallE _) (lift_liftN' P 0).symm

/-- The inhabited front gives the full Prop front. -/
theorem propFront_of_inhabitedPropFront (henv : env.WF) (H : InhabitedPropFront env) :
    PropFront env := by
  intro U Γ Q P₁ P₂ hΓ h₁ h₂ he
  have hΓ₀ := hΓ.1
  have h₁' : env.HasType U (Q :: Γ) P₁.lift (.sort .zero) := h₁.weak henv.ordered
  have h₂' : env.HasType U (Q :: Γ) P₂.lift (.sort .zero) := h₂.weak henv.ordered
  have hd : env.IsDefEq U (Q :: Γ) P₁.lift P₂.lift (.sort .zero) := he.of_l henv hΓ h₁'
  have hbody : env.IsDefEq U (P₁.lift :: Q :: Γ) P₁.lift.lift P₂.lift.lift (.sort .zero) :=
    hd.weak henv.ordered
  have hS : env.IsDefEqU U (Q :: Γ) (selfArrow P₁).lift (selfArrow P₂).lift := by
    rw [selfArrow_lift, selfArrow_lift]
    exact ⟨_, .forallEDF hd hbody⟩
  have h := H hΓ (selfArrow_typed henv.ordered h₁) (selfArrow_typed henv.ordered h₂)
    (selfArrow_inhabited h₁) (selfArrow_inhabited h₂) hS
  obtain ⟨u, hu⟩ := (h.forallE_inv henv hΓ₀).1
  exact ⟨_, hu⟩

theorem inhabitedPropFront_iff_propFront (henv : env.WF) :
    InhabitedPropFront env ↔ PropFront env :=
  ⟨propFront_of_inhabitedPropFront henv, InhabitedPropFront.of_propFront⟩

/-- Under canonical `Eq`, the inhabited Prop front is the typed front. -/
theorem inhabitedPropFront_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    InhabitedPropFront env ↔ TypedFront env :=
  (inhabitedPropFront_iff_propFront henv).trans (typedFront_iff_propFront henv heq).symm

/-! ## The lambda-domain front

Two lifted abstractions, each typed below (at possibly different types, the mode-0 situation
of the normal-equality descent: the argument pair of a matched β-redex pair), convertible
above: their domains are convertible below. With a *common* type below this is trivial
(`lamDomain_of_common_type`, by `Π`-injectivity), which is why the residue lives at positions
without type information. Without a common type it is exactly `TypeFront`
(`lamDomainFront_iff_typeFront`). -/

/-- Domain descent for lifted abstractions typed below at unrelated types. -/
def LamDomainFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q C₁ C₂ t₁ t₂ T₁ T₂⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U Γ (.lam C₁ t₁) T₁ → env.HasType U Γ (.lam C₂ t₂) T₂ →
    env.IsDefEqU U (Q :: Γ) (VExpr.lam C₁ t₁).lift (VExpr.lam C₂ t₂).lift →
    env.IsDefEqU U Γ C₁ C₂

/-- With a common type below, the domains agree below by `Π`-injectivity alone. -/
theorem lamDomain_of_common_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.HasType U Γ (.lam C₁ t₁) T) (h₂ : env.HasType U Γ (.lam C₂ t₂) T) :
    env.IsDefEqU U Γ C₁ C₂ := by
  obtain ⟨B₁, e₁, -⟩ := h₁.lam_inv_forallE henv hΓ
  obtain ⟨B₂, e₂, -⟩ := h₂.lam_inv_forallE henv hΓ
  obtain ⟨u, h⟩ := ((e₁.trans henv hΓ (e₂.symm)).forallE_inv henv hΓ).1
  exact ⟨_, h⟩

theorem LamDomainFront.of_typeFront (henv : env.WF) (H : TypeFront env) : LamDomainFront env := by
  intro U Γ Q C₁ C₂ t₁ t₂ T₁ T₂ hΓ h₁ h₂ he
  obtain ⟨⟨u, hC₁⟩, -⟩ := h₁.lam_inv henv hΓ.1
  obtain ⟨⟨v, hC₂⟩, -⟩ := h₂.lam_inv henv hΓ.1
  obtain ⟨w, hd⟩ := IsDefEqU.lam_domain henv hΓ he
  exact H hΓ hC₁ hC₂ ⟨_, hd⟩

theorem TypeFront.of_lamDomainFront (henv : env.WF) (H : LamDomainFront env) : TypeFront env := by
  intro U Γ Q A B u v hΓ hA hB hAB
  have hΓ₀ := hΓ.1
  have hd := hAB.of_l henv hΓ (hA.weak henv.ordered)
  have hv : env.HasType U (Q :: Γ) B.lift (.sort u) := hd.hasType.2
  have hId₁ : env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) := HasType.lam hA (.bvar .zero)
  have hId₂ : env.HasType U Γ (.lam B (.bvar 0)) (.forallE B B.lift) := HasType.lam hB (.bvar .zero)
  have he : env.IsDefEqU U (Q :: Γ) (VExpr.lam A (.bvar 0)).lift (VExpr.lam B (.bvar 0)).lift := by
    refine ⟨_, IsDefEq.lamDF (u := u) hd (.bvar .zero)⟩
  exact H hΓ hId₁ hId₂ he

/-- The lambda-domain front is the type front. -/
theorem lamDomainFront_iff_typeFront (henv : env.WF) : LamDomainFront env ↔ TypeFront env :=
  ⟨TypeFront.of_lamDomainFront henv, LamDomainFront.of_typeFront henv⟩

/-- Under canonical `Eq`, the lambda-domain front is the typed front. -/
theorem lamDomainFront_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    LamDomainFront env ↔ TypedFront env :=
  (lamDomainFront_iff_typeFront henv).trans (typeFront_iff_typedFront henv heq)

end Lean4Lean.VEnv.Strengthening
