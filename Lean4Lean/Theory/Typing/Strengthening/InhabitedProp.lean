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

end Lean4Lean.VEnv.Strengthening
