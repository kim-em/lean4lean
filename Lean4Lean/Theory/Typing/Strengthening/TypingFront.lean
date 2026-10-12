import Lean4Lean.Theory.Typing.Strengthening.Cancel
import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.Confluence.PatternConstructorRigidity

/-! # Typing strengthening: the typing front, the typed front and the Prop front

The three forms of the open problem that every route meets, with their equivalences under
canonical `Eq` (all proved here; nothing in this file is conditional on an open statement):

* `TypingFront`: a `q`-free term typable in `Q :: Γ` is typable in `Γ` at some type.
  **This is the whole problem**: `cancel_of_typingFront` (existential typing descent gives
  `Cancel`, hence `Strengthening`). Fixed-type descent follows from existential descent through
  the ascription `(λ x : A. x) e` (`fixed_typingFront`), and an equation `a↑ ≡ b↑` above is the
  typing `Eq.refl a↑ : Eq A↑ a↑ b↑`, whose descent yields `a ≡ b` below by unique typing and
  injectivity of the rigid head `Eq` (`canonicalEq_rigid`, from the registered ι pattern of
  `Eq.rec`). `not_cancel_iff_typing_gap`: `Cancel` fails exactly when some `q`-free term is
  typable above and at no type below.
* `TypedFront`: an equation between terms typed below at a common type descends. The form the
  confluence route (route A) and the model route (route B) both reduce to; `Cancel` implies
  it (`typedFront_of_cancel`), the converse is the content of PR #53's replay chain, not
  reproduced here.
* `PropFront`: two *propositions* typed below with convertible lifts are convertible below.
  Under canonical `Eq` this is equivalent to `TypedFront` (`typeFront_iff_propFront`,
  `typeFront_iff_typedFront`): a comparison of types `A B : Sort u` is the comparison of the
  propositions `Eq (Sort u) A A` and `Eq (Sort u) A B`, and injectivity of `Eq` brings it back.
  So the universe of the compared types is immaterial (impredicativity), and the leaf
  obligation of every descent (the proof-irrelevance leaf of normal equality, where two proofs
  typed below at `P₁`, `P₂ : Prop` have `P₁↑ ≡ P₂↑` above) is already the whole problem.

Where canonical `Eq` is used: only in the encodings (`Eq.refl`, `Eq` injectivity) that turn
conversions into typings and arbitrary-universe comparisons into `Prop` comparisons. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {Q a b T : VExpr}

/-! ## The typing front -/

/-- Existential typing descent at the front of the context. -/
def TypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

/-- Existential typing descent for binders with no inhabitant below. -/
def UninhabitedTypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    (∀ q, ¬ env.HasType U Γ q Q) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

theorem typingFront_of_uninhabited (henv : env.WF)
    (H : UninhabitedTypingFront env) : TypingFront env := by
  intro U Γ Q e A hΓ he
  classical
  by_cases h : ∃ q, env.HasType U Γ q Q
  · obtain ⟨q, hq⟩ := h
    exact ⟨A.inst q, by simpa only [inst_lift] using he.instN henv.ordered Ctx.InstN.zero hq⟩
  · exact H hΓ (by simpa using h) he

/-- A type ascription, by application and lambda: `(λ x : A. x) e`. -/
def ascribe (e A : VExpr) : VExpr := .app (.lam A (.bvar 0)) e

theorem ascribe_typed (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ e A) : env.HasType U Γ (ascribe e A) A := by
  obtain ⟨u, hA⟩ := he.isType henv hΓ
  simpa only [ascribe, inst_lift] using HasType.app (HasType.lam hA (.bvar .zero)) he

theorem ascribe_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ (ascribe e A) B) : env.HasType U Γ e A := by
  obtain ⟨D, E, hf, he⟩ := he.app_inv henv hΓ
  obtain ⟨C, hPi, _⟩ := hf.lam_inv_forallE henv hΓ
  obtain ⟨u, hAD⟩ := (hPi.forallE_inv henv hΓ).1
  exact .defeqDF hAD.symm he

/-- Existential typing descent gives fixed-type descent, through the ascription. -/
theorem fixed_typingFront (henv : env.WF) (H : TypingFront env)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (he : env.HasType U (Q :: Γ) e.lift A.lift) : env.HasType U Γ e A := by
  have ht := ascribe_typed henv.ordered hΓ he
  have ht' : env.HasType U (Q :: Γ) (ascribe e A).lift A.lift := ht
  obtain ⟨B, hb⟩ := H hΓ ht'
  exact ascribe_inv henv hΓ.1 hb

/-! ## Canonical `Eq` is rigid and injective -/

/-- `Eq.refl` is the constructor of the registered ι pattern of `Eq.rec`. -/
theorem canonicalEq_isPatCtor (heq : env.HasCanonicalEq) : IsPatCtor env ``Eq.refl :=
  let ⟨_, _, _, hp⟩ := heq.2.2.2
  ⟨_, _, ``Eq.rec, 5, 2, hp, rfl⟩

/-- Canonical `Eq` is rigid: it is the result type former of the pattern constructor
`Eq.refl`. -/
theorem canonicalEq_rigid (henv : env.WF) (heq : env.HasCanonicalEq) : env.Rigid ``Eq := by
  obtain ⟨ci, hci, F, ls, hF, -, hr⟩ := henv.patCtor_resultRigid (canonicalEq_isPatCtor heq)
  rw [heq.2.1] at hci
  cases hci
  have : (VExpr.const ``Eq [.param 0] : VExpr) = .const F ls := by
    simpa [canonicalEqReflType, VExpr.forallResult, VExpr.getAppFnArgs,
      VExpr.getAppFnArgs.go] using hF
  cases this
  exact hr

/-- Injectivity of `Eq` in its right endpoint. -/
theorem eqApp_injective (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (hT : env.HasType U Γ T (.sort u)) (ha : env.HasType U Γ a T)
    (hu : u.WF U)
    (H : env.IsDefEqU U Γ (eqApp u T a a) (eqApp u T a b)) :
    env.IsDefEqU U Γ a b := by
  have ht := HasType.eqApp heq hu hT ha ha
  have hh := (IsDefEqU.rigidApp_inv (args := [T,a,a]) (args' := [T,a,b]) henv hΓ
    (canonicalEq_rigid henv heq) H ht).2
  cases hh with | cons _ hh =>
    cases hh with | cons _ hh =>
      cases hh with | cons h _ => exact h

/-! ## The typing front is the whole problem -/

/-- Under canonical `Eq`, existential typing descent gives cancellation: the equation
`a↑ ≡ b↑` above is the typing `Eq.refl a↑ : Eq A↑ a↑ b↑`, whose descent gives
`Eq A a a ≡ Eq A a b` below by unique typing, and `a ≡ b` by injectivity of `Eq`. -/
theorem cancel_of_typingFront (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : TypingFront env) : Cancel env := by
  apply Cancel.of_front henv
  intro U Γ Q a b hΓ hab
  obtain ⟨R, hab⟩ := hab
  obtain ⟨A, ha⟩ := H hΓ hab.hasType.1
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ.1
  have hu := hA.sort_r henv.ordered hΓ.1
  have ha' : env.HasType U (Q :: Γ) a.lift A.lift := ha.weak henv.ordered
  have hab' := (show env.IsDefEqU U (Q :: Γ) a.lift b.lift from ⟨_, hab⟩).of_l henv hΓ ha'
  have hA' : env.HasType U (Q :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  have hr := HasType.eqReflApp heq hu hA' ha'
  have hr' := (IsDefEq.eqApp_r heq hu hA' ha' hab').defeq hr
  have hd : env.HasType U Γ (eqReflApp u A a) (eqApp u A a b) := by
    apply fixed_typingFront henv H hΓ
    simpa only [eqReflApp, eqApp, lift, liftN] using hr'
  have hr₀ := HasType.eqReflApp heq hu hA ha
  exact eqApp_injective henv heq hΓ.1 hA ha hu (hr₀.uniqU henv hΓ.1 hd)

theorem uninhabitedTypingFront_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    UninhabitedTypingFront env ↔ Cancel env := by
  constructor
  · intro H
    exact cancel_of_typingFront henv heq (typingFront_of_uninhabited henv H)
  · intro H U Γ Q e A hΓ _ he
    obtain ⟨B, hb⟩ := Front.of_cancel H hΓ ⟨A, he⟩
    exact ⟨B, hb⟩

theorem typingFront_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypingFront env ↔ Cancel env :=
  ⟨cancel_of_typingFront henv heq, fun hc _ _ _ _ _ hΓ he =>
    let ⟨B, hb⟩ := Front.of_cancel hc hΓ ⟨_, he⟩; ⟨B, hb⟩⟩

/-- `Cancel` fails exactly when some `q`-free term is typable above an uninhabited binder and
at no type below: the typing gap. -/
theorem not_cancel_iff_typing_gap (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ Cancel env ↔
      ∃ (U : Nat) (Γ : List VExpr) (Q e A : VExpr),
        OnCtx (Q :: Γ) (env.IsType U) ∧
        (∀ q, ¬ env.HasType U Γ q Q) ∧
        env.HasType U (Q :: Γ) e.lift A ∧
        ∀ B, ¬ env.HasType U Γ e B := by
  classical
  rw [← uninhabitedTypingFront_iff_cancel henv heq]
  simp only [UninhabitedTypingFront, Classical.not_forall, not_exists, exists_prop]

/-! ## The typed front -/

/-- Fixed-type descent for endpoints typed below at a common type (PR #53's `TypedFront`). -/
def TypedFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEq U (Q :: Γ) a.lift b.lift T.lift → env.IsDefEq U Γ a b T

/-- The typed front along any single-binder insertion. -/
def TypedFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' a b T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEq U Γ' (a.liftN 1 k) (b.liftN 1 k) (T.liftN 1 k) → env.IsDefEq U Γ a b T

/-- Descent of conversions between types typed below, at the front. -/
def TypeFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q A B u v⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U Γ A (.sort u) → env.HasType U Γ B (.sort v) →
    env.IsDefEqU U (Q :: Γ) A.lift B.lift → env.IsDefEqU U Γ A B

/-- Descent of conversions between types typed below, along any single-binder insertion. -/
def TypeFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' A B u v⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ A (.sort u) → env.HasType U Γ B (.sort v) →
    env.IsDefEqU U Γ' (A.liftN 1 k) (B.liftN 1 k) → env.IsDefEqU U Γ A B

/-- Descent of conversions between *propositions* typed below, at the front. -/
def PropFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q P₁ P₂⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U Γ P₁ (.sort .zero) → env.HasType U Γ P₂ (.sort .zero) →
    env.IsDefEqU U (Q :: Γ) P₁.lift P₂.lift → env.IsDefEqU U Γ P₁ P₂

theorem TypedFront.of_typedFrontN (H : TypedFrontN env) : TypedFront env :=
  fun _ _ _ _ _ _ hΓ hQ ha hb hab => H Ctx.LiftN.one hΓ ⟨hΓ, hQ⟩ ha hb hab

theorem TypeFront.of_typeFrontN (H : TypeFrontN env) : TypeFront env :=
  fun _ _ _ _ _ _ _ hΓ hA hB hAB => H Ctx.LiftN.one hΓ.1 hΓ hA hB hAB

theorem PropFront.of_typeFront (H : TypeFront env) : PropFront env :=
  fun _ _ _ _ _ hΓ h₁ h₂ h => H hΓ h₁ h₂ h

theorem typedFront_of_cancel (henv : env.WF) (hc : Cancel env) : TypedFront env := by
  intro U Γ Q a b T hΓ hQ ha hb hab
  have hΓ' : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, hQ⟩
  exact IsDefEqU.of_l henv hΓ (Front.of_cancel hc hΓ' ⟨_, hab⟩) ha

theorem typedFrontN_of_cancel (henv : env.WF) (hc : Cancel env) : TypedFrontN env := by
  intro U k Γ Γ' a b T W hΓ hΓ' ha hb hab
  obtain ⟨S, hS⟩ := Strengthening.of_cancel henv hc W hΓ' ⟨_, hab⟩
  exact IsDefEqU.of_l henv hΓ ⟨_, hS⟩ ha

theorem typeFrontN_of_cancel (henv : env.WF) (hc : Cancel env) : TypeFrontN env :=
  fun _ _ _ _ _ _ _ _ W _ hΓ' _ _ hAB => Strengthening.of_cancel henv hc W hΓ' hAB

/-- The independent-endpoint form of the typed front: the endpoints need only be typed below,
at any types. -/
theorem TypedFront.independent (henv : env.WF) (H : TypedFront env)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (hab : env.IsDefEqU U (Q :: Γ) a.lift b.lift) : env.IsDefEqU U Γ a b := by
  have hΓ₀ := hΓ.1
  have hQ := hΓ.2
  have ha' : env.HasType U (Q :: Γ) a.lift A.lift := ha.weak henv.ordered
  have hb' : env.HasType U (Q :: Γ) b.lift B.lift := hb.weak henv.ordered
  have hd := hab.of_l henv hΓ ha'
  have hAB' := hd.uniqU henv hΓ hb'
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ₀
  obtain ⟨v, hB⟩ := hb.isType henv.ordered hΓ₀
  have hA' : env.HasType U (Q :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  have hB' : env.HasType U (Q :: Γ) B.lift (.sort v) := hB.weak henv.ordered
  have huv := ((hAB'.of_l henv hΓ hA').uniqU henv hΓ hB').sort_inv henv hΓ
  have hBu : env.HasType U Γ B (.sort u) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓ₀) (hA.sort_r henv.ordered hΓ₀)
      (Eq.symm huv)).defeq hB
  have hAB : env.IsDefEq U Γ A B (.sort u) := H hΓ₀ hQ hA hBu (hAB'.of_l henv hΓ hA')
  have hbA : env.HasType U Γ b A := hAB.symm.defeq hb
  exact ⟨_, H hΓ₀ hQ ha hbA hd⟩

/-! ## The typed front is the type front is the Prop front -/

/-- The type front gives the typed front: an equation between terms typed below at a common
type is encoded as the `Eq` types `Eq T a a` and `Eq T a b`, types below with convertible
lifts above; their agreement below gives `a ≡ b` by injectivity of the rigid head `Eq`. -/
theorem typedFront_of_typeFront (henv : env.WF) (heq : env.HasCanonicalEq) (H : TypeFront env) :
    TypedFront env := by
  intro U Γ Q a b T hΓ hQ ha hb hab
  obtain ⟨u, hT⟩ := ha.isType henv.ordered hΓ
  have hu := hT.sort_r henv.ordered hΓ
  have hΓ' : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, hQ⟩
  have hT' : env.HasType U (Q :: Γ) T.lift (.sort u) := hT.weak henv.ordered
  have ha' : env.HasType U (Q :: Γ) a.lift T.lift := ha.weak henv.ordered
  have e1 := IsDefEq.eqApp_r heq hu hT' ha' hab
  have e2 : env.IsDefEqU U (Q :: Γ) (eqApp u T a a).lift (eqApp u T a b).lift :=
    ⟨_, by simpa only [eqApp, lift, liftN] using e1⟩
  have h := H hΓ' (HasType.eqApp heq hu hT ha ha) (HasType.eqApp heq hu hT ha hb) e2
  exact (eqApp_injective henv heq hΓ hT ha hu h).of_l henv hΓ ha

theorem typeFront_of_typedFront (henv : env.WF) (H : TypedFront env) :
    TypeFront env := by
  intro U Γ Q A B u v hΓ hA hB hAB
  exact H.independent henv hΓ hA hB hAB

/-- Under canonical `Eq`, the type front is exactly the typed front. -/
theorem typeFront_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypeFront env ↔ TypedFront env :=
  ⟨typedFront_of_typeFront henv heq, typeFront_of_typedFront henv⟩

/-- The Prop front gives the type front: two types `A B : Sort u` typed below with convertible
lifts are compared as the propositions `Eq (Sort u) A A` and `Eq (Sort u) A B`, typed below at
`Prop`, whose lifts are convertible above by congruence; their agreement below gives `A ≡ B` by
injectivity of `Eq`. The universe `u` of the compared types plays no role: `Prop` is
impredicative. -/
theorem typeFront_of_propFront (henv : env.WF) (heq : env.HasCanonicalEq) (H : PropFront env) :
    TypeFront env := by
  intro U Γ Q A B u v hΓ hA hB hAB
  have hΓ₀ := hΓ.1
  have hu := hA.sort_r henv.ordered hΓ₀
  have hA' : env.HasType U (Q :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  have hB' : env.HasType U (Q :: Γ) B.lift (.sort v) := hB.weak henv.ordered
  have hd := hAB.of_l henv hΓ hA'
  have huv := (hd.uniqU henv hΓ hB').sort_inv henv hΓ
  have hBu : env.HasType U Γ B (.sort u) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓ₀) hu (Eq.symm huv)).defeq hB
  have hsu : (VLevel.succ u).WF U := hu
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := HasType.sort hu
  have hS' : env.HasType U (Q :: Γ) (.sort u) (.sort (.succ u)) := HasType.sort hu
  have e1 := IsDefEq.eqApp_r heq hsu hS' hA' hd
  have e2 : env.IsDefEqU U (Q :: Γ) (eqApp (.succ u) (.sort u) A A).lift
      (eqApp (.succ u) (.sort u) A B).lift :=
    ⟨_, by simpa only [eqApp, lift, liftN] using e1⟩
  have h := H hΓ (HasType.eqApp heq hsu hS hA hA) (HasType.eqApp heq hsu hS hA hBu) e2
  exact eqApp_injective henv heq hΓ₀ hS hA hsu h

/-- Under canonical `Eq`, the type front is exactly the Prop front. -/
theorem typeFront_iff_propFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypeFront env ↔ PropFront env :=
  ⟨PropFront.of_typeFront, typeFront_of_propFront henv heq⟩

/-- Under canonical `Eq`, the typed front is exactly the Prop front: the whole typed problem
is the descent of conversions between propositions typed below. -/
theorem typedFront_iff_propFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypedFront env ↔ PropFront env :=
  (typeFront_iff_typedFront henv heq).symm.trans (typeFront_iff_propFront henv heq)

theorem propFront_of_cancel (henv : env.WF) (hc : Cancel env) : PropFront env :=
  PropFront.of_typeFront (typeFront_of_typedFront henv (typedFront_of_cancel henv hc))

end Lean4Lean.VEnv.Strengthening
