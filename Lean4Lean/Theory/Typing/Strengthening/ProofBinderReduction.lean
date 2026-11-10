import Lean4Lean.Theory.Typing.EqTyping

/-! # Strengthening reduces to one closed proof binder

With canonical `Eq`, strengthening of definitional equality for one binder of an arbitrary
type `A : Sort u` follows from strengthening for one binder of the closed proposition
`∀ p : Prop, p`. A variable `x : A` is replaced by the cast of the identity function on `A`
along a proof of `@Eq (Sort u) (A → A) A`, and that proof is the new variable applied to the
equation. `A → A` is inhabited whatever `A` is, so no inhabitant of `A` is needed. Terms that
do not mention `x` are unchanged.

Consequently the open statement `IsDefEqU.weakN_iff` (at one binder, which is the only case
`IsDefEqU.weak'_iff` uses) is equivalent to its restriction `UniversalBinderStrengthening`:
assuming every proposition creates no definitional equality between terms that do not mention
the assumption. In that form the removed variable is a proof, so it occurs only inside proof
subterms of any term of the larger context. This is a reduction of the open problem, not a
proof of it.
-/

namespace Lean4Lean
open VExpr

namespace VEnv.Strengthening

variable {env : VEnv} {U : Nat}

/-- `Γ'` is `Γ` with one binder inserted at depth `k`, whose type satisfies `T`. -/
inductive BinderLift (T : List VExpr → VExpr → Prop) : Nat → List VExpr → List VExpr → Prop where
  | zero : T Γ Q → BinderLift T 0 Γ (Q :: Γ)
  | succ : BinderLift T k Γ Γ' → BinderLift T (k+1) (A :: Γ) (A.liftN 1 k :: Γ')

theorem BinderLift.liftN {T} (H : BinderLift T k Γ Γ') : Ctx.LiftN 1 k Γ Γ' := by
  induction H with
  | zero _ => exact .one
  | succ _ ih => exact .succ ih

/-- The closed proposition `∀ p : Prop, p`. -/
def allProps : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- Strengthening of definitional equality for a single binder whose type satisfies `T`. -/
def BinderStrengthening (env : VEnv) (T : List VExpr → VExpr → Prop) : Prop :=
  ∀ {U k Γ Γ' e1 e2}, BinderLift T k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2

/-- Strengthening of definitional equality for a single binder of type `∀ p : Prop, p`.

This is the special case of `IsDefEqU.weakN_iff` that remains open. What is missing is a proof
that a derivation in the larger context, whose intermediate terms may contain proofs built from
the new variable, can be replaced by one that does not use it. -/
def UniversalBinderStrengthening (env : VEnv) : Prop :=
  BinderStrengthening env fun _ Q => Q = allProps

/-- Substituting for the inserted variable after inserting a second binder below it is the
identity on terms that do not mention the inserted variable. -/
theorem liftN_liftN_inst (e e₀ : VExpr) (k : Nat) :
    ((e.liftN 1 k).liftN 1 (k+1)).inst e₀ k = e.liftN 1 k := by
  rw [← liftN_liftN_comm e 1 1 k k (Nat.le_refl _), inst_liftN]

/-- Replace an inserted binder by an inserted binder of another type `Q`, given a term of the
old type over `Q`: a weakening followed by an instantiation, both of which fix every lifted
term. -/
theorem exists_binderLift {T : List VExpr → VExpr → Prop} (henv : env.Ordered)
    (base : ∀ {Γ A}, OnCtx Γ (env.IsType U) → env.IsType U Γ A →
      ∃ Q e₀, T Γ Q ∧ env.IsType U Γ Q ∧ env.HasType U (Q :: Γ) e₀ A.lift)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    ∃ Γ₀ e₀ A₀ Γ₁ Γ'', BinderLift T k Γ Γ'' ∧ OnCtx Γ'' (env.IsType U) ∧
      Ctx.LiftN 1 (k+1) Γ' Γ₁ ∧ Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ'' ∧ env.HasType U Γ₀ e₀ A₀ := by
  induction W with
  | @zero Γ As h =>
    obtain ⟨A, rfl⟩ := List.length_eq_one_iff.1 h
    simp only [List.singleton_append] at hΓ' ⊢
    obtain ⟨hΓ, hA⟩ := hΓ'
    obtain ⟨Q, e₀, hT, hQ, h₀⟩ := base hΓ hA
    exact ⟨_, _, _, A.lift :: Q :: Γ, Q :: Γ, .zero hT, ⟨hΓ, hQ⟩, .succ .one, .zero, h₀⟩
  | @succ k Γ Γ' B W ih =>
    obtain ⟨hΓ', hB⟩ := hΓ'
    obtain ⟨Γ₀, e₀, A₀, Γ₁, Γ'', hL, hΓ'', W₁, W₂, h₀⟩ := ih hΓ'
    have hB' := (hB.weakN henv W₁).instN henv W₂ h₀
    rw [liftN_liftN_inst] at hB'
    have W₂' := Ctx.InstN.succ (A := (B.liftN 1 k).liftN 1 (k+1)) W₂
    rw [liftN_liftN_inst] at W₂'
    exact ⟨Γ₀, e₀, A₀, _, _, .succ hL, ⟨hΓ'', hB'⟩, .succ W₁, W₂', h₀⟩

/-- Strengthening for one binder follows from strengthening for the binders satisfying `T`,
when every type has an inhabitant over some binder satisfying `T`. -/
theorem strengthening_of_binderStrengthening {T : List VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (base : ∀ {Γ A}, OnCtx Γ (env.IsType U) → env.IsType U Γ A →
      ∃ Q e₀, T Γ Q ∧ env.IsType U Γ Q ∧ env.HasType U (Q :: Γ) e₀ A.lift)
    (H : BinderStrengthening env T)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (h : env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k)) : env.IsDefEqU U Γ e1 e2 := by
  obtain ⟨Γ₀, e₀, A₀, Γ₁, Γ'', hL, hΓ'', W₁, W₂, h₀⟩ := exists_binderLift henv base W hΓ'
  have h' := (h.weakN henv W₁).instN henv W₂ h₀
  rw [liftN_liftN_inst, liftN_liftN_inst] at h'
  exact H hL hΓ'' h'

/-- With canonical `Eq`, every type is inhabited over a proof of `∀ p : Prop, p`: cast the
identity function on `A` along the proof of `@Eq (Sort u) (A → A) A` that the hypothesis
supplies. -/
theorem inhabited_over_allProps (henv : env.Ordered) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hA : env.IsType U Γ A) :
    ∃ Q e₀, Q = allProps ∧ env.IsType U Γ Q ∧ env.HasType U (Q :: Γ) e₀ A.lift := by
  obtain ⟨u, hA⟩ := hA
  have hu : u.WF U := IsDefEq.sort_r henv hΓ hA
  have hsu : (VLevel.succ u).WF U := hu
  have h0 : VLevel.zero.WF U := trivial
  have hQ : env.HasType U Γ allProps (.sort (.imax (.succ .zero) .zero)) :=
    .forallE (.sort h0) (.bvar .zero)
  have hΓQ : OnCtx (allProps :: Γ) (env.IsType U) := ⟨hΓ, _, hQ⟩
  have hA' := hA.weak henv (B := allProps)
  have hs : env.HasType U (allProps :: Γ) (.sort u) (.sort (.succ u)) := .sort hu
  -- `A → A : Sort u`, over the new binder
  have hX : env.HasType U (allProps :: Γ) (.forallE A.lift A.lift.lift) (.sort u) :=
    (IsDefEq.sortDF (show (VLevel.imax u u).WF U from ⟨hu, hu⟩) hu VLevel.imax_self).defeq
      (.forallE hA' (hA'.weak henv))
  have hP := HasType.eqApp heq hsu hs hX hA'
  -- the hypothesis applied to the equation
  have hv : env.HasType U (allProps :: Γ)
      (.app (.bvar 0) (VExpr.eqApp (.succ u) (.sort u) (.forallE A.lift A.lift.lift) A.lift))
      (VExpr.eqApp (.succ u) (.sort u) (.forallE A.lift A.lift.lift) A.lift) := by
    have hb : env.HasType U (allProps :: Γ) (.bvar 0) (.forallE (.sort .zero) (.bvar 0)) := by
      have := HasType.bvar (env := env) (U := U) (Lookup.zero (ty := allProps) (Γ := Γ))
      simpa [allProps, VExpr.lift, VExpr.liftN, liftVar] using this
    have := hb.app hP
    simpa [VExpr.inst, instVar] using this
  have hid : env.HasType U (allProps :: Γ) (.lam A.lift (.bvar 0))
      (.forallE A.lift A.lift.lift) :=
    .lam hA' (.bvar .zero)
  exact ⟨_, _, rfl, ⟨_, hQ⟩, HasType.typeCast henv heq hu hX hA' hv hid⟩

/-- **Strengthening for one binder follows from strengthening for one binder of type
`∀ p : Prop, p`**, in an environment with canonical `Eq`. -/
theorem strengthening_of_universalBinder (henv : env.Ordered) (heq : env.HasCanonicalEq)
    (H : UniversalBinderStrengthening env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (h : env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k)) : env.IsDefEqU U Γ e1 e2 :=
  strengthening_of_binderStrengthening henv (inhabited_over_allProps henv heq) H W hΓ' h

end VEnv.Strengthening
end Lean4Lean
