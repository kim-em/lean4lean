import Lean4Lean.Theory.Typing.Strengthening.ReflexiveCastReplay

/-! # Context-free computation with syntactically reflexive casts

The nonlinear K rule repeats its endpoint type. It is preserved by arbitrary
substitution and reflected by injective binder renaming. Source typing suffices
to replay the entire extended computational path in any smaller context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions PatternCompute)

/-- View a binder renaming as a substitution of renamed variables. -/
theorem lift_as_subst (e : VExpr) (ρ : Lift) :
    e.lift' ρ = e.subst (Subst.lift_r Subst.id ρ) := by
  simpa only [subst_id] using (lift'_subst (e := e) (σ := Subst.id) (ρ := ρ))

/-- Cast syntax commutes with arbitrary binder insertion. -/
theorem typeCast_lift' : (typeCast u X Y p x).lift' ρ =
    typeCast u (X.lift' ρ) (Y.lift' ρ) (p.lift' ρ) (x.lift' ρ) := by
  simp only [lift_as_subst, typeCast_subst]

/-- The repeated type and all relevant cast arguments descend through a lift.
Applying the lift's retraction gives the source shape; syntax recovers the payload. -/
theorem lift'_eq_reflexive_cast (h : e.lift' ρ = typeCast u X X p x) :
    ∃ X₀ p₀ x₀, e = typeCast u X₀ X₀ p₀ x₀ ∧ x = x₀.lift' ρ := by
  have he := congrArg (fun e => e.subst ρ.inv) h
  simp only [subst_lift', lift_l_inv, subst_id, typeCast_subst] at he
  refine ⟨_, _, _, he, ?_⟩
  have hh := h.symm.trans (congrArg (fun e => e.lift' ρ) he)
  rw [typeCast_lift'] at hh
  simp only [typeCast, eqRecApp, VExpr.app.injEq] at hh
  exact hh.1.1.2

variable [Params]

/-- Ordinary concrete computation extended by reflexive type-cast contraction.
The endpoint equality is raw syntax, not an ambient definitional-equality guard. -/
inductive CastCompute (D : Definitions) : VExpr → VExpr → Prop where
  | base : PatternCompute D e out → CastCompute D e out
  | cast : CastCompute D (typeCast u X X p x) x
  | trans : CastCompute D a b → CastCompute D b c → CastCompute D a c
  | app : CastCompute D f f' → CastCompute D a a' → CastCompute D (.app f a) (.app f' a')
  | lam : CastCompute D A A' → CastCompute D b b' → CastCompute D (.lam A b) (.lam A' b')
  | forallE : CastCompute D A A' → CastCompute D B B' → CastCompute D (.forallE A B) (.forallE A' B')
  | proj : CastCompute D m m' → CastCompute D (.proj s i m) (.proj s i m')

/-- This includes identity computation. -/
theorem CastCompute.refl : CastCompute D e e := .base .refl

/-- Nonlinear reflexive casts remain matched after arbitrary raw substitution. -/
theorem CastCompute.subst (R : CastCompute D e out) :
    CastCompute D (e.subst σ) (out.subst σ) := by
  induction R generalizing σ with
  | base h => exact .base h.subst
  | cast => simpa only [typeCast_subst] using CastCompute.cast
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Replay uses only source typing, canonical Eq, and sound closed equations. -/
theorem CastCompute.simAt (R : CastCompute D e out) (heq : Params.env.HasCanonicalEq)
    (hs : D.Sound Params.env Params.univs) (hΓ : OnCtx Γ (Params.env.IsType Params.univs)) :
    Params.env.SimAt Params.univs Γ e out := by
  induction R generalizing Γ with
  | base h => exact h.simAt hs hΓ
  | cast => exact reflexive_cast_simAt Params.henv heq hΓ
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | app _ _ ih1 ih2 => exact .app Params.henv.orderedStrong hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 => exact .lam Params.henv.orderedStrong hΓ (ih1 hΓ) ih2
  | forallE _ _ ih1 ih2 => exact .forallE Params.henv.orderedStrong hΓ (ih1 hΓ) ih2
  | proj _ ih => exact .proj Params.henv.orderedStrong hΓ (ih hΓ)

/-- Every path beginning at a lifted term is itself a lift. The nonlinear K
case lowers because binder insertion is injective on its repeated endpoint. -/
theorem CastCompute.lift_inv (R : CastCompute D (e.lift' ρ) out) :
    ∃ e', CastCompute D e e' ∧ out = e'.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | base h =>
    rw [← hsrc] at h
    obtain ⟨e', hr, he⟩ := h.lift_inv
    exact ⟨e', .base hr, he⟩
  | cast =>
    obtain ⟨X, p, x, rfl, hx⟩ := lift'_eq_reflexive_cast hsrc
    exact ⟨x, .cast, hx⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1, R1, h1⟩ := ih1 hsrc
    obtain ⟨e2, R2, h2⟩ := ih2 h1.symm
    exact ⟨e2, R1.trans R2, h2⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨f', Rf, rfl⟩ := ihf rfl
    obtain ⟨a', Ra, rfl⟩ := iha rfl
    exact ⟨_, .app Rf Ra, rfl⟩
  | proj _ ihm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsrc
    obtain ⟨m', Rm, rfl⟩ := ihm rfl
    exact ⟨_, .proj Rm, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', Rb, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA Rb, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩

/-- Lower the full extended computation and replay its equality below, without
any ambient typing or alignment hypothesis. -/
theorem CastCompute.descend (R : CastCompute D (e.lift' ρ) out)
    (heq : Params.env.HasCanonicalEq) (hs : D.Sound Params.env Params.univs)
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (he : Params.env.HasType Params.univs Γ e T) :
    ∃ e', out = e'.lift' ρ ∧ CastCompute D e e' ∧
      Params.env.IsDefEq Params.univs Γ e e' T := by
  obtain ⟨e', R0, hh⟩ := R.lift_inv
  exact ⟨e', hh, R0, R0.simAt heq hs hΓ T he⟩

end Lean4Lean.VEnv.Strengthening
