import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-! # Reflecting beta computation at a fresh argument

A finite beta path from `f↑ #0` either retains its application boundary or
crosses it after exposing a lambda in `f`. In the latter case all subsequent
computation can be performed inside that lambda. This is a syntactic lemma for
eta postponement; it asserts neither full-reduction coverage nor strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- A finite beta path from an application either preserves the application
boundary or contracts it once and then continues from the instantiated body. -/
theorem beta_application_cases (R : VExpr.BetaRed (.app f a) out) :
    ∃ f' a', VExpr.BetaRed f f' ∧ VExpr.BetaRed a a' ∧
      (out = .app f' a' ∨ ∃ D b, f' = .lam D b ∧ VExpr.BetaRed (b.inst a') out) := by
  generalize hs : VExpr.app f a = source at R
  induction R generalizing f a with
  | refl => exact ⟨_, _, .refl, .refl, .inl hs.symm⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨f1, a1, Rf1, Ra1, h1⟩ := ih1 hs
    rcases h1 with rfl | ⟨D, b, rfl, Rb⟩
    · obtain ⟨f2, a2, Rf2, Ra2, h2⟩ := ih2 rfl
      exact ⟨_, _, Rf1.trans Rf2, Ra1.trans Ra2, h2⟩
    · exact ⟨_, _, Rf1, Ra1, .inr ⟨D, b, rfl, Rb.trans R2⟩⟩
  | app Rf Ra => cases hs; exact ⟨_, _, Rf, Ra, .inl rfl⟩
  | beta => cases hs; exact ⟨_, _, .refl, .refl, .inr ⟨_, _, rfl, .refl⟩⟩
  | lam | forallE | proj => cases hs

private theorem beta_bvar_eq (R : VExpr.BetaRed (.bvar i) out) : out = .bvar i := by
  have aux {x y : VExpr} (R : VExpr.BetaRed x y) : ∀ i, x = .bvar i → y = .bvar i := by
    induction R with
    | refl => exact fun _ h => h
    | trans _ _ ih1 ih2 => exact fun i h => ih2 i (ih1 i h)
    | app | lam | forallE | proj | beta => exact fun _ h => by cases h
  exact aux R i rfl

/-- Computation at a fresh argument is reflected by computation of the function
itself. A crossed application boundary produces a lambda with the exact computed
body; its domain comes from the original function's beta path. -/
theorem beta_fresh_application (R : VExpr.BetaRed (.app f.lift (.bvar 0)) out) :
    ∃ f', VExpr.BetaRed f f' ∧
      (out = .app f'.lift (.bvar 0) ∨ ∃ D, f' = .lam D out) := by
  obtain ⟨f1, a1, Rf, Ra, h⟩ := beta_application_cases R
  have ha := beta_bvar_eq Ra
  subst a1
  have Rf' : VExpr.BetaRed (f.lift' Lift.refl.skip) f1 := by simpa only [lift_eq_lift'] using Rf
  obtain ⟨f0, R0, he⟩ := betaRed_lift_inv Rf'
  rcases h with rfl | ⟨D, b, hb, Rb⟩
  · exact ⟨f0, R0, .inl (by simp only [he, lift_eq_lift'])⟩
  · obtain ⟨D0, b0, rfl, hD, hbody⟩ := lift'_eq_lam (he.symm.trans hb)
    have hbody' : b = b0.liftN 1 1 := by
      rw [hbody, ← lift'_consN_skipN]; rfl
    rw [hbody', inst_liftN_bvar] at Rb
    exact ⟨_, R0.trans (.lam .refl Rb), .inr ⟨D0, rfl⟩⟩

variable [Params]

/-- Any beta computation beneath an eta expansion can instead be performed in
the original typed function, up to ordinary normal equality. The function's own
beta reduct supplies its domain, so the reduction path adds no eta annotation.
This covers beta only; declaration and singleton computation are not asserted. -/
theorem beta_eta_body_reflection (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : VExpr.BetaRed (.app f.lift (.bvar 0)) out) :
    ∃ f', VExpr.BetaRed f f' ∧ NormalEq Γ f' (.lam A out) := by
  obtain ⟨f', Rf, hout⟩ := beta_fresh_application R
  have hf' : env.HasType univs Γ f' (.forallE A B) :=
    (Rf.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf).hasType.2
  refine ⟨f', Rf, ?_⟩
  rcases hout with rfl | ⟨D, rfl⟩
  · exact .etaR hf' (.refl (HasType.app (hf'.weak henv) (.bvar .zero)))
  · obtain ⟨⟨_, hD⟩, _, hb⟩ := hf'.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := ((hD.lam hb).uniqU henv hΓ hf').forallE_inv henv hΓ
    exact .lamDF hDA.hasType.1 hDA (.refl hb)

end Lean4Lean.VEnv.Strengthening
