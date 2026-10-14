import Lean4Lean.Theory.Typing.Strengthening.FreshDeclarationReflection
import Lean4Lean.Theory.Typing.Strengthening.PatternComputation

/-! # Fresh-argument reflection for applied patterns and projection computation

Every concrete applied pattern demands a constructor-headed final argument.
Consequently no pattern can contract at the root of `f↑ #0`. This extends the
fresh-argument reflection needed for eta postponement to compatible core pattern
and saturated projection computation. Prefixes and structure eta are excluded.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- A concrete pattern cannot consume a bare variable as its final argument. -/
theorem pattern_no_variable_argument (hp : Pat p r)
    (hm : p.Matches (.app f (.bvar i)) ls captures) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn => cases hm
  | iota recursor major ctor fields =>
    cases hm with
    | app hf ha =>
      obtain ⟨c, hc⟩ := (ConstHeaded.varN (p := .const ctor) (n := fields) trivial).matches_head ha
      cases hc

/-- Projection computation leaves a bare variable unchanged. -/
theorem ProjectionCompute.bvar_eq (R : ProjectionCompute D (.bvar i) out) : out = .bvar i := by
  have aux {a b : VExpr} (R : ProjectionCompute D a b) : ∀ i, a = .bvar i → b = .bvar i := by
    induction R with
    | base R => intro i h; subst h; exact compute_bvar_eq R
    | trans _ _ ih1 ih2 => exact fun i h => ih2 i (ih1 i h)
    | projIota | app | lam | forallE | proj => exact fun _ h => by cases h
  exact aux R i rfl

/-- Projection steps cannot cross a fresh application boundary. If beta crosses
it, subsequent computation is reflected inside the exposed lambda. -/
theorem ProjectionCompute.fresh_application
    (R : ProjectionCompute D (.app f.lift (.bvar 0)) out) :
    ∃ f', ProjectionCompute D f f' ∧
      (out = .app f'.lift (.bvar 0) ∨ ∃ A, f' = .lam A out) := by
  generalize hs : VExpr.app f.lift (.bvar 0) = source at R
  induction R generalizing f with
  | base R =>
    rw [← hs] at R
    obtain ⟨f', Rf, h⟩ := compute_fresh_application R
    exact ⟨f', .base Rf, h⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨f1, Rf1, h1⟩ := ih1 hs
    rcases h1 with rfl | ⟨A, rfl⟩
    · obtain ⟨f2, Rf2, h2⟩ := ih2 rfl
      exact ⟨f2, Rf1.trans Rf2, h2⟩
    · exact ⟨_, Rf1.trans (.lam (.base .refl) R2), .inr ⟨A, rfl⟩⟩
  | app Rf Ra =>
    cases hs
    have ha := Ra.bvar_eq
    subst ha
    have Rf' := Rf
    rw [lift_eq_lift'] at Rf'
    obtain ⟨f', Rf0, he⟩ := Rf'.lift_inv
    exact ⟨f', Rf0, .inl (by simp only [he, lift_eq_lift'])⟩
  | projIota | lam | forallE | proj => cases hs

/-- Pattern computation also leaves a bare variable unchanged. -/
theorem PatternCompute.bvar_eq (R : PatternCompute D (.bvar i) out) : out = .bvar i := by
  have aux {a b : VExpr} (R : PatternCompute D a b) : ∀ i, a = .bvar i → b = .bvar i := by
    induction R with
    | base R => intro i h; subst h; exact R.bvar_eq
    | trans _ _ ih1 ih2 => exact fun i h => ih2 i (ih1 i h)
    | pattern hp hm hc =>
      intro i h; subst h
      obtain ⟨c, hh⟩ := (Params.constHeaded hp).matches_head hm
      cases hh
    | app | lam | forallE | proj => exact fun _ h => by cases h
  exact aux R i rfl

/-- Every finite compatible pattern/projection computation at a fresh argument
reflects into computation of the original function. No source typing is required. -/
theorem PatternCompute.fresh_application
    (R : PatternCompute D (.app f.lift (.bvar 0)) out) :
    ∃ f', PatternCompute D f f' ∧
      (out = .app f'.lift (.bvar 0) ∨ ∃ A, f' = .lam A out) := by
  generalize hs : VExpr.app f.lift (.bvar 0) = source at R
  induction R generalizing f with
  | base R =>
    rw [← hs] at R
    obtain ⟨f', Rf, h⟩ := R.fresh_application
    exact ⟨f', .base Rf, h⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨f1, Rf1, h1⟩ := ih1 hs
    rcases h1 with rfl | ⟨A, rfl⟩
    · obtain ⟨f2, Rf2, h2⟩ := ih2 rfl
      exact ⟨f2, Rf1.trans Rf2, h2⟩
    · exact ⟨_, Rf1.trans (.lam .refl R2), .inr ⟨A, rfl⟩⟩
  | pattern hp hm hc =>
    rw [← hs] at hm
    exact (pattern_no_variable_argument hp hm).elim
  | app Rf Ra =>
    cases hs
    have ha := Ra.bvar_eq
    subst ha
    have Rf' := Rf
    rw [lift_eq_lift'] at Rf'
    obtain ⟨f', Rf0, he⟩ := Rf'.lift_inv
    exact ⟨f', Rf0, .inl (by simp only [he, lift_eq_lift'])⟩
  | lam | forallE | proj => cases hs

/-- The typed eta-body reflection now covers applied patterns and projections.
The output comparison remains ordinary NormalEq with opaque domain conversion. -/
theorem PatternCompute.eta_body_reflection (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (R : PatternCompute D (.app f.lift (.bvar 0)) out) :
    ∃ f', PatternCompute D f f' ∧ NormalEq Γ f' (.lam A out) := by
  obtain ⟨f', Rf, hout⟩ := R.fresh_application
  have hf' : env.HasType univs Γ f' (.forallE A B) := (Rf.simAt hs hΓ _ hf).hasType.2
  refine ⟨f', Rf, ?_⟩
  rcases hout with rfl | ⟨D, rfl⟩
  · exact .etaR hf' (.refl (HasType.app (hf'.weak henv) (.bvar .zero)))
  · obtain ⟨⟨_, hD⟩, _, hb⟩ := hf'.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := ((hD.lam hb).uniqU henv hΓ hf').forallE_inv henv hΓ
    exact .lamDF hDA.hasType.1 hDA (.refl hb)

end Lean4Lean.VEnv.Strengthening.PureObservation
