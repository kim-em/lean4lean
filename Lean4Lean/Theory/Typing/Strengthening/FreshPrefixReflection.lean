import Lean4Lean.Theory.Typing.Strengthening.PrefixComputation
import Lean4Lean.Theory.Typing.Strengthening.FreshPatternReflection

/-! # Finite fresh-argument reflection with actual prefixes

The root and duplicated-domain lemmas handle fresh prefix boundaries. Reflection
of arbitrary compatible subcomputations uses the explicit witnessed proposition
front. This gives a conditional eta-postponement interface without claiming the
front or full strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Actual prefix computation cannot change a bare variable. -/
theorem PrefixCompute.bvar_eq (R : PrefixCompute D Γ (.bvar i) out) : out = .bvar i := by
  have aux {Δ : List VExpr} {a b : VExpr} (R : PrefixCompute D Δ a b) :
      ∀ i, a = .bvar i → b = .bvar i := by
    induction R with
    | base R => intro i h; subst h; exact R.bvar_eq
    | trans _ _ ih1 ih2 => exact fun i h => ih2 i (ih1 i h)
    | singleton | quotient =>
      intro i h
      have hh := congrArg VExpr.getAppFn h
      simp only [getAppFn_mkApps, getAppFn] at hh
      cases hh
    | app | lam | forallE | proj => exact fun _ h => by cases h
  exact aux R i rfl

/-- Under the witnessed front, every finite compatible computation at a fresh
argument reflects into the original typed function. The exact output either
retains the application boundary or is the body of a computed lambda. -/
theorem PrefixCompute.fresh_application (R : PrefixCompute D (A :: Γ) (.app f.lift (.bvar 0)) out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B)) :
    ∃ f', PrefixCompute D Γ f f' ∧
      (out = .app f'.lift (.bvar 0) ∨ ∃ domain, f' = .lam domain out) := by
  generalize hsrc : VExpr.app f.lift (.bvar 0) = source at R
  generalize hctx : A :: Γ = Δ at R
  induction R generalizing Γ A B f with
  | base R =>
    rw [← hsrc] at R
    obtain ⟨f', Rf, hout⟩ := R.fresh_application
    exact ⟨f', .base Rf, hout⟩
  | singleton H =>
    cases hctx
    obtain ⟨upperArgs, ha, hfn⟩ := RigidHead.const.mkApps_eq_app hsrc.symm
    rw [ha] at H
    have hfn' := hfn
    rw [lift_eq_lift'] at hfn'
    obtain ⟨args, rfl, rfl⟩ := lift'_eq_const_spine hfn'
    obtain ⟨domain, _, Hlower⟩ := prefixUnfold_fresh_argument henv hΓ hf (by
      simpa only [← lift_eq_lift'] using H)
    exact ⟨_, .singleton Hlower, .inr ⟨domain, rfl⟩⟩
  | quotient H =>
    cases hctx
    obtain ⟨upperArgs, ha, hfn⟩ := RigidHead.const.mkApps_eq_app hsrc.symm
    rw [ha] at H
    have hfn' := hfn
    rw [lift_eq_lift'] at hfn'
    obtain ⟨args, rfl, rfl⟩ := lift'_eq_const_spine hfn'
    obtain ⟨domain, _, Hlower⟩ := quotPrefixUnfold_fresh_argument henv hΓ hf (by
      simpa only [← lift_eq_lift'] using H)
    exact ⟨_, .quotient Hlower, .inr ⟨domain, rfl⟩⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨f1, Rf1, hout⟩ := ih1 hΓ hf hsrc hctx
    have hf1 := (Rf1.simAt hs hΓ _ hf).hasType.2
    rcases hout with rfl | ⟨domain, rfl⟩
    · obtain ⟨f2, Rf2, hout⟩ := ih2 hΓ hf1 rfl hctx
      exact ⟨f2, Rf1.trans Rf2, hout⟩
    · cases hctx
      obtain ⟨⟨_, hD⟩, _, hb⟩ := hf1.lam_inv henv hΓ
      obtain ⟨⟨_, hDA⟩, _⟩ := ((hD.lam hb).uniqU henv hΓ hf1).forallE_inv henv hΓ
      have hbA := hb.defeqDFC henv (.succ .zero hDA)
      have Rb := R2.defeqDFC hs hΓ (.succ .zero hDA.symm) hbA
      exact ⟨_, Rf1.trans (.lam .refl Rb), .inr ⟨domain, rfl⟩⟩
  | app Rf Ra =>
    cases hctx
    cases hsrc
    have ha := Ra.bvar_eq
    subst ha
    obtain ⟨hA, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have Rf' := Rf
    rw [lift_eq_lift'] at Rf'
    obtain ⟨f', Rlower, hout⟩ := Rf'.lift_inv heq hs hfront (Ctx.Lift'.skip .refl)
      hΓ ⟨hΓ, hA⟩ hf
    exact ⟨f', Rlower, .inl (by
      simpa only [← lift_eq_lift'] using congrArg (fun x => VExpr.app x (.bvar 0)) hout)⟩
  | lam | forallE | proj => cases hsrc

/-- The conditional finite reflection supplies the ordinary normal comparison
needed to postpone eta. Lambda-domain conversions remain opaque in NormalEq. -/
theorem PrefixCompute.eta_body_reflection (R : PrefixCompute D (A :: Γ) (.app f.lift (.bvar 0)) out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B)) :
    ∃ f', PrefixCompute D Γ f f' ∧ NormalEq Γ f' (.lam A out) := by
  obtain ⟨f', Rf, hout⟩ := R.fresh_application heq hs hfront hΓ hf
  have hf' := (Rf.simAt hs hΓ _ hf).hasType.2
  refine ⟨f', Rf, ?_⟩
  rcases hout with rfl | ⟨domain, rfl⟩
  · exact .etaR hf' (.refl (HasType.app (hf'.weak henv) (.bvar .zero)))
  · exact normal_lam_domain_of_pi hΓ hf'

end Lean4Lean.VEnv.Strengthening.PureObservation
