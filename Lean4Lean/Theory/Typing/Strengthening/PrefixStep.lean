import Lean4Lean.Theory.Typing.Strengthening.PrefixComputation
import Lean4Lean.Theory.Typing.Strengthening.PatternStep

/-! Single compatible contractions for actual prefix computation. Binder paths
are serialized body-first, preserving the context carried by every check. -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A concrete pattern contraction or an actual prefix, under compatible syntax. -/
inductive PrefixStep (D : Definitions) : List VExpr → VExpr → VExpr → Prop where
  | base : PatternStep D a b → PrefixStep D Γ a b
  | singleton : PrefixUnfold env univs recursorData Γ name levels args out →
      PrefixStep D Γ (mkApps (.const name levels) args) out
  | quotient : QuotPrefixUnfold env univs Γ levels args out →
      PrefixStep D Γ (mkApps (.const ``Quot.lift levels) args) out
  | appL : PrefixStep D Γ f f' → PrefixStep D Γ (.app f a) (.app f' a)
  | appR : PrefixStep D Γ a a' → PrefixStep D Γ (.app f a) (.app f a')
  | lamL : PrefixStep D Γ A A' → PrefixStep D Γ (.lam A b) (.lam A' b)
  | lamR : PrefixStep D (A :: Γ) b b' → PrefixStep D Γ (.lam A b) (.lam A b')
  | forallL : PrefixStep D Γ A A' → PrefixStep D Γ (.forallE A B) (.forallE A' B)
  | forallR : PrefixStep D (A :: Γ) B B' → PrefixStep D Γ (.forallE A B) (.forallE A B')
  | proj : PrefixStep D Γ m m' → PrefixStep D Γ (.proj s i m) (.proj s i m')

variable {D : Definitions}

theorem PrefixStep.toCompute (R : PrefixStep D Γ a b) : PrefixCompute D Γ a b := by
  induction R with
  | base R => exact .base R.toCompute
  | singleton R => exact .singleton R
  | quotient R => exact .quotient R
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

/-- Weakening retains each actual prefix check. -/
theorem PrefixStep.weakN (R : PrefixStep D Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    PrefixStep D Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing Γ' k with
  | base R => exact .base (R.liftN n k)
  | singleton R =>
    simpa only [liftN_mkApps, liftN] using PrefixStep.singleton (R.weakN henv W)
  | quotient R =>
    simpa only [liftN_mkApps, liftN] using PrefixStep.quotient (R.weakN henv W)
  | appL _ ih => exact .appL (ih W)
  | appR _ ih => exact .appR (ih W)
  | lamL _ ih => exact .lamL (ih W)
  | lamR _ ih => exact .lamR (ih W.succ)
  | forallL _ ih => exact .forallL (ih W)
  | forallR _ ih => exact .forallR (ih W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Typed conversion of the ambient context preserves a single checked step. -/
theorem PrefixStep.defeqDFC (R : PrefixStep D Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : PrefixStep D Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | base R => exact .base R
  | singleton R => exact .singleton (R.defeqDFC henv hΓ W)
  | quotient R => exact .quotient (R.defeqDFC henv hΓ W)
  | appL _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .appL (ih W hf)
  | appR _ ih =>
    obtain ⟨_, _, _, ha⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .appR (ih W ha)
  | lamL _ ih =>
    obtain ⟨⟨_, hA⟩, _, _⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lamL (ih W hA)
  | lamR _ ih =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lamR (ih (.succ W hA) hb)
  | forallL _ ih =>
    obtain ⟨⟨_, hA⟩, _, _⟩ := ht.forallE_inv henv
    exact .forallL (ih W hA)
  | forallR _ ih =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.forallE_inv henv
    exact .forallR (ih (.succ W hA) hb)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)

/-- Finite compatible paths serialize into single steps. Computing binder bodies
before their domains keeps each body's original checking context intact. -/
theorem prefix_induct_steps (hc : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PrefixCompute D Γ a b) {P : VExpr → Prop} (ha : P a)
    (hstep : ∀ {x y}, PrefixStep D Γ x y → P x → P y) : P b := by
  have aux {Γ a b} (R : PrefixCompute D Γ a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, PrefixStep D Γ x y → Q x → Q y) → Q b := by
    induction R with
    | base R => exact fun Q h H => pattern_induct_steps hc R h (fun R => H (.base R))
    | singleton R => exact fun _ h H => H (.singleton R) h
    | quotient R => exact fun _ h H => H (.quotient R) h
    | trans _ _ ih1 ih2 => exact fun Q h H => ih2 Q (ih1 Q h H) H
    | @app Γ f f' a a' _ _ ihf iha =>
      intro Q h H
      exact iha (fun x => Q (.app f' x))
        (ihf (fun x => Q (.app x a)) h (fun R => H (.appL R))) (fun R => H (.appR R))
    | @lam Γ A A' b b' _ _ ihA ihb =>
      intro Q h H
      exact ihA (fun x => Q (.lam x b'))
        (ihb (fun x => Q (.lam A x)) h (fun R => H (.lamR R))) (fun R => H (.lamL R))
    | @forallE Γ A A' B B' _ _ ihA ihB =>
      intro Q h H
      exact ihA (fun x => Q (.forallE x B'))
        (ihB (fun x => Q (.forallE A x)) h (fun R => H (.forallR R))) (fun R => H (.forallL R))
    | @proj Γ m m' s i _ ihm =>
      exact fun Q h H => ihm (fun x => Q (.proj s i x)) h (fun R => H (.proj R))
  exact aux R P ha hstep

end Lean4Lean.VEnv.Strengthening.PureObservation
