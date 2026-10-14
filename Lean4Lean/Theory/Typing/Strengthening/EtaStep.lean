import Lean4Lean.Theory.Typing.Strengthening.EtaExpansion

/-! # Single compatible typed eta expansions

Finite typed eta paths serialize body-first under binders, retaining the context
of each root typing. This presentation supports exchange with normal comparison.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- One typed eta expansion at the root. -/
inductive TypedEtaRoot : List VExpr → VExpr → VExpr → Prop where
  | funEta : env.HasType univs Γ e (.forallE A B) →
      TypedEtaRoot Γ e (.lam A (.app e.lift (.bvar 0)))
  | structEta : env.projections family info → params.length = info.nparams → info.nindices = 0 →
      env.HasType univs Γ e (mkApps (.const family levels) params) →
      env.HasType univs Γ (structExpand family info levels params e)
        (mkApps (.const family levels) params) →
      TypedEtaRoot Γ e (structExpand family info levels params e)

/-- Exactly one typed eta expansion at any compatible position. -/
inductive TypedEtaStep : List VExpr → VExpr → VExpr → Prop where
  | root : TypedEtaRoot Γ a b → TypedEtaStep Γ a b
  | appL : TypedEtaStep Γ f f' → TypedEtaStep Γ (.app f a) (.app f' a)
  | appR : TypedEtaStep Γ a a' → TypedEtaStep Γ (.app f a) (.app f a')
  | lamL : TypedEtaStep Γ A A' → TypedEtaStep Γ (.lam A b) (.lam A' b)
  | lamR : TypedEtaStep (A :: Γ) b b' → TypedEtaStep Γ (.lam A b) (.lam A b')
  | forallL : TypedEtaStep Γ A A' → TypedEtaStep Γ (.forallE A B) (.forallE A' B)
  | forallR : TypedEtaStep (A :: Γ) B B' → TypedEtaStep Γ (.forallE A B) (.forallE A B')
  | proj : TypedEtaStep Γ m m' → TypedEtaStep Γ (.proj s i m) (.proj s i m')

/-- A root step retains its original finite expansion witness. -/
theorem TypedEtaRoot.toExpansion (R : TypedEtaRoot Γ a b) : TypedEtaExpansion Γ a b := by
  cases R with
  | funEta ht => exact .funEta ht
  | structEta hi hp hx hm hc => exact .structEta hi hp hx hm hc

/-- A single compatible step is a finite expansion. -/
theorem TypedEtaStep.toExpansion (R : TypedEtaStep Γ a b) : TypedEtaExpansion Γ a b := by
  induction R with
  | root R => exact R.toExpansion
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | lamL _ ih => exact .lam ih .refl
  | lamR _ ih => exact .lam .refl ih
  | forallL _ ih => exact .forallE ih .refl
  | forallR _ ih => exact .forallE .refl ih
  | proj _ ih => exact .proj ih

/-- Weakening preserves the root's actual type witnesses. -/
theorem TypedEtaRoot.weakN (R : TypedEtaRoot Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    TypedEtaRoot Γ' (a.liftN n k) (b.liftN n k) := by
  cases R with
  | funEta ht =>
    simpa only [liftN, ← lift_liftN', liftVar_zero] using TypedEtaRoot.funEta (ht.weakN henv W)
  | structEta hi hp hx hm hc =>
    have hm' := hm.weakN henv W
    have hc' := hc.weakN henv W
    simp only [liftN_mkApps, liftN, structExpand_liftN] at hm' hc' ⊢
    exact .structEta hi (by simpa using hp) hx hm' hc'

/-- Root expansion survives ambient context conversion. -/
theorem TypedEtaRoot.defeqDFC (R : TypedEtaRoot Γ₁ a b)
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) : TypedEtaRoot Γ₂ a b := by
  cases R with
  | funEta ht => exact .funEta (ht.defeqDFC henv W)
  | structEta hi hp hx hm hc => exact .structEta hi hp hx (hm.defeqDFC henv W) (hc.defeqDFC henv W)

/-- Weakening retains each actual eta typing. -/
theorem TypedEtaStep.weakN (R : TypedEtaStep Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    TypedEtaStep Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing Γ' k with
  | root R => exact .root (R.weakN W)
  | appL _ ih => exact .appL (ih W)
  | appR _ ih => exact .appR (ih W)
  | lamL _ ih => exact .lamL (ih W)
  | lamR _ ih => exact .lamR (ih W.succ)
  | forallL _ ih => exact .forallL (ih W)
  | forallR _ ih => exact .forallR (ih W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Typed conversion of the ambient context preserves a single eta step. -/
theorem TypedEtaStep.defeqDFC (R : TypedEtaStep Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : TypedEtaStep Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | root R => exact .root (R.defeqDFC W)
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

/-- Finite compatible paths serialize into single steps. Expanding binder bodies
before their domains keeps each body's original typing context intact. -/
theorem eta_induct_steps (R : TypedEtaExpansion Γ a b) {P : VExpr → Prop} (ha : P a)
    (hstep : ∀ {x y}, TypedEtaStep Γ x y → P x → P y) : P b := by
  have aux {Γ a b} (R : TypedEtaExpansion Γ a b) :
      ∀ (Q : VExpr → Prop), Q a → (∀ {x y}, TypedEtaStep Γ x y → Q x → Q y) → Q b := by
    induction R with
    | refl => exact fun _ h _ => h
    | funEta ht => exact fun _ h H => H (.root (.funEta ht)) h
    | structEta hi hp hx hm he => exact fun _ h H => H (.root (.structEta hi hp hx hm he)) h
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
