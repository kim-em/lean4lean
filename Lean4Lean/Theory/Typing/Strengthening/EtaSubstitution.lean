import Lean4Lean.Theory.Typing.Strengthening.EtaExpansion

/-! # Substitution and beta exchange for typed eta expansion

Substitution retains the actual typings at eta roots. Changing the substituted
argument uses compatible expansion and weakening. These operations handle both
an existing beta redex and beta contraction of a function-eta-created lambda;
global postponement remains separate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A typed substitution preserves every function and structure expansion. -/
theorem TypedEtaExpansion.instN (R : TypedEtaExpansion Γ₁ e e')
    (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ) (ha : env.HasType univs Γ₀ a A₀) :
    TypedEtaExpansion Γ (e.inst a k) (e'.inst a k) := by
  induction R generalizing Γ k with
  | refl => exact .refl
  | structEta hi hp hx ht hc =>
    have ht' := ht.instN henv W ha
    have hc' := hc.instN henv W ha
    simp only [inst_mkApps, inst, List.map_append, List.map_map, Function.comp_def] at ht' hc' ⊢
    exact .structEta hi (by simpa only [List.length_map] using hp) hx ht' hc'
  | funEta ht =>
    simpa only [inst, lift_instN_lo, instVar, Nat.zero_lt_succ, if_true] using
      (TypedEtaExpansion.funEta (ht.instN henv W ha))
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Expansion of the argument propagates through any raw substitution body.
Only the expansion's own root witnesses are used. -/
theorem TypedEtaExpansion.inst_argument (R : TypedEtaExpansion Γ a a') (e : VExpr) :
    TypedEtaExpansion Γ (e.inst a) (e.inst a') := by
  rw [inst_eq, inst_eq]
  apply typedEtaExpansion_congrRel.subst_args
  intro i
  cases i with
  | zero => exact .inr R
  | succ i => exact .inl rfl

/-- Simultaneous expansion of a body and its typed substituted argument. -/
theorem TypedEtaExpansion.inst_both (R : TypedEtaExpansion (A :: Γ) b b')
    (ha : env.HasType univs Γ a A) (HA : TypedEtaExpansion Γ a a') :
    TypedEtaExpansion Γ (b.inst a) (b'.inst a') :=
  (R.instN .zero ha).trans (HA.inst_argument b')

/-- Contract an existing beta redex before expanding its body and argument.
Changes of the displayed lambda domain do not appear in either contractum. -/
theorem beta_eta_exchange (R : TypedEtaExpansion (A :: Γ) b b')
    (ha : env.HasType univs Γ a A) (HA : TypedEtaExpansion Γ a a') :
    ∃ out, PrefixCompute D Γ (.app (.lam A b) a) out ∧
      TypedEtaExpansion Γ out (b'.inst a') :=
  ⟨b.inst a, .base (.of_beta .beta), R.inst_both ha HA⟩

/-- Beta consuming a function-eta-created lambda needs no earlier computation.
The remaining body and argument expansions replay directly on the original
application. The eta annotation's domain only supplies substitution typing. -/
theorem function_eta_beta_exchange
    (R : TypedEtaExpansion (A :: Γ) (.app f.lift (.bvar 0)) b')
    (ha : env.HasType univs Γ a A) (HA : TypedEtaExpansion Γ a a') :
    TypedEtaExpansion Γ (.app f a) (b'.inst a') := by
  simpa only [inst, inst_lift, instVar, Nat.lt_irrefl, if_false, if_true, liftN_zero] using
    R.inst_both ha HA

end Lean4Lean.VEnv.Strengthening.PureObservation
