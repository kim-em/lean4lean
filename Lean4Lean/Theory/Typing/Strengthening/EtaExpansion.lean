import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixFactorization
import Lean4Lean.Theory.Typing.PrefixUnfolding.ArgumentCongruence

/-! # Finite compatible typed eta expansion

Function and structure eta are kept separate from computation and ordinary
normal equality. Function roots retain their Pi typing; structure roots retain
their registration and both endpoint typings. This is an interface for
postponement, not a completeness assertion about full reduction.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Finite function and structure expansions, including expansions under binders
and inside annotations. There are no computational contractions. -/
inductive TypedEtaExpansion : List VExpr → VExpr → VExpr → Prop where
  | refl : TypedEtaExpansion Γ e e
  | structEta : env.projections family info → params.length = info.nparams → info.nindices = 0 →
      env.HasType univs Γ e (mkApps (.const family levels) params) →
      env.HasType univs Γ
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun j => .proj family j e))
        (mkApps (.const family levels) params) →
      TypedEtaExpansion Γ e
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun j => .proj family j e))
  | funEta : env.HasType univs Γ e (.forallE A B) →
      TypedEtaExpansion Γ e (.lam A (.app e.lift (.bvar 0)))
  | trans : TypedEtaExpansion Γ a b → TypedEtaExpansion Γ b c → TypedEtaExpansion Γ a c
  | app : TypedEtaExpansion Γ f f' → TypedEtaExpansion Γ a a' →
      TypedEtaExpansion Γ (.app f a) (.app f' a')
  | lam : TypedEtaExpansion Γ A A' → TypedEtaExpansion (A :: Γ) b b' →
      TypedEtaExpansion Γ (.lam A b) (.lam A' b')
  | forallE : TypedEtaExpansion Γ A A' → TypedEtaExpansion (A :: Γ) B B' →
      TypedEtaExpansion Γ (.forallE A B) (.forallE A' B')
  | proj : TypedEtaExpansion Γ m m' → TypedEtaExpansion Γ (.proj s i m) (.proj s i m')

/-- Forgetting the separation gives an actual finite full-reduction path. -/
theorem TypedEtaExpansion.full (R : TypedEtaExpansion Γ a b) : FullReduction Γ a b := by
  induction R with
  | refl => exact .rfl
  | structEta hi hp hx ht hc => exact .tail .rfl (.structEta hi hp hx ht hc)
  | funEta ht => exact .tail .rfl (.funEta ht)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Source typing reconstructs all intermediate and binder typings. -/
theorem TypedEtaExpansion.simAt (R : TypedEtaExpansion Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ a b :=
  fun _ ht => R.full.defeq hΓ ht

/-- Weakening preserves both typings of every root expansion. -/
theorem TypedEtaExpansion.weakN (R : TypedEtaExpansion Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    TypedEtaExpansion Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing Γ' k with
  | refl => exact .refl
  | structEta hi hp hx ht hc =>
    have ht' := ht.weakN henv W
    have hc' := hc.weakN henv W
    simp only [liftN_mkApps, liftN, List.map_append, List.map_map, Function.comp_def] at ht' hc' ⊢
    exact .structEta hi (by simpa only [List.length_map] using hp) hx ht' hc'
  | funEta ht =>
    simpa only [liftN, ← lift_liftN', liftVar_zero] using
      (TypedEtaExpansion.funEta (ht.weakN henv W))
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Ambient context conversion retains the actual expansion witnesses. -/
theorem TypedEtaExpansion.defeqDFC (R : TypedEtaExpansion Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : TypedEtaExpansion Γ₂ a b := by
  induction R generalizing Γ₂ T with
  | refl => exact .refl
  | structEta hi hp hx hs hc => exact .structEta hi hp hx (hs.defeqDFC henv W) (hc.defeqDFC henv W)
  | funEta hf => exact .funEta (hf.defeqDFC henv W)
  | trans R1 _ ih1 ih2 => exact .trans (ih1 W ht) (ih2 W (R1.simAt (W.isType' hΓ) _ ht).hasType.2)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hA) (ih2 (.succ W hA) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (.succ W hA) hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)

/-- The generic prefix congruence interface applies to actual eta expansion. -/
theorem typedEtaExpansion_congrRel : CongrRel TypedEtaExpansion where
  rfl := .refl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN W R := R.weakN W

/-- Prefix capture substitution uses source typing to check the related result. -/
theorem typedEtaExpansion_argRel : ArgRel TypedEtaExpansion :=
  typedEtaExpansion_congrRel.argRel (fun hΓ R ht => R.simAt hΓ _ ht)

/-- Neither eta form can create a Pi head, even without source typing. -/
theorem TypedEtaExpansion.forallE_source (R : TypedEtaExpansion Γ e (.forallE A B)) :
    ∃ A' B', e = .forallE A' B' := by
  generalize hout : VExpr.forallE A B = target at R
  induction R generalizing A B with
  | refl => exact ⟨_, _, hout.symm⟩
  | structEta =>
    have hh := congrArg VExpr.getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | trans _ _ ih1 ih2 =>
    obtain ⟨A', B', he⟩ := ih2 hout
    exact ih1 he.symm
  | forallE => exact ⟨_, _, rfl⟩
  | app | lam | proj | funEta => cases hout

end Lean4Lean.VEnv.Strengthening.PureObservation
