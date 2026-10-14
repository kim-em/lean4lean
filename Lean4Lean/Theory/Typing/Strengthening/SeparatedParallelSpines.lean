import Lean4Lean.Theory.Typing.Strengthening.PrefixOrdinaryExchange

/-! # Typed congruence and fixed-instance spines for separated parallel reduction -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Separated parallel computation preserves every type of its source. -/
theorem SeparatedPar.simAt (R : SeparatedPar D a b) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (A) (ha : env.HasType univs Γ a A) :
    env.IsDefEq univs Γ a b A := R.toCompute.simAt hs hΓ A ha

/-- Parallel development has the untyped congruence interface needed by full
prefix-program congruence, including weakening under dependent binders. -/
theorem separatedPar_congrRel : CongrRel (fun _ => SeparatedPar D) where
  rfl := .refl _
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN _ R := R.liftN _ _

/-- Exclusion of delta at the displayed universes and of pattern matches at
shorter prefixes preserves a constant spine in one parallel development. -/
theorem SeparatedPar.const_spine_of
    (R : SeparatedPar D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (hno : ∀ {p r pre lv vals}, Pat p r → pre.length ≤ n →
      p.Matches (VExpr.mkApps (.const c ls) pre) lv vals → False)
    (hlen : args.length ≤ n) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (SeparatedPar D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | const =>
    obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj (as' := []) he
    exact ⟨[], rfl, .nil⟩
  | delta hd =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
    exact (hn _ hd).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf (by simp only [List.length_append, List.length_singleton] at hlen; omega) hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | pattern hp hm _ _ _ _ => exact (hno hp hlen (he.symm ▸ hm)).elim
  | bvar | sort | beta | lam | forallE | proj | projIota =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
