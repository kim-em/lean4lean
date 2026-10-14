import Lean4Lean.Theory.Typing.Strengthening.NormalSpineExposure

/-! # Exact outer shapes under beta computation

Beta preserves variable and projection heads and distributes over an existing
constant spine. These raw facts isolate the beta paths produced by normal
spine exposure without treating projection iota as beta computation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

theorem beta_variable_fixed (R : BetaRed (.bvar i) out) : out = .bvar i := by
  have aux {e out} (R : BetaRed e out) : ∀ i, e = .bvar i → out = .bvar i := by
    induction R with
    | refl => exact fun _ h => h
    | trans _ _ ih1 ih2 => exact fun i h => ih2 i (ih1 i h)
    | app | lam | forallE | proj | beta => exact fun _ h => by cases h
  exact aux R i rfl

theorem beta_projection_shape (R : BetaRed (.proj s i m) out) :
    ∃ m', out = .proj s i m' := by
  generalize hsrc : VExpr.proj s i m = source at R
  induction R generalizing m with
  | refl => exact ⟨m, hsrc.symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨m', he⟩ := ih1 hsrc
    exact ih2 he.symm
  | proj => cases hsrc; exact ⟨_, rfl⟩
  | app | lam | forallE | beta => cases hsrc

/-- An existing constant head and its exact levels survive beta; the only
changes are pointwise beta paths in the supplied arguments. -/
theorem beta_constant_spine (R : BetaRed (mkApps (.const c ls) args) out) :
    ∃ args', out = mkApps (.const c ls) args' ∧ List.Forall₂ BetaRed args args' := by
  generalize hsrc : mkApps (.const c ls) args = source at R
  induction R generalizing c ls args with
  | refl => exact ⟨args, hsrc.symm, BetaRed.forall₂_refl args⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨args1, he1, H1⟩ := ih1 hsrc
    obtain ⟨args2, he2, H2⟩ := ih2 he1.symm
    exact ⟨args2, he2, H1.trans (fun _ _ _ h h' => h.trans h') H2⟩
  | app Rf Ra ihf iha =>
    obtain ⟨args0, rfl, hf⟩ := RigidHead.const.mkApps_eq_app hsrc
    obtain ⟨args1, he, H1⟩ := ihf hf.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← he], H1.append' (.cons Ra .nil)⟩
  | lam | forallE | proj | beta =>
    have hh := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

end Lean4Lean.VEnv.Strengthening.PureObservation
