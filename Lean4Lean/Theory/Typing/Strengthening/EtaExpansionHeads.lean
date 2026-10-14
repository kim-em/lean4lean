import Lean4Lean.Theory.Typing.Strengthening.EtaExpansion

/-! # Head reflection for the eta-expansion phase

Neither function nor structure expansion can create Pi or sort syntax. On a
sort-typed or function-typed source it also cannot create a constant spine;
any expansions occur inside its existing arguments. These are typed shape
invariants, not a full postponement theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A root structure expansion is incompatible with a source sort or Pi typing. -/
theorem structure_source_not_sort_or_pi (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (ht : env.HasType univs Γ e (mkApps (.const family levels) params))
    (hs : (∃ u, env.HasType univs Γ e (.sort u)) ∨
      ∃ A B, env.HasType univs Γ e (.forallE A B)) : False := by
  obtain ⟨_, hfamily⟩ := ht.isType henv hΓ
  rcases hs with ⟨u, hu⟩ | ⟨A, B, hf⟩
  · have HE := hu.uniqU henv hΓ ht
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ (.sort ((hu.isType henv hΓ).sort_inv henv)))
  · exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily
      (ht.uniqU henv hΓ hf)

/-- On a source typed by a sort or a Pi, a final constant spine was already
present with the same head, levels and arity. Its arguments retain the exact
compatible eta-expansion paths. -/
theorem TypedEtaExpansion.const_spine_source (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ e (mkApps (.const name levels) args))
    (ht : (∃ u, env.HasType univs Γ e (.sort u)) ∨
      ∃ A B, env.HasType univs Γ e (.forallE A B)) :
    ∃ args', e = mkApps (.const name levels) args' ∧
      List.Forall₂ (TypedEtaExpansion Γ) args' args := by
  generalize hout : mkApps (.const name levels) args = target at R
  induction R generalizing name levels args with
  | refl => exact ⟨args, hout.symm, List.Forall₂.rfl (fun _ _ => .refl)⟩
  | structEta hi _ _ hs _ => exact (structure_source_not_sort_or_pi hΓ hi hs ht).elim
  | @trans Γ a b c R1 R2 ih1 ih2 =>
    have hm : (∃ u, env.HasType univs Γ b (.sort u)) ∨
        ∃ A B, env.HasType univs Γ b (.forallE A B) := by
      rcases ht with ⟨u, hu⟩ | ⟨A, B, hf⟩
      · exact .inl ⟨u, (R1.simAt hΓ _ hu).hasType.2⟩
      · exact .inr ⟨A, B, (R1.simAt hΓ _ hf).hasType.2⟩
    obtain ⟨args1, he1, H1⟩ := ih2 hΓ hm hout
    obtain ⟨args0, he0, H0⟩ := ih1 hΓ ht he1.symm
    exact ⟨args0, he0, H0.trans (fun _ _ _ h1 h2 => h1.trans h2) H1⟩
  | @app Γ f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, hfn⟩ := RigidHead.const.mkApps_eq_app hout
    have hsrc : VExpr.WF env univs Γ (.app f a) := by
      rcases ht with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact ⟨_, h⟩
    obtain ⟨A, B, hf, _⟩ := hsrc.app_inv henv hΓ
    obtain ⟨args', hf', Hargs⟩ := ihf hΓ (.inr ⟨A, B, hf⟩) hfn.symm
    refine ⟨args' ++ [_], ?_, Hargs.append' (.cons Ra .nil)⟩
    rw [mkApps_snoc, ← hf']
  | lam | forallE | proj | funEta =>
    have hh := congrArg VExpr.getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Sort-typed eta expansion preserves constant heads and argument arity. -/
theorem TypedEtaExpansion.sort_const_spine_source (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ e (mkApps (.const name levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ args', e = mkApps (.const name levels) args' ∧ args'.length = args.length := by
  obtain ⟨args', he, Hargs⟩ := R.const_spine_source hΓ (.inl ⟨u, ht⟩)
  exact ⟨args', he, Hargs.length_eq⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
