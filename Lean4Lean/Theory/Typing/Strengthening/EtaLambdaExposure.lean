import Lean4Lean.Theory.Typing.Strengthening.EtaSubstitution

/-! # Lambda exposure and beta exchange after finite eta paths

A final lambda either preserves an earlier lambda or expands a function.
Dependent body paths are converted to the original domain as intermediate
annotations change. This handles arbitrary eta paths in function position;
it does not yet serialize arbitrary mixed reductions.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem eta_body_chain (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (RA : TypedEtaExpansion Γ A A')
    (R1 : TypedEtaExpansion (A :: Γ) b b') (R2 : TypedEtaExpansion (A' :: Γ) b' b'') :
    TypedEtaExpansion (A :: Γ) b b'' := by
  have hAA := RA.simAt hΓ _ hA
  have hb' := (R1.simAt ⟨hΓ, _, hA⟩ _ hb).hasType.2
  exact R1.trans (R2.defeqDFC hΓ (.succ .zero hAA.symm)
    (hb'.defeqDFC henv (.succ .zero hAA)))

/-- A finite eta path exposing a lambda retains either the original lambda's
body path or a function-eta body path. Both use the original domain's context,
and the displayed domain has its own finite eta path. -/
theorem TypedEtaExpansion.lam_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ e (.lam A b)) (ht : env.HasType univs Γ e T) :
    (∃ A0 b0, e = .lam A0 b0 ∧ TypedEtaExpansion Γ A0 A ∧
      TypedEtaExpansion (A0 :: Γ) b0 b) ∨
    ∃ A0 B, env.HasType univs Γ e (.forallE A0 B) ∧ TypedEtaExpansion Γ A0 A ∧
      TypedEtaExpansion (A0 :: Γ) (.app e.lift (.bvar 0)) b := by
  generalize hout : VExpr.lam A b = target at R
  induction R generalizing A b T with
  | refl => exact .inl ⟨A, b, hout.symm, .refl, .refl⟩
  | structEta =>
    have hh := congrArg getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  | funEta hf => cases hout; exact .inr ⟨_, _, hf, .refl, .refl⟩
  | @trans Γ a middle target R1 R2 ih1 ih2 =>
    rcases ih2 hΓ (R1.simAt hΓ _ ht).hasType.2 hout with
      ⟨A1, b1, hm, RA1, RB1⟩ | ⟨A1, B1, hf, RA1, RB1⟩
    · rcases ih1 hΓ ht hm.symm with ⟨A0, b0, rfl, RA0, RB0⟩ |
        ⟨A0, B0, hf, RA0, RB0⟩
      · obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
        exact .inl ⟨A0, b0, rfl, RA0.trans RA1, eta_body_chain hΓ hA hb RA0 RB0 RB1⟩
      · obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
        have hb := HasType.app (hf.weak henv) (.bvar .zero)
        exact .inr ⟨A0, B0, hf, RA0.trans RA1, eta_body_chain hΓ hA hb RA0 RB0 RB1⟩
    · have hf0 := hf.defeqU_l henv hΓ ⟨_, (R1.simAt hΓ _ ht).symm⟩
      exact .inr ⟨A1, B1, hf0, RA1, (TypedEtaExpansion.app (R1.weakN .one) .refl).trans RB1⟩
  | lam RA RB => cases hout; exact .inl ⟨_, _, rfl, RA, RB⟩
  | app | forallE | proj => cases hout

/-- Arbitrary finite eta expansion in function position commutes with beta at
the resulting application. An existing lambda contracts first; an eta-created
lambda leaves only the residual body and argument expansions. -/
theorem eta_function_beta_compute (hΓ : OnCtx Γ (env.IsType univs))
    (RF : TypedEtaExpansion Γ f (.lam A b)) (RA : TypedEtaExpansion Γ a a')
    (ht : env.HasType univs Γ (.app f a) T) :
    ∃ out, PrefixCompute D Γ (.app f a) out ∧ TypedEtaExpansion Γ out (b.inst a') := by
  obtain ⟨A1, B1, hf, ha⟩ := ht.app_inv henv hΓ
  rcases RF.lam_exposure hΓ hf with ⟨A0, b0, rfl, _, RB⟩ | ⟨A0, B0, hf0, _, RB⟩
  · exact beta_eta_exchange RB (HasType.app_lam_arg hΓ ht) RA
  · obtain ⟨⟨_, hAA⟩, _⟩ := (hf.uniqU henv hΓ hf0).forallE_inv henv hΓ
    exact ⟨_, .refl, function_eta_beta_exchange RB (hAA.defeq ha) RA⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
