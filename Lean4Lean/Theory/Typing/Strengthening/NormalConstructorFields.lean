import Lean4Lean.Theory.Typing.Strengthening.BetaSpineShape
import Lean4Lean.Theory.Typing.Strengthening.EtaNormalHeadReflection

/-! # Field constraints for a normal constructor-spine comparison

At a non-propositional rigid family type, normal comparison of constant spines
exposes pointwise beta paths followed by normal argument comparisons. A sort-
typed variable or projection cannot exchange its outer shape through those
paths. This module does not assert arbitrary eta-spine exposure.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Normal comparison between constant spines at a rigid non-propositional
family type yields pointwise beta/normal argument comparisons. -/
theorem normal_constructor_fields (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info)
    (hnp : ¬ env.HasType univs Γ (mkApps (.const family familyLevels) params) (.sort .zero))
    (ht : env.HasType univs Γ (mkApps (.const c ls) args)
      (mkApps (.const family familyLevels) params))
    (H : NormalEq Γ (mkApps (.const c ls) args) (mkApps (.const c' ls') args')) :
    ∃ args0, List.Forall₂ BetaRed args args0 ∧ List.Forall₂ (NormalEq Γ) args0 args' := by
  obtain ⟨n, H⟩ := H
  rcases normal_spine_expose_beta hΓ .const n H (bs := []) .nil ht with
    hp | ⟨head, args0, hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, ha, hf⟩
  · exact (hnp hp).elim
  · simp only [mkApps_nil] at RB
    obtain ⟨args1, he, HR⟩ := beta_constant_spine RB
    have he' := congrArg getAppArgs he
    cases hh with
    | const _ =>
      simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at he'
      subst args0
      exact ⟨args1, HR, by simpa only [List.append_nil] using HA⟩
  · simp only [mkApps_nil] at RB
    obtain ⟨args0, he, _⟩ := beta_constant_spine RB
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
  · have hz' := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2
    obtain ⟨_, hfamily⟩ := hz'.isType henv hΓ
    exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hfamily
      (hz'.uniqU henv hΓ hz)).elim

/-- Beta followed by normal comparison cannot turn a projection into a
non-proof, non-function variable. -/
theorem projection_beta_normal_not_variable (hΓ : OnCtx Γ (env.IsType univs))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (R : BetaRed (.proj family index major) out)
    (H : NormalEq Γ out (.bvar i)) : False := by
  obtain ⟨major', rfl⟩ := beta_projection_shape R
  have he := normal_bvar_eq_of_nonfunction (sortTyped_not_isProof hΓ hv)
    (fun A B hf => (hv.uniqU henv hΓ hf).sort_forallE_inv henv hΓ) (H.symm hΓ)
  cases he

/-- A sort-typed variable is fixed even when beta precedes normal comparison. -/
theorem variable_beta_normal_fixed (hΓ : OnCtx Γ (env.IsType univs))
    (hv : env.HasType univs Γ (.bvar i) (.sort u))
    (R : BetaRed (.bvar i) mid) (H : NormalEq Γ mid out) : out = .bvar i := by
  cases beta_variable_fixed R
  exact normal_bvar_eq_of_nonfunction (sortTyped_not_isProof hΓ hv)
    (fun A B hf => (hv.uniqU henv hΓ hf).sort_forallE_inv henv hΓ) H

end Lean4Lean.VEnv.Strengthening.PureObservation
