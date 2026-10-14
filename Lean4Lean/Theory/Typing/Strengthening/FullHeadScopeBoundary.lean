import Lean4Lean.Theory.Typing.Strengthening.FullRecoveryExistence

/-! # Even full Pi targets need annotation repair

Restricting full reduction to sort-typed sources, or even requiring both source
and target to have a Pi head, does not give exact scope reflection. Compatible
eta may insert an unused binder inside a beta-erased domain argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

/-- A closed type-valued application ignores its identity-function argument. -/
def scopeDomain : VExpr := .app (.lam (tower 1) (.sort .zero)) (ident 0)

/-- Its ordinary typing does not use any hypotheses from the context. -/
theorem scopeDomain_typed : env.HasType univs Γ scopeDomain (.sort (.succ .zero)) :=
  .app (.lam (tower_typed env univs Γ 1) (.sort (by trivial)))
    (ident_typed env univs Γ 0)

/-- Both ends of this full reduction are Pi types, but the target annotation
captures the new binder. Therefore head repair must be allowed to choose other
annotations even for a sort-typed source that already has the desired head. -/
theorem full_pi_target_scope_failure :
    ∃ A B out, env.HasType univs [] (.forallE A B)
        (.sort (.imax (.succ .zero) (.succ .zero))) ∧
      FullRecoveryCompute [.sort .zero] (VExpr.forallE A B).lift out ∧
      (∃ A' B', out = .forallE A' B') ∧ ¬ out.Skips 1 0 := by
  letI := henv.params univs
  let fn : VExpr := .lam (tower 1) (.sort .zero)
  let dom : VExpr := .app fn.lift (EtaScope.expanded (.sort .zero))
  have hD : FullRecoveryCompute [.sort .zero] scopeDomain.lift dom :=
    FullReduction.app .rfl
      (.tail .rfl (@EtaScope.captured_step (henv.params univs) (.sort .zero) []))
  have R : FullRecoveryCompute [.sort .zero]
      (VExpr.forallE scopeDomain (.sort .zero)).lift (.forallE dom (.sort .zero)) :=
    FullReduction.forallE hD .rfl
  refine ⟨scopeDomain, .sort .zero, .forallE dom (.sort .zero),
    .forallE scopeDomain_typed (.sort (by trivial)), R, ⟨_, _, rfl⟩, ?_⟩
  intro hscope
  have hdom : dom.Skips 1 0 := (skips_iff.1 hscope).1 |> skips_iff.2
  have harg : (EtaScope.expanded (.sort .zero)).Skips 1 0 :=
    (skips_iff.1 hdom).2 |> skips_iff.2
  exact EtaScope.captured_not_lift harg

/-- Even the weaker sort-source replay interface excludes full reduction.
The captured annotation occurs in a reduction between actual Pi types. -/
theorem FullRecoveryCompute.not_typeComputeDescent :
    ¬ TypeComputeDescent FullRecoveryCompute := by
  intro hc
  obtain ⟨A, B, target, ht, R, _, hscope⟩ := full_pi_target_scope_failure
  rw [lift_eq_lift'] at R
  have hΓ : OnCtx [.sort .zero] (env.IsType univs) :=
    ⟨trivial, _, HasType.sort (by trivial)⟩
  obtain ⟨out, he, _⟩ := hc R (.skip .refl) trivial hΓ ht
  apply hscope
  rw [he, ← lift_eq_lift']
  exact .liftN

end Lean4Lean.VEnv.Strengthening
