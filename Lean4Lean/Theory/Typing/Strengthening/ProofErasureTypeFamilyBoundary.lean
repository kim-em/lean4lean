import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionCarrierConversion

/-! # An arbitrary type parameter is not a terminal input domain

The target grammar supports dependent terminal domains, but not the generic
polymorphic predicate family. Specializing its type parameter to a function
would contradict the proved non-function invariant of terminal images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A fresh arbitrary type cannot classify all its inhabitants as terminal:
specialization to Prop → Prop produces a function-typed generic value. -/
theorem terminalDomain_type_parameter_failure (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ TerminalDomain (.sort (.succ .zero) :: Γ) (.bvar 0) := by
  intro H
  let F : VExpr := .forallE (.sort .zero) (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hU : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := F) (A₀ := .sort (.succ .zero))).substEq hΓU hF
  have HF : TerminalDomain Γ F := H.subst hΓ W (HasType.bvar .zero)
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hv : env.HasType univs (F :: Γ) (.bvar 0) (.forallE (.sort .zero) (.sort .zero)) :=
    .bvar .zero
  exact (show TerminalImage (F :: Γ) (.bvar 0) from HF).not_function hΓF hv

/-- The polymorphic predicate type is an actual well-typed family. -/
theorem polymorphic_predicate_type_typed : env.HasType univs Γ
    (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero)))
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE (HasType.sort (by trivial))
    (HasType.forallE (HasType.bvar .zero) (HasType.sort (by trivial)))

/-- Terminal-input family readout does not yet cover ∀ A : Type, A → Prop.
This is a certificate-coverage failure, not a declarative counterexample. -/
theorem terminalTypeFamily_polymorphic_predicate_failure
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ TerminalTypeFamily Γ
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))) := by
  intro H
  cases H with
  | function _ HC =>
    cases HC with
    | function HA _ => exact terminalDomain_type_parameter_failure hΓ HA

end Lean4Lean.VEnv.Strengthening
