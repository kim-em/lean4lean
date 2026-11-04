import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpecializedCarrierChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFamilyBoundary

/-! # Specialization repairs a generic value, but is not substitution closed

The generic value excluded by TerminalDomain has an actual type-specialization
witness. Substituting a function type for its type parameter destroys that
witness. This prevents treating specialization as an ordinary substitution-stable
terminal image in the existing recovery-path proofs.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The generic value of an arbitrary Type parameter admits a specialization
although the previous terminal-domain classification is provably unavailable. -/
theorem sortSpecialization_generic_value
    (hΓ : OnCtx Γ (env.IsType univs)) :
    SortSpecialization (.bvar 0 :: .sort (.succ .zero) :: Γ) (.bvar 0) ∧
    ¬ TerminalDomain (.sort (.succ .zero) :: Γ) (.bvar 0) := by
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓX : OnCtx (.bvar 0 :: .sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓU, _, HasType.bvar .zero⟩
  have hx : env.HasType univs (.bvar 0 :: .sort (.succ .zero) :: Γ) (.bvar 0) (.bvar 1) :=
    .bvar .zero
  exact ⟨SortSpecialization.type_parameter (Ctx.InstN.succ .zero) hΓX (by trivial) hx,
    terminalDomain_type_parameter_failure hΓ⟩

/-- Actual typed substitution can turn a specializable generic value into a
function. Thus arbitrary substitution closure for this new certificate is false,
even though its binder weakening and equality replay laws are proved. -/
theorem sortSpecialization_substitution_failure
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ Γ' σ e T, OnCtx Δ (env.IsType univs) ∧ OnCtx Γ' (env.IsType univs) ∧
      Ctx.SubstEq env univs Γ' σ σ Δ ∧ env.HasType univs Δ e T ∧
      SortSpecialization Δ e ∧ ¬ SortSpecialization Γ' (e.subst σ) := by
  let F : VExpr := .forallE (.sort .zero) (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓX : OnCtx (.bvar 0 :: .sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓU, _, HasType.bvar .zero⟩
  have WI : Ctx.InstN Γ F (.sort (.succ .zero)) 1
      (.bvar 0 :: .sort (.succ .zero) :: Γ) (F :: Γ) := .succ .zero
  have WS := WI.substEq hΓX hF
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  refine ⟨_, _, _, .bvar 0, .bvar 1, hΓX, hΓF, WS, HasType.bvar .zero,
    (sortSpecialization_generic_value hΓ).1, ?_⟩
  intro H
  have hv : env.HasType univs (F :: Γ) (.bvar 0) (.forallE (.sort .zero) (.sort .zero)) :=
    .bvar .zero
  exact H.not_function hv

end Lean4Lean.VEnv.Strengthening
