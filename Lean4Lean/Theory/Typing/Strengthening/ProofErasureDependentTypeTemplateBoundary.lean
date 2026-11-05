import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextJoin

/-! # A type-valued instance need not come from a type-valued template

The local declaration f : (X : Type) -> X gives f Prop : Prop. At a fresh
X : Type, the application f X instead has type X and cannot have any sort type.
Thus contextual instantiation for type bodies does not cover all applications
whose actual result is a type. No special environment or failure of confluence
is used; the separation holds in every well-formed environment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A concrete obstruction to genericizing every type-valued application.
The context is well formed, the actual application f Prop is a proposition,
and the generic application f X has no sort typing at any universe. This does
not refute contextual congruence, type-fork joining, or strengthening. It rules
out inferring generic type-body typing from an instance's type-body typing. -/
theorem dependent_type_instance_not_generic
    (hΓ : OnCtx Γ (env.IsType univs)) :
    let F := VExpr.forallE (.sort (.succ .zero)) (.bvar 0)
    let Δ := F :: Γ
    OnCtx Δ (env.IsType univs) ∧
      env.HasType univs Δ (.app (.bvar 0) (.sort .zero)) (.sort .zero) ∧
      env.HasType univs (.sort (.succ .zero) :: Δ) (.app (.bvar 1) (.bvar 0)) (.bvar 0) ∧
      ∀ v, ¬ env.HasType univs (.sort (.succ .zero) :: Δ)
        (.app (.bvar 1) (.bvar 0)) (.sort v) := by
  let F := VExpr.forallE (.sort (.succ .zero)) (.bvar 0)
  let Δ := F :: Γ
  have hF : env.HasType univs Γ F (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
    .forallE (HasType.sort (by trivial)) (.bvar .zero)
  have hΔ : OnCtx Δ (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hf : env.HasType univs Δ (.bvar 0) F := .bvar .zero
  have hX : env.HasType univs (.sort (.succ .zero) :: Δ) (.bvar 0) (.sort (.succ .zero)) :=
    .bvar .zero
  have hΔX : OnCtx (.sort (.succ .zero) :: Δ) (env.IsType univs) :=
    ⟨hΔ, _, HasType.sort (by trivial)⟩
  have hf' : env.HasType univs (.sort (.succ .zero) :: Δ) (.bvar 1) F := .bvar (.succ .zero)
  have happ : env.HasType univs (.sort (.succ .zero) :: Δ)
      (.app (.bvar 1) (.bvar 0)) (.bvar 0) := .app hf' hX
  refine ⟨hΔ, HasType.app hf (HasType.sort (by trivial)), happ, ?_⟩
  intro v hv
  have HE := (happ.uniqU henv hΔX hv).of_l henv hΔX hX
  have hP : env.HasType univs Δ (.forallE (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have H := HE.instN henv.ordered hP Ctx.InstN.zero
  exact H.toU.symm.sort_forallE_inv henv hΔ

end Lean4Lean.VEnv.Strengthening
