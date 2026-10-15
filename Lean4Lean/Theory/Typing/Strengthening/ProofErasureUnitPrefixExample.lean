import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitSingletonStages
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # Universe exposure using a unit-carrier Eq prefix

Two neutral endpoints cannot compare in ScopedCompare at any augmented stage,
but their explicit empty-structure carrier licenses an Eq prefix reduction.
The example has an actual typed source and computes to Prop at stage one. It
establishes useful forward coverage, not separation of all old/new computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A closed registered empty structure gives a concrete two-variable context
and a type-valued Eq recursor that exposes Prop at stage one. Even the augmented
comparison relation cannot compare its distinct variable indices at any stage.
Thus carrying the type at this computational guard avoids the neutral comparison
gap without assuming general certificate composition or recovery completeness. -/
theorem unit_neutral_sort_exposure (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ e (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)) ∧
      ProofShape.ScopedCompute (ErasedUnitSingletonStage D 1) (proofEraseCtx Γ)
        (proofErase Γ e) (.sort .zero) ∧
      ∀ stage mode, ¬ ProofShape.ScopedCompare (ErasedUnitSingletonStage D stage)
        (proofEraseCtx Γ) mode (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hS' : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have H₀₁ := IsDefEq.unitLike hi (params := []) hp.symm hx hf h₀ h₁
  have hw := hS'.sort_r henv hΓ
  let q := eqReflApp (.succ u) S (.bvar 0)
  have hq : env.HasType univs Γ q (eqApp (.succ u) S (.bvar 0) (.bvar 1)) :=
    (IsDefEq.eqApp_r heq hw hS' h₀ H₀₁).defeq (HasType.eqReflApp heq hw hS' h₀)
  let M := constantEqMotive (.succ u) S (.bvar 0) (.sort (.succ .zero))
  let e := eqRecApp (.succ (.succ .zero)) (.succ u) S (.bvar 0) M (.sort .zero) (.bvar 1) q
  have he : env.HasType univs Γ e (.sort (.succ .zero)) :=
    constant_eqRec_typed henv heq (by trivial) hw hΓ hS' h₀
      (HasType.sort (by trivial)) (HasType.sort (by trivial)) h₁ hq
  have HE : env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)) :=
    eqRecApp_simAt henv heq hΓ ⟨_, H₀₁⟩ _ he
  have R := proofErase_unit_singleton_full_forward (D := D) heq hΓ hi hx hf (ps := []) hp.symm he
  have Eprop : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  rw [Eprop] at R
  obtain ⟨_, _, _, _, _, HN⟩ := scoped_unit_typed_composition_failure
    (Stages := ErasedUnitSingletonStage D) erased_unit_singleton_stage_head
    hΓ hi (ps := []) hp.symm hx hf hS' h₀ h₁ (by decide)
  exact ⟨Γ, e, hΓ, he, HE, R, HN⟩

end Lean4Lean.VEnv.Strengthening
