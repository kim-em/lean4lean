import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointComputedRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Computing an image can repair unavailable exact recovery

An identity beta redex retains a syntactically noncanonical universe in every
recovered type. Its reduct Prop recovers Sort 1. Both are assigned Sort 1 by
ordinary universe conversion, so computing before recovery strictly enlarges
the admitted class of substitution images, even at computation stage zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private declared declared_equiv image_typed erase_sort
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]
namespace ComputedRecoveryBoundary

private def source : VExpr := .app (.lam (.sort declared) (.bvar 0)) (.sort .zero)
private def sourceRaw : ProofShape := .app (.lam (.sort declared) (.bvar 0)) (.sort .zero)

private theorem identity_typed : env.HasType univs Γ (.lam (.sort declared) (.bvar 0))
    (.forallE (.sort declared) (.sort declared)) :=
  .lam (.sort (by trivial)) (.bvar .zero)

private theorem source_typed : env.HasType univs Γ source (.sort (.succ .zero)) := by
  have H : env.HasType univs Γ source (.sort declared) := .app identity_typed image_typed
  exact (IsDefEq.sortDF (by trivial) (by trivial) declared_equiv).defeq H

private theorem erase_source (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ source = sourceRaw := by
  have hC : OnCtx (.sort declared :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hv : env.HasType univs (.sort declared :: Γ) (.bvar 0) (.sort declared) := .bvar .zero
  change proofErase Γ (.app _ _) = _
  rw [show proofErase Γ (.app (.lam (.sort declared) (.bvar 0)) (.sort .zero)) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ source_typed)]
  rw [show proofErase Γ (.lam (.sort declared) (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ identity_typed)]
  rw [erase_sort hΓ (by trivial), erase_sort hΓ (by trivial)]
  rw [show proofErase (.sort declared :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hC hv)]
  rfl

private theorem identity_recovery
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.lam (.sort u) (.bvar 0)) out) :
    out = .forallE (.sort u) (.sort u) := by
  generalize E : ProofShape.lam (.sort u) (.bvar 0) = e at R
  induction R generalizing u with
  | lam R =>
    cases E
    have H := R.bvar_compute
    change ScopedCompute Step _ (.sort u) _ at H
    rw [H.sort_fixed hhead]
  | convert R H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨fun _ H => hhead H, trivial⟩⟩
  | bvar | sort | const | app | forallE | proj => cases E

private theorem source_recovery
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ sourceRaw out) : out = .sort declared := by
  generalize E : sourceRaw = e at R
  induction R with
  | app R =>
    cases E
    have H := identity_recovery hhead R
    cases H
    rfl
  | convert R H ih =>
    rw [ih E] at H
    exact H.sort_fixed hhead
  | bvar | sort | const | lam | forallE | proj => cases E

private theorem lambda_source_recovery
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.lam (.sort .zero) sourceRaw) out) :
    out = .forallE (.sort .zero) (.sort declared) := by
  generalize E : ProofShape.lam (.sort .zero) sourceRaw = e at R
  induction R with
  | lam R =>
    cases E
    rw [source_recovery hhead R]
  | convert R H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), ⟨fun _ H => hhead H, trivial⟩,
      ⟨fun _ H => hhead H, trivial⟩⟩
  | bvar | sort | const | app | forallE | proj => cases E

/-- At stage zero an actual non-proof lambda image computes to an image
recovering its assigned type, although the original lambda has no such recovery
in the entire joint union. This strict extension includes lambda arguments,
the shape involved in the original matched-beta residue. -/
theorem strict_extension (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ x A image, (∃ domain body, x = .lam domain body) ∧
      env.HasType univs Γ x A ∧ ¬ IsProof Γ x ∧
      ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ x) image ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) image (proofErase Γ A) ∧
      ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A) := by
  have hC : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have ht : env.HasType univs Γ (.lam (.sort .zero) source)
      (.forallE (.sort .zero) (.sort (.succ .zero))) := .lam (.sort (by trivial)) source_typed
  have hn := not_isProof_function_to_sort hΓ ht
  have EX : proofErase Γ (.lam (.sort .zero) source) = .lam (.sort .zero) sourceRaw := by
    rw [show proofErase Γ (.lam (.sort .zero) source) = .lam _ _ from if_neg hn,
      erase_sort hΓ (by trivial), erase_source hC]
  have hT : env.HasType univs Γ (.forallE (.sort .zero) (.sort (.succ .zero)))
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    .forallE (.sort (by trivial)) (.sort (by trivial))
  have ET : proofErase Γ (.forallE (.sort .zero) (.sort (.succ .zero))) =
      .forallE (.sort .zero) (.sort (.succ .zero)) := by
    rw [show proofErase Γ (.forallE (.sort .zero) (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hT), erase_sort hΓ (by trivial), erase_sort hC (by trivial)]
  refine ⟨.lam (.sort .zero) source, .forallE (.sort .zero) (.sort (.succ .zero)),
    .lam (.sort .zero) (.sort .zero), ⟨_, _, rfl⟩, ht, hn, ?_, ?_, ?_⟩
  · rw [EX]
    exact .lam .refl (.beta .beta)
  · rw [ET]
    exact .lam (.sort (by trivial))
  · intro R
    rw [EX, ET] at R
    have H := lambda_source_recovery erased_joint_union_head R
    cases H

/-- Computing the image does not eliminate the eta-converted assigned-type
obstruction: a variable is fixed by the whole joint union, and its native and
assigned types have no computational join. Computed recovery remains an
explicit hypothesis, not a consequence of arbitrary non-proof typing. -/
theorem eta_variable_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' x T, OnCtx Γ' (env.IsType univs) ∧ env.HasType univs Γ' x T ∧ ¬ IsProof Γ' x ∧
      ∀ image, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' x) image →
        ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') image (proofErase Γ' T) := by
  obtain ⟨Γ', x, T, out, rfl, hΓ', hx, hn, _, _, Hno⟩ :=
    EtaRecoveryJoinBoundary.typed_join_failure D hΓ
  refine ⟨Γ', .bvar 0, T, hΓ', hx, hn, ?_⟩
  intro image RC HR
  have EX : proofErase Γ' (.bvar 0) = .bvar 0 := if_neg hn
  rw [EX] at RC
  have EI := RC.bvar_fixed erased_joint_union_head
  rw [EI, ← EX] at HR
  exact Hno _ _ HR .refl .refl

end ComputedRecoveryBoundary
end Lean4Lean.VEnv.Strengthening
