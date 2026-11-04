import Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Eta-converted domains obstruct exact selected lambda exposure

Even a lambda returning Prop has a finite selected recovery path at its native
Pi type but no path at an eta-converted assigned Pi. Its written domain is a
neutral normal form, so computing the lambda cannot repair this discrepancy.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private context native assigned nativeRaw assignedRaw context_wf native_typed
  types_equal erasures normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]
namespace SelectedDomainEtaBoundary
open EtaRecoveryJoinBoundary

private theorem lambda_recovery
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.lam nativeRaw (.sort .zero)) out) :
    out = .forallE nativeRaw (.sort (.succ .zero)) := by
  generalize E : ProofShape.lam nativeRaw (.sort .zero) = e at R
  induction R with
  | lam R =>
    cases E
    rw [R.sort_compute.sort_fixed hhead]
  | convert R H ih =>
    rw [ih E] at H
    apply scoped_normal_fixed H
    intro Δ
    exact ⟨(fun _ H => hhead H), (normal_forms (Step := Step) hhead Δ).1,
      ⟨fun _ H => hhead H, trivial⟩⟩
  | bvar | sort | const | app | forallE | proj => cases E

/-- Exact selected-domain exposure is not a consequence of arbitrary typed
lambda images, even for a type-valued constant body with a native sort-rooted
path. Both native recovery and the sort-rooted alternative fail at the assigned
Pi, and no joint computation can expose a lambda at that assigned domain.
This is an obstruction to that coverage strategy, not to strengthening. -/
theorem typed_lambda_domain_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B f T, OnCtx Γ' (env.IsType univs) ∧
      f = .lam A (.sort .zero) ∧ T = .forallE B (.sort (.succ .zero)) ∧
      env.HasType univs Γ' f T ∧ ¬ IsProof Γ' f ∧
      SortRootedRecovery D Γ' f
        (.forallE (proofErase Γ' A) (.sort (.succ .zero))) 1 ∧
      ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' f) (proofErase Γ' T) ∧
      (∀ body, ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' f) (.lam (proofErase Γ' B) body)) ∧
      ∀ n, ¬ SortRootedRecovery D Γ' f (proofErase Γ' T) n := by
  have hC := context_wf hΓ
  have hCA : OnCtx (native :: context Γ) (env.IsType univs) := ⟨hC, _, native_typed⟩
  have hCB : OnCtx (assigned :: context Γ) (env.IsType univs) :=
    ⟨hC, _, types_equal.hasType.1⟩
  have ht : env.HasType univs (context Γ) (.lam native (.sort .zero))
      (.forallE assigned (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))).defeq
      (HasType.lam native_typed (HasType.sort (by trivial)))
  have hn := not_isProof_function_to_sort hC ht
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EX : proofErase (context Γ) (.lam native (.sort .zero)) =
      .lam nativeRaw (.sort .zero) := by
    rw [show proofErase (context Γ) (.lam native (.sort .zero)) = .lam _ _ from if_neg hn,
      EN, show proofErase (native :: context Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hCA (HasType.sort (by trivial)))]
  have hT : env.HasType univs (context Γ) (.forallE assigned (.sort (.succ .zero)))
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    HasType.forallE types_equal.hasType.1 (HasType.sort (by trivial))
  have ET : proofErase (context Γ) (.forallE assigned (.sort (.succ .zero))) =
      .forallE assignedRaw (.sort (.succ .zero)) := by
    rw [show proofErase (context Γ) (.forallE assigned (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hC hT), EA,
      show proofErase (assigned :: context Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hCB (HasType.sort (by trivial)))]
  have Hno : ∀ body, ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.lam native (.sort .zero)))
      (.lam (proofErase (context Γ) assigned) body) := by
    intro body R
    rw [EX, EA] at R
    have E := scoped_normal_fixed R (fun Δ =>
      ⟨(fun _ H => erased_joint_union_head H),
        (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).1,
        ⟨fun _ H => erased_joint_union_head H, trivial⟩⟩)
    cases E
  refine ⟨context Γ, native, assigned, .lam native (.sort .zero),
    .forallE assigned (.sort (.succ .zero)), hC, rfl, rfl, ht, hn,
    .lam (.type (HasType.sort (by trivial))), ?_, Hno, ?_⟩
  · intro R
    rw [EX, ET] at R
    have E := lambda_recovery erased_joint_union_head R
    cases E
  · intro n H
    rw [ET] at H
    obtain ⟨body, R⟩ := H.selected_domain hC ht hn
    apply Hno body
    rw [EA]
    exact R.mono (fun H => ⟨0, H⟩)

end SelectedDomainEtaBoundary
end Lean4Lean.VEnv.Strengthening
