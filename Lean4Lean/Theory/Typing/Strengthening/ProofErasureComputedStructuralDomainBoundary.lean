import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSelectedDomainEtaBoundary

/-! # Assigned-domain recovery still fails in the enlarged computed union

Wrapping the eta-converted neutral domains in Pi makes the assigned domain
structural. Exact recovery and lambda exposure still fail, while the inert
alternative is false by reflexivity. The enlarged computation guards do not remove the normal-annotation obstruction.
This concerns recovery coverage only, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private context native assigned nativeRaw assignedRaw context_wf native_typed
  types_equal erasures normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]
namespace StructuralDomainBoundary

open private lambda_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary

/-- A typed type-valued lambda can fail native recovery and exact-domain
computation while its assigned domain is already a Pi. Thus adding the inert
alternative does not give coverage of arbitrary typed images. The witness
also has no anchored-family recovery at its assigned type, at any cutoff.
This is not a strengthening counterexample. -/
theorem typed_structural_domain_failure_computed (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' f A u, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' f (.forallE A (.sort u)) ∧ ¬ IsProof Γ' f ∧
      CarrierExposure (proofErase Γ' A) ∧
      (¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' f) (proofErase Γ' (.forallE A (.sort u)))) ∧
      (∀ body, ¬ ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' f) (.lam (proofErase Γ' A) body)) ∧
      (∀ cut n, ¬ AnchoredFamilyRecovery D cut Γ' f
        (proofErase Γ' (.forallE A (.sort u))) n) := by
  let X : VExpr := .forallE native (.sort .zero)
  let Y : VExpr := .forallE assigned (.sort .zero)
  let XR : ProofShape := .forallE nativeRaw (.sort .zero)
  let YR : ProofShape := .forallE assignedRaw (.sort .zero)
  have hC := context_wf hΓ
  have hX := HasType.forallE (Γ := context Γ) native_typed (HasType.sort (l := .zero) (by trivial))
  have hXY : env.IsDefEq univs (context Γ) X Y _ :=
    IsDefEq.forallEDF types_equal.symm (HasType.sort (by trivial))
  have hY := hXY.hasType.2
  have ht : env.HasType univs (context Γ) (.lam X (.sort .zero))
      (.forallE Y (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF hXY (HasType.sort (by trivial))).defeq
      (HasType.lam hX (HasType.sort (by trivial)))
  have hn := not_isProof_function_to_sort hC ht
  have hCN : OnCtx (native :: context Γ) (env.IsType univs) := ⟨hC, _, native_typed⟩
  have hCA : OnCtx (assigned :: context Γ) (env.IsType univs) := ⟨hC, _, types_equal.hasType.1⟩
  have hCX : OnCtx (X :: context Γ) (env.IsType univs) := ⟨hC, _, hX⟩
  have hCY : OnCtx (Y :: context Γ) (env.IsType univs) := ⟨hC, _, hY⟩
  have EX : proofErase (context Γ) X = XR := by
    rw [show proofErase (context Γ) X = .forallE _ _ from
      if_neg (not_isProof_of_sort hC hX), (erasures hΓ).1,
      show proofErase (native :: context Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hCN (HasType.sort (by trivial)))]
  have EY : proofErase (context Γ) Y = YR := by
    rw [show proofErase (context Γ) Y = .forallE _ _ from
      if_neg (not_isProof_of_sort hC hY), (erasures hΓ).2,
      show proofErase (assigned :: context Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hCA (HasType.sort (by trivial)))]
  have Ef : proofErase (context Γ) (.lam X (.sort .zero)) = .lam XR (.sort .zero) := by
    rw [show proofErase (context Γ) (.lam X (.sort .zero)) = .lam _ _ from if_neg hn, EX,
      show proofErase (X :: context Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hCX (HasType.sort (by trivial)))]
  have hT := HasType.forallE hY (HasType.sort (l := .succ .zero) (by trivial))
  have ET : proofErase (context Γ) (.forallE Y (.sort (.succ .zero))) =
      .forallE YR (.sort (.succ .zero)) := by
    rw [show proofErase (context Γ) (.forallE Y (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hC hT), EY,
      show proofErase (Y :: context Γ) (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hCY (HasType.sort (by trivial)))]
  have HX : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ) XR := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      (normal_forms (Step := ErasedComputedJointUnion D) erased_computed_joint_union_head Δ).1,
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩
  have Hno : ∀ body, ¬ ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.lam X (.sort .zero))) (.lam (proofErase (context Γ) Y) body) := by
    intro body R
    rw [Ef, EY] at R
    have E := scoped_normal_fixed R (fun Δ =>
      ⟨(fun _ H => erased_computed_joint_union_head H), HX Δ,
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩)
    dsimp [XR, YR, nativeRaw, assignedRaw] at E
    cases E
  refine ⟨context Γ, .lam X (.sort .zero), Y, .succ .zero, hC, ht, hn, ?_, ?_, Hno, ?_⟩
  · rw [EY]; exact .function
  · intro R
    rw [Ef, ET] at R
    have E := lambda_recovery erased_computed_joint_union_head HX R
    dsimp [XR, YR, nativeRaw, assignedRaw] at E
    cases E
  · intro cut n H
    rw [ET] at H
    rcases H.selected_domain_or_inert hC ht hn with ⟨body, R⟩ | Hnone
    · apply Hno body
      rw [EY]
      exact R.mono (fun H => ⟨0, H⟩)
    · exact Hnone .refl .function

end StructuralDomainBoundary
end Lean4Lean.VEnv.Strengthening
