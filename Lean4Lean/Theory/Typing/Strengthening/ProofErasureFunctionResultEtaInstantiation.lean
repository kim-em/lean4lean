import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedBodyInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Structural eta-domain images returning another function

The outer lambda uses a structural converted input. Its body is a lambda
returning a retained context value, so its selected result is itself a Pi.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned assignedRaw context_wf native_typed source_typed
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

private def writtenDomain : VExpr := .forallE native (.sort .zero)
private def assignedDomain : VExpr := .forallE assigned (.sort .zero)
private def resultType : VExpr := .forallE native.lift native.lift.lift
private def imageBody : VExpr := .lam native.lift (.bvar 2)
private def functionImage : VExpr := .lam writtenDomain imageBody
private def functionType : VExpr := .forallE assignedDomain resultType

private theorem written_typed : env.HasType univs (context Γ) writtenDomain
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  HasType.forallE native_typed (HasType.sort (by trivial))

private theorem body_typed : env.HasType univs (writtenDomain :: context Γ) imageBody resultType := by
  have hN : env.HasType univs (writtenDomain :: context Γ) native.lift (.sort (.succ .zero)) :=
    native_typed.weak henv
  have hx : env.HasType univs (writtenDomain :: context Γ) (.bvar 1) native.lift :=
    source_typed.weak henv
  exact HasType.lam hN (hx.weak henv)

private theorem image_typed : env.HasType univs (context Γ) functionImage functionType := by
  have HKK := IsDefEq.forallEDF (Γ := context Γ) types_equal (HasType.sort (l := .zero) (by trivial))
  have hN : env.HasType univs (writtenDomain :: context Γ) native.lift (.sort (.succ .zero)) :=
    native_typed.weak henv
  have hE := HasType.forallE hN (hN.weak henv)
  exact (IsDefEq.forallEDF HKK.symm hE).defeq (HasType.lam written_typed body_typed)

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (writtenDomain :: context Γ) imageBody
      (proofErase (writtenDomain :: context Γ) resultType) 1 := by
  have hC := context_wf hΓ
  have hC₁ : OnCtx (writtenDomain :: context Γ) (env.IsType univs) := ⟨hC, _, written_typed⟩
  have hN : env.HasType univs (writtenDomain :: context Γ) native.lift (.sort (.succ .zero)) :=
    native_typed.weak henv
  have hC₂ : OnCtx (native.lift :: writtenDomain :: context Γ) (env.IsType univs) := ⟨hC₁, _, hN⟩
  have hE := HasType.forallE hN (hN.weak henv)
  have HN : AnchoredCarrier 2 (proofErase (native.lift :: writtenDomain :: context Γ) native.lift.lift) := by
    rw [proofErase_liftN hC₁ hC₂ Ctx.LiftN.one hN,
      proofErase_liftN hC hC₁ Ctx.LiftN.one native_typed, (erasures hΓ).1]
    exact ⟨3, [.bvar 4], by omega, rfl⟩
  rw [show proofErase (writtenDomain :: context Γ) resultType = .forallE _ _ from
    if_neg (not_isProof_of_sort hC₁ hE)]
  exact .lam (.neutral HN)

private theorem image_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 0 (context Γ) functionImage (proofErase (context Γ) functionType) 2 := by
  have HA : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  exact StructuralFamilyRecovery.of_converted_body (context_wf hΓ) types_equal HA image_typed (body_path hΓ)

/-- A structural eta-domain image returning a function instantiates every
common-typed stage-zero body comparison. The selected result is a Pi, so
neither sort-result nor neutral-result terminal coverage alone suffices. -/
theorem proofErase_computed_joint_function_result_eta_body_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (functionType :: context Γ) a T)
    (hb : env.HasType univs (functionType :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (functionType :: context Γ)) mode
      (proofErase (functionType :: context Γ) a) (proofErase (functionType :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst functionImage)) (proofErase (context Γ) (b.inst functionImage)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs (context_wf hΓ) image_typed
    (image_path hΓ) ha hb H

/-- The same function-returning image preserves every first-layer computation
and its exact substituted output. -/
theorem proofErase_computed_joint_function_result_eta_firstStage_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (functionType :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (functionType :: context Γ))
      (proofErase (functionType :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst functionImage))
      (out.inst (proofErase (context Γ) functionImage)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs (context_wf hΓ) image_typed
    (image_path hΓ) he R

end Lean4Lean.VEnv.Strengthening
