import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Substitution by an eta-converted function returning a neutral-typed value

The image returns a retained context value. Its assigned input differs from
its written input by eta, while its result type has a protected neutral head.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned assignedRaw context_wf native_typed source_typed
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

private def valueImage : VExpr := .lam native (.bvar 1)
private def valueType : VExpr := .forallE assigned native.lift

private theorem image_typed : env.HasType univs (context Γ) valueImage valueType := by
  have hbody : env.HasType univs (native :: context Γ) (.bvar 1) native.lift :=
    source_typed.weak henv
  have hresult : env.HasType univs (native :: context Γ) native.lift (.sort (.succ .zero)) :=
    native_typed.weak henv
  exact (IsDefEq.forallEDF types_equal.symm hresult).defeq
    (HasType.lam native_typed hbody)

private theorem image_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 0 (context Γ) valueImage (proofErase (context Γ) valueType) 0 := by
  have hC := context_wf hΓ
  have hCA : OnCtx (assigned :: context Γ) (env.IsType univs) :=
    ⟨hC, _, types_equal.hasType.1⟩
  have HA : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  have HC : AnchoredCarrier 1 (proofErase (assigned :: context Γ) native.lift) := by
    rw [proofErase_liftN hC hCA Ctx.LiftN.one native_typed, (erasures hΓ).1]
    exact ⟨2, [.bvar 3], by omega, rfl⟩
  exact StructuralFamilyRecovery.of_neutral_result hC image_typed HA HC

/-- An eta-converted input annotation does not prevent full recursive body
substitution by this function returning a value of the retained neutral type. -/
theorem proofErase_computed_joint_neutral_result_eta_body_inst
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (valueType :: context Γ) a T)
    (hb : env.HasType univs (valueType :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (valueType :: context Γ)) mode
      (proofErase (valueType :: context Γ) a) (proofErase (valueType :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst valueImage)) (proofErase (context Γ) (b.inst valueImage)) :=
  proofErase_computed_joint_zero_compare_inst_structural hs (context_wf hΓ) image_typed
    (image_path hΓ) ha hb H

/-- The same value-producing function also instantiates all first-layer
computations with recursive stage-zero guards and exact substituted outputs. -/
theorem proofErase_computed_joint_neutral_result_eta_firstStage_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (valueType :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (valueType :: context Γ))
      (proofErase (valueType :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst valueImage))
      (out.inst (proofErase (context Γ) valueImage)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs (context_wf hΓ) image_typed
    (image_path hΓ) he R

end Lean4Lean.VEnv.Strengthening
