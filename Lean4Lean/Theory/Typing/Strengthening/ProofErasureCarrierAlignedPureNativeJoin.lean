import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPureComputation

/-! # Repairing native selection after pure carrier computation

A native output may be a common reduct rather than the literal assigned type.
Confluence on pure carriers preserves this evidence under any further guarded
computation of the selected carrier. The repair uses only beta/universe steps,
so the native certificate remains at its original stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- If a typed pure carrier computes to an existing native output, any other
finite-stage reduct of that carrier has a common native reduct. The native
recovery stage does not increase, even when the selection path uses later guards. -/
theorem proofErase_carrier_aligned_pure_native_selection
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HP : PureLambda (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ) (proofErase Γ A) native)
    (RS : ScopedCompute (ErasedLevelRecoveredStage D m) (proofEraseCtx Γ) (proofErase Γ A) selected) :
    ∃ out, ScopedTypeRecovery (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) source out ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) selected out := by
  obtain ⟨out, RN', RS'⟩ := proofErase_carrier_aligned_pure_stage_confluent hΓ hA HP RA RS
  exact ⟨out, RN.convert (RN'.mono (fun H => erased_level_primitive_into_stage H n)), RS'⟩

/-- Union-native common-reduct evidence survives every guarded selection path
from the same typed pure carrier. No global guarded confluence is assumed. -/
theorem proofErase_carrier_aligned_pure_union_native_selection
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HP : PureLambda (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A) native)
    (RS : ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A) selected) :
    ∃ out, ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) source out ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) selected out := by
  obtain ⟨out, RN', RS'⟩ := proofErase_carrier_aligned_pure_union_confluent hΓ hA HP RA RS
  exact ⟨out, RN.convert (RN'.mono (fun H => ⟨0, erased_level_primitive_into_stage H 0⟩)), RS'⟩

end Lean4Lean.VEnv.Strengthening
