import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Neutral carrier alignment does not require recovered-type joins

The eta obstruction to literal joins admits exact carrier-guard transport in
both directions, for all raw endpoints. This tests the new transport rule on
actual typed data and lookup recovery, not just unrelated raw type shapes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf
  source_typed types_equal native_typed normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Every joint stage aligns guards across arbitrary variable-headed carriers,
without requiring any relation between their arguments or a computational join.
Endpoint typings remain separate hypotheses of the sound interpretation. -/
theorem joint_stage_neutral_carrier_iff
    (D : PureObservation.Definitions) (stage : Nat) :
    JointCarrierGuard (ErasedJointStage D stage) Δ (mkApps (.bvar i) args) a b ↔
      JointCarrierGuard (ErasedJointStage D stage) Δ (mkApps (.bvar j) args') a b :=
  ⟨fun H => H.bvar_spine_reindex (erased_joint_stage_head stage),
    fun H => H.bvar_spine_reindex (erased_joint_stage_head stage)⟩

/-- In an actual typed eta-conversion example, a variable has an assigned type
and a recovered native type with no literal common reduct in the joint union.
Nevertheless all carrier guards transfer in both directions at every finite
stage. Thus this obstruction to type joins does not obstruct guard alignment. -/
theorem neutral_recovered_carrier_alignment (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' e T U, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' e T ∧ env.HasType univs Γ' e U ∧ ¬ IsProof Γ' e ∧
      env.IsDefEq univs Γ' T U (.sort (.succ .zero)) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ')
        (proofErase Γ' e) (proofErase Γ' U) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' T) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' U) shared) ∧
      ∀ stage a b, JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
          (proofErase Γ' T) a b ↔
        JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
          (proofErase Γ' U) a b := by
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  have Ee : proofErase (context Γ) (.bvar 0) = .bvar 0 := if_neg hn
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle,
      erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  refine ⟨context Γ, .bvar 0, assigned, native, hC,
    types_equal.symm.defeq source_typed, source_typed, hn, types_equal, ?_, ?_, ?_⟩
  · rw [Ee, EN, ← EO]
    exact .bvar
  · rintro ⟨shared, RT, RU⟩
    rw [EA] at RT
    rw [EN] at RU
    have ET := scoped_normal_fixed RT (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).2)
    have EU := scoped_normal_fixed RU (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).1)
    cases ET.symm.trans EU
  · intro stage a b
    rw [EA, EN]
    exact joint_stage_neutral_carrier_iff D stage
      (args := [.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))]) (args' := [.bvar 2])

end Lean4Lean.VEnv.Strengthening
