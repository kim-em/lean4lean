import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralFunctionCarrierConversion

/-! # Function-carrier conversion with a literal sort codomain -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every finite carrier guard at a function type into a sort transfers along
actual equality of its neutral source domain. Endpoint reductions are
realized at their original type; carrier reductions replay their actual domain conversion.
No future-body premise or recovery-completeness hypothesis is required. -/
theorem proofErase_computed_joint_neutral_function_carrier_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (hf : env.HasType univs Γ f (.forallE A (.sort v)))
    (hg : env.HasType univs Γ g (.forallE A (.sort v)))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (.sort v)) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ B) (.sort v)) (proofErase Γ f) (proofErase Γ g) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨w, hA⟩, _, hv⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have EU : proofErase (A :: Γ) (.sort v) = .sort v :=
    if_neg (not_isProof_of_sort hΓA hv)
  simpa only [EU] using proofErase_computed_joint_dependent_neutral_function_carrier_convert
    hs hΓ HAB HA hf hg (by simpa only [EU] using H)

end Lean4Lean.VEnv.Strengthening
