import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativePiExample

/-! # Selected-domain comparison without exact assigned-Pi recovery

The existing identity-redex/universe-alias witness now carries the inferred
domain comparison produced by native Pi selection. The negative exact-recovery
result still holds in the entire recovered-carrier union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Native selection supplies its actual Pi typing, exact recovery and inferred
domain comparison even when the assigned Pi has no exact recovery in the full
union. This uses the concrete native identity-redex witness, not a recovery oracle. -/
theorem carrier_aligned_selected_domain_without_assigned_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ Γ f A B A' B', OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE A B) ∧ env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ A') ∧
      ¬ ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.forallE A B)) := by
  obtain ⟨Γ, f, A, B, T, hΓ, hf, R, H, _, Hno⟩ := carrier_aligned_native_pi_residual_strict heq hs
  obtain ⟨A', B', hf', R', HD⟩ := proofErase_carrier_aligned_recovered_pi_domain
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head hΓ hf R H
  exact ⟨Γ, f, A, B, A', B', hΓ, hf, hf', R', HD, Hno⟩

end Lean4Lean.VEnv.Strengthening
