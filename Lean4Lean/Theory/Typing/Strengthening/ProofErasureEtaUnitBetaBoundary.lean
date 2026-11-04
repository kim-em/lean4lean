import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaUnitNativeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinedRecoveryBoundary

/-! # One beta step loses even full function-eta common-native coverage

An identity wrapper carries the convertible assigned type explicitly. Removing
that annotation exposes the unit-indexed native mismatch. Adding function eta
therefore does not establish general native source-computation stability.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- In every canonical-Eq environment with a closed positive empty structure,
one typed beta contraction changes exact stage-zero native recovery into failure
of common-native recovery in the entire function-eta union. This includes
arbitrary higher singleton guards on both common-reduct branches. -/
theorem identity_beta_loses_eta_common_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) p) p A ∧
      ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) ∧
      ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) ∧
      ∀ native shared, ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ p) native →
        ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) shared →
        ¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) native shared := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, Hno⟩ := eta_unit_common_native_failure_context heq hs hi hp hx hz hS
  exact ⟨Γ, p, A, hΓ, hp, hn, nativeIdentityExpansion_equal hp,
    proofErase_identity_wrapper_beta hΓ hp hn, proofErase_identity_wrapper_native hΓ hp hn, Hno⟩

end Lean4Lean.VEnv.Strengthening
