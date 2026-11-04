import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaNativeExample
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecoveryExample

/-! # Eta expansion does not remove the general capture obstruction

The older obstruction applies to every relation admitting source-typed descent.
It therefore still excludes universal exact native coverage here. For this
example, common-reduct recovery already works at the base stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape Developments EtaScope
variable [Params]

/-- Specialization of the general capture obstruction: no eta-expanded union
certificate can recover an annotation retaining the newly inserted proposition
from a lifted identity. The identity nevertheless has that actual assigned type. -/
theorem eta_expansion_captured_exact_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) ∧
    ¬ ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx (.sort .zero :: Γ))
      (proofErase (.sort .zero :: Γ) (ident 0).lift)
      (proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero))) :=
  ⟨identity_at_captured_pi,
    scoped_identity_captured_not_recovered (erased_eta_expansion_union_descent heq hs) hΓ⟩

/-- The same captured assigned type and the identity's ordinary native output
have a common reduct at stage zero. This does not require erasing the retained
fresh proposition from the selected annotation by an inverse recovery rule. -/
theorem eta_expansion_captured_common_reduct (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ T, ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx (.sort .zero :: Γ))
        (proofErase (.sort .zero :: Γ) (ident 0).lift) T ∧
      ScopedCompute (ErasedEtaExpansionStage D 0) (proofEraseCtx (.sort .zero :: Γ))
        (proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero))) T := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have RN := ErasedRecoverySubstitutionBoundary.identity_plain_recovery
    (Step := fun _ _ => False) hΓS
  rw [← proofEraseCtx_oracle] at RN
  refine ⟨.forallE (.sort .zero) (.sort .zero), ?_, ?_⟩
  · exact RN.scoped (fun H => H.elim)
  · rw [ErasedRecoverySubstitutionBoundary.captured_erasure hΓ]
    exact .beta ErasedRecoverySubstitutionBoundary.captured_beta_plain

/-- Exact assigned recovery fails in the eta-expanded system while the same
actually typed image has base-stage native common-reduct evidence. Thus adding
more descent-preserving primitive rules cannot justify universal exact coverage. -/
theorem eta_expansion_exact_vs_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    (¬ ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx (.sort .zero :: Γ))
      (proofErase (.sort .zero :: Γ) (ident 0).lift)
      (proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero)))) ∧
    ∃ T, ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx (.sort .zero :: Γ))
        (proofErase (.sort .zero :: Γ) (ident 0).lift) T ∧
      ScopedCompute (ErasedEtaExpansionStage D 0) (proofEraseCtx (.sort .zero :: Γ))
        (proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero))) T :=
  ⟨(eta_expansion_captured_exact_failure heq hs hΓ).2,
    eta_expansion_captured_common_reduct hΓ⟩

end Lean4Lean.VEnv.Strengthening
