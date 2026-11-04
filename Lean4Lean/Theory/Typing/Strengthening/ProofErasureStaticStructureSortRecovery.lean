import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortReadout

/-! # Exact universe demands from common native certificates -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A common native certificate against a universe meets the exact assigned
sort demand. Beta readout removes control frames; one universe conversion
restores the original level. No confluence or exact image coverage is assumed. -/
theorem static_structure_exact_sort_of_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.sort u) shared) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.sort u) := by
  obtain ⟨v, HE, _, R⟩ := static_structure_native_sort_of_common heq hs hΓ ht RN RC
  obtain ⟨_, hU⟩ := ht.isType henv hΓ
  exact R.convert (.base ⟨0, .inl (.inr (.sort HE.symm (hU.sort_inv henv.ordered)))⟩)

/-- Dependent function formation needs only common native certificates for
its domain and codomain. Each assigned universe can be recovered exactly,
including when its common output contains temporary expansion frames. -/
theorem static_structure_forallE_of_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (RNA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) sharedA)
    (RCA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.sort u) sharedA)
    (RNB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) sharedB)
    (RCB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (.sort v) sharedB) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.sort (.imax u v)) := by
  have RA := static_structure_exact_sort_of_common heq hs hΓ hA RNA RCA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have RB := static_structure_exact_sort_of_common heq hs hΓA hB RNB RCB
  rw [show proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))]
  exact .forallE RA RB

end Lean4Lean.VEnv.Strengthening
