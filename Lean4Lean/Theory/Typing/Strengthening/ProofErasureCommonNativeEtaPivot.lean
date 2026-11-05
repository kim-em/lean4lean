import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePivotPrimitiveSquare

/-! # Function-eta squares using common native type output

The pivot need not recover the original chosen Pi exactly. A common computation
of that Pi and a native pivot type suffices. Pi-origin readout supplies a new
annotation, its original sort and the forward annotation path for the long side.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Common native output replaces exact native-output transfer in the eta
square. The source annotation computes to the pivot's new annotation, while
both bodies reach the same raw value. No global type-fork joining is assumed;
the common type output is explicit and must be constructed by the caller. -/
theorem common_native_eta_pivot_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot target)
    (Rβ : ProofShape.BetaRed source target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) commonType) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.lam (proofErase Γ A) (.app (source.liftN 1) (etaArgument u))) shared := by
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RT
  obtain ⟨X, Y, ⟨A', B', HAA', _, EA', _, RA, _⟩, Rclean⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RT
  have SD : DomainSort (proofEraseCtx Γ) X u := ⟨Γ, A', hΓ, rfl, HAA'.hasType.2, EA'⟩
  have RNP := RN.convert (.beta Rclean)
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot
      (.lam X (.app (pivot.liftN 1) (etaArgument u))) :=
    .base (erased_static_structure_eta_expansion_union_eta (.intro RNP SD))
  refine ⟨.lam X (.app (target.liftN 1) (etaArgument u)), ?_, ?_⟩
  · exact Rbefore.trans (RE.trans (.lam .refl
      (.app (static_structure_compute_under_domain heq hs SD Rafter) .refl)))
  · exact (ScopedCompute.beta (.lam .refl (.app Rβ.liftN .refl))).trans (.lam RA .refl)

end Lean4Lean.VEnv.Strengthening
