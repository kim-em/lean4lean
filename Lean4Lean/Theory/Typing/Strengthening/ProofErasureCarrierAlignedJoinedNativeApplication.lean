import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeImages

/-! # Typed uses of joined native substitution

Joined image evidence transports the actual assigned type after substitution,
selects demanded sorts exactly, and composes with expanded image recovery.
The output comparison is available to the existing aligned checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- An expanded pure image can instantiate pure expanded native recovery once
its existing output is joined to the binder annotation. Both native certificates
may have arbitrary finite guard depths inside the union. -/
theorem erased_expansion_union_native_joined_inst_image
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (A :: Δ) e B)
    (HΔ : PureContext Δ) (HA : PureLambda A) (HE : PureLambda e)
    (RP : ScopedTypeRecovery (ErasedExpansionUnion D) Δ p T)
    (HP : PureLambda p) (HT : BetaLevelJoin T A) :
    ∃ B', ScopedTypeRecovery (fun _ _ _ => False) Δ (e.inst p) B' ∧ BetaLevelJoin B' (B.inst p) := by
  obtain ⟨T', RP', HT'⟩ := erased_expansion_union_native_beta_basis RP HΔ HP
  exact erased_expansion_union_native_joined_inst R HΔ HA HE RP' (HT'.trans HT)

/-- Joined image substitution retains an exact demanded sort at expanded stage
zero, using one final explicit universe conversion if needed. Exact image type
recovery and purity of the target image syntax are not required. -/
theorem erased_expansion_union_native_joined_sort_subst
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ e (.sort u))
    (HΔ : PureContext Δ) (HE : PureLambda e) (hu : u.WF univs)
    (W : JoinedNativeImages Δ Δ' τ) :
    ScopedTypeRecovery (ErasedExpansionStage D 0) Δ' (e.subst τ) (.sort u) := by
  obtain ⟨T, RN, HJ⟩ := erased_expansion_union_native_joined_subst R HΔ HE W
  exact proofErase_carrier_aligned_joined_sort_exact
    (fun H => erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0))
    (RN.mono (fun H => H.elim)) HJ hu

/-- Native evidence joined to an actual assigned type survives typed
substitution by joined images. The target evidence uses beta only, and its
comparison to the actual substituted type is available at expanded stage zero. -/
theorem proofErase_carrier_aligned_joined_native_subst
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (he : env.HasType univs Γ e A)
    (HΔ : PureContext (proofEraseCtx Γ)) (HE : PureLambda (proofErase Γ e))
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) T)
    (HT : BetaLevelJoin T (proofErase Γ A))
    (HI : JoinedNativeImages (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) :
    ∃ T', ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) T' ∧
      BetaLevelJoin T' (proofErase Γ₀ (A.subst σ)) ∧
      ComputedJointCompare (ErasedExpansionStage D 0) (proofEraseCtx Γ₀) false
        T' (proofErase Γ₀ (A.subst σ)) := by
  obtain ⟨T', RN, HJ⟩ := erased_expansion_union_native_joined_subst R HΔ HE HI
  obtain ⟨u, hA⟩ := he.isType henv W.wf
  have HJ' := HJ.trans (HT.subst (σ := τ))
  rw [← proofErase_subst_with hΓ₀ W he ES] at RN
  rw [← proofErase_subst_with hΓ₀ W hA ES] at HJ'
  exact ⟨T', RN, HJ', proofErase_carrier_aligned_raw_join_compare
    (fun H => erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0))
    hΓ₀ (hA.subst henv.orderedStrong W hΓ₀) HJ'⟩

/-- Substituting joined images into a native Pi demand retains Pi selection
and a computed domain comparison in the actual target context. The selected
codomain remains joined to the substituted original codomain. -/
theorem proofErase_carrier_aligned_joined_native_pi_subst
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hA : env.HasType univs Γ A (.sort u))
    (HΔ : PureContext (proofEraseCtx Γ)) (HE : PureLambda e)
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) e
      (.forallE (proofErase Γ A) B))
    (HI : JoinedNativeImages (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) :
    ∃ X Y, ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ₀)
        (e.subst τ) (.forallE X Y) ∧
      ComputedJointCompare (ErasedExpansionStage D 0) (proofEraseCtx Γ₀) false
        X (proofErase Γ₀ (A.subst σ)) ∧ BetaLevelJoin Y (B.subst τ.lift) := by
  obtain ⟨T', RN, HJ⟩ := erased_expansion_union_native_joined_subst R HΔ HE HI
  change BetaLevelJoin T' (.forallE ((proofErase Γ A).subst τ) (B.subst τ.lift)) at HJ
  rw [← proofErase_subst_with hΓ₀ W hA ES] at HJ
  exact proofErase_carrier_aligned_joined_pi_selection
    (fun H => erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0))
    hΓ₀ (hA.subst henv.orderedStrong W hΓ₀) (RN.mono (fun H => H.elim)) HJ

end Lean4Lean.VEnv.Strengthening
