import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedProjectionRecipe

/-! # The local type fork exposed by dependent projection transport

Two major paths with a common output induce a common output of every selected
dependent field recipe. A native conversion tail creates a fork at the source
recipe. Joining that particular fork supplies common native coverage at the
other projection; no native completeness or global type-fork premise is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Common computation of two majors gives a common computation of their
complete dependent recipes. Both source projections are typed, while the common
major is raw and requires neither typing nor a native family certificate. -/
theorem typed_projectionType_common_major
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (ht' : env.HasType univs Γ (.proj s j m') U') (hn' : ¬ IsProof Γ (.proj s j m'))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (hm' : env.HasType univs Γ m' (VExpr.mkApps (.const s ls) args))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m) common)
    (R' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m') common) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m))
        (projectionType s info doms j hj (args.map (proofErase Γ)) common) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m'))
        (projectionType s info doms j hj (args.map (proofErase Γ)) common) :=
  ⟨typed_projectionType_compute_major heq hs hΓ hi HT hj ht hn hm R,
    typed_projectionType_compute_major heq hs hΓ hi HT hj ht' hn' hm' R'⟩

/-- A native projection tail transfers up to a common native output when the
single fork at its source recipe joins. The explicit joining premise remains
open in general. It is not exact native-output transfer and is not asserted to
be a strictly smaller sufficient strengthening obligation. -/
theorem projection_native_tail_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (ht' : env.HasType univs Γ (.proj s j m') U') (hn' : ¬ IsProof Γ (.proj s j m'))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (hm' : env.HasType univs Γ m' (VExpr.mkApps (.const s ls) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m') (ProofShape.mkApps (.const s ls) (args.map (proofErase Γ))))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m) common)
    (R' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m') common)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) selected)
    (joinRecipe : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared) :
    ∃ shared, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.proj s j m')) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) selected shared := by
  obtain ⟨RM, RM'⟩ := typed_projectionType_common_major heq hs hΓ hi HT hj ht hn ht' hn' hm hm' R R'
  obtain ⟨shared, RS, RR⟩ := joinRecipe RC RM
  have hlen := (retained_projection_family_facts hΓ hi ht hn hm).2.2.1
  have RP := ScopedTypeRecovery.proj hi HT hj
    (by simpa only [List.length_map] using hlen) RN
  refine ⟨shared, ?_, RS⟩
  rw [show proofErase Γ (.proj s j m') = .proj s j (proofErase Γ m') from if_neg hn']
  exact RP.convert (RM'.trans RR)

end Lean4Lean.VEnv.Strengthening
