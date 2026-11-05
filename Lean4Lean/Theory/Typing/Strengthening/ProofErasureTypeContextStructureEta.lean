import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaReplay

/-! # Structure eta inside type contexts from generic instantiation

The generic major recovers its declared family exactly. Its guarded expansion
then instantiates inside an arbitrary type context using TypeInstantiationJoin.
Actual majors and their parameters need no native recovery certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- TypeInstantiationJoin covers every actual admissible structure eta equation
inside an arbitrary typed type context. The generic major supplies the only
native family guard. Actual parameters may be open or dependent, fields may be
retained or erased, and proof majors are handled directly by erasure. -/
theorem TypeInstantiationJoin.contextual_structure_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs Γ (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps))
    (hC : env.HasType univs (VExpr.mkApps (.const family ls) ps :: Γ) C (.sort v)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst m)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst (structExpand family info ls ps m))) shared := by
  obtain ⟨u, hF⟩ := hm.isType henv hΓ
  have hΓF : OnCtx (VExpr.mkApps (.const family ls) ps :: Γ) (env.IsType univs) := ⟨hΓ, u, hF⟩
  have HE := IsDefEq.structEta hi hp hx hm hc
  classical
  by_cases hn : IsProof Γ m
  · have hn' : IsProof Γ (structExpand family info ls ps m) := (isProof_congr hΓ HE).2 hn
    have E : proofErase Γ (C.inst m) = proofErase Γ (C.inst (structExpand family info ls ps m)) := by
      rw [proofErase_instN hΓF hm Ctx.InstN.zero hC,
        proofErase_instN hΓF hc Ctx.InstN.zero hC,
        proofErase_eq_proof.2 hn, proofErase_eq_proof.2 hn']
    exact ⟨_, .refl, E ▸ ScopedCompute.refl⟩
  have hnc : ¬ IsProof Γ (structExpand family info ls ps m) :=
    fun h => hn ((isProof_congr hΓ HE).1 h)
  have EF := proofErase_const_spine hΓ hF (not_isProof_of_sort hΓ hF)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (VExpr.mkApps (.const family ls) ps :: Γ)) (.bvar 0)
      (ProofShape.mkApps (.const family ls) ((ps.map (proofErase Γ)).map (fun a => a.liftN 1))) := by
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, EF,
      ProofShape.liftN_mkApps, ProofShape.liftN] using
      (ScopedTypeRecovery.bvar (Step := ErasedStaticStructureEtaExpansionUnion D)
        (Δ := proofEraseCtx (VExpr.mkApps (.const family ls) ps :: Γ)) (i := 0))
  have RG := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure
    (NativeMaskedStructureExpansion.intro hi hx
      ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
      (by simpa only [List.length_map] using hp) RN))
  obtain ⟨shared, RL, RR⟩ := TypeInstantiationJoin.generic_type_context heq hs HJ hΓ hF hC hm RG
  have EG : (nativeStructureOutput family info ls
      ((ps.map (proofErase Γ)).map (fun a => a.liftN 1)) (.bvar 0)).inst (proofErase Γ m) =
      proofErase Γ (structExpand family info ls ps m) := by
    rw [proofErase_nativeStructureOutput hΓ hi hp hc hnc]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      nativeStructureOutput_subst, List.map_map, Function.comp_def, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.subst, ProofShape.Subst.cons]
  rw [EG, ← proofErase_instN hΓF hc Ctx.InstN.zero hC] at RR
  exact ⟨shared, RL, RR⟩

end Lean4Lean.VEnv.Strengthening
