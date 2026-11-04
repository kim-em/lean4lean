import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard

/-! # Native recovery after structure expansion

Saturated constructors of unindexed structures follow their literal declared
telescope to the family at their own parameters. This supplies native recovery
without native certificates for any parameter or field. In particular a
structure-eta target recovers its selected source family directly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private native_walk_typing from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params]

/-- Every typed saturated constructor of an unindexed registered structure
walks its literal declaration to the exact family at its supplied parameters.
The result does not depend on its arbitrary original assigned type. -/
theorem structure_constructor_native_walk
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections name info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName levels) args) T) :
    InstForallsC env univs Γ (info.ctorType.instL levels) args
      (VExpr.mkApps (.const name levels) (args.take info.nparams)) := by
  obtain ⟨decl, family, ctor, hfamily, hctorMem, hname, hctorUvars, huvars,
    hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
    _, Hraw, hnodup⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  have hdomlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have hc := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  have hs : info.ctorType.instL levels = wrapForalls (doms.map (instL levels)) (result.instL levels) := by
    rw [← hctorType, hshape, instL_wrapForalls]
  obtain ⟨res, HW, _⟩ := HasType.mkApps_telescope henv hΓ hc ⟨_, ht⟩ (by
    change (info.ctorType.instL levels).takeForalls args.length = _
    rw [hs, show args.length = (doms.map (instL levels)).length by simp [hlen, hdomlen]]
    exact takeForalls_wrapForalls _ _)
  have Eres := (hs ▸ HW).wrapForalls_eq (by simp [hlen, hdomlen])
  have hhead' : (result.instL levels).getAppFnArgs.1 = .const name levels := by
    rw [VExpr.getAppFnArgs_instL]
    change result.getAppFnArgs.1.instL levels = _
    rw [hhead, hname]
    simp [VExpr.instL, VLevel.params_map_inst levels (hl.trans huvars.symm)]
  obtain ⟨idx, hresEq, family', hfamily', hname', hidxCount⟩ :=
    (hvalid.instL levels).instOuter (by simpa only [hname] using hhead') args (by omega)
  have hsame : family' = family := List.eq_of_mem_of_nodup_map
    (VInductDecl.typeNames_nodup hnodup) hfamily' hfamily (by simpa only [hname] using hname')
  have hidxEmpty : idx = [] := List.eq_nil_of_length_eq_zero (by rw [hidxCount, hsame, hindices, hx])
  rw [hresEq, hidxEmpty, List.append_nil, hnparams, hname] at Eres
  exact Eres ▸ HW

/-- Saturated structure constructors recover their exact family at any
computation relation, even the empty one. Field native recovery is unnecessary. -/
theorem proofErase_structure_constructor_native
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections name info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName levels) args) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName levels) args)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const info.ctorName levels) args))
      (ProofShape.mkApps (.const name levels) ((args.take info.nparams).map (proofErase Γ))) := by
  have HW := structure_constructor_native_walk hΓ hi hx hlen ht
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have RN := proofErase_const_native_recovery (Step := Step) hΓ
    (henv.ordered.projectionConstructor hi) hw hl HW hn
  have hc := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  have ht' := native_walk_typing hc HW
  obtain ⟨_, hS⟩ := ht'.isType henv hΓ
  rwa [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)] at RN

/-- The target of a masked structure expansion natively recovers the exact
family selected by its source guard. The target computation relation is
arbitrary: no native certificates for parameters, projections or fields are
needed, and no source-computation stability hypothesis is assumed. -/
theorem proofErase_masked_structure_output_native
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hp : ps.length = info.nparams)
    (RN : ScopedTypeRecovery Source (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const family ls) ps)) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (nativeStructureOutput family info ls ps (proofErase Γ e))
      (ProofShape.mkApps (.const family ls) ps) := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht RN
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EA
  have hargs : args.length = info.nparams := by simpa only [List.length_map] using hp
  have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hargs hx heA).2 ha
  have HE := (IsDefEq.structEta hi hargs hx heA hc).symm
  have hn : ¬ IsProof Γ e := fun H => RN.ne_proof (by rw [proofErase_eq_proof.2 H])
  have hnc : ¬ IsProof Γ (structExpand family info ls args e) :=
    fun H => hn ((isProof_congr hΓ HE).2 H)
  have R := proofErase_structure_constructor_native (Step := Target) hΓ hi hx
    (by simp only [List.length_append, List.length_map, List.length_range, hargs]) hc hnc
  have E : (args ++ (List.range info.numFields).map (fun j => VExpr.proj family j e)).take info.nparams = args := by
    rw [← hargs, List.take_append_length]
  rw [E] at R
  change ScopedTypeRecovery Target (proofEraseCtx Γ)
    (proofErase Γ (structExpand family info ls args e)) _ at R
  rwa [proofErase_nativeStructureOutput hΓ hi hargs hc hnc] at R

/-- Any further conversion from the selected family remains available after
structure expansion. This transports the entire native guard tail, not just
its rigid family head. -/
theorem proofErase_masked_structure_output_convert
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hp : ps.length = info.nparams)
    (RN : ScopedTypeRecovery Source (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const family ls) ps))
    (RC : ScopedCompute Target (proofEraseCtx Γ) (ProofShape.mkApps (.const family ls) ps) out) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (nativeStructureOutput family info ls ps (proofErase Γ e)) out :=
  (proofErase_masked_structure_output_native hstep hΓ ht hi hx ha hp RN).convert RC

/-- The selected family guard survives a full-stage structure-eta source
step already at stage zero. All higher conversions after that family can
then be reapplied at their original stage. -/
theorem static_structure_eta_output_stage_zero
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hp : ps.length = info.nparams)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) (ProofShape.mkApps (.const family ls) ps)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) (nativeStructureOutput family info ls ps (proofErase Γ e)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (nativeStructureOutput family info ls ps (proofErase Γ e)) (ProofShape.mkApps (.const family ls) ps) := by
  exact ⟨.base (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hp RN)),
    proofErase_masked_structure_output_native
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht hi hx ha hp RN⟩

end Lean4Lean.VEnv.Strengthening
