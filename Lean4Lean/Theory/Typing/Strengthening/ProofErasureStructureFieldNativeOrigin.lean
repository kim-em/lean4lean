import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureFieldNativeWalk
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFirstProjectionPivot

/-! # Native origins of independently computed structure fields

For a structure with no parameters, the selected family has no occurrences of
its fields. Its expanded constructor has an exact native walk, supplied by the
original major certificate. Arbitrary independent field computations preserve
the family as an ancestor of every selected native output. Any pivot recovering
that same family can consequently replay the entire output conversion tail.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_walk_typing from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every selected native output of independently computed expansion fields
is reachable from the parameter-free family. Conversions at all intermediate
constructor prefixes are included, as are dependent and proof fields. No native
certificates are required for computed fields. -/
theorem structure_fields_computed_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls [] m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ m) (.const s ls))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (RO : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) fields) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.const s ls) out := by
  have HW := structure_fields_retained_native_walk hΓ hi hp hx HT hd hw hl hc RN
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  have hc' := native_walk_typing hctor HW.typed
  obtain ⟨u, hS⟩ := hc'.isType henv hΓ
  have R := static_structure_computed_const_native heq hs hΓ
    (henv.ordered.projectionConstructor hi) hw hl HW HA RO
  rwa [show proofErase Γ (.const s ls) = .const s ls from if_neg (not_isProof_of_sort hΓ hS)] at R

/-- Any pivot with the same parameter-free family recovers every native output
of the independently computed constructor. The pivot may be raw and need not
retain any of the fields. This is exact output transfer for this constructor
frame, not a general transfer law for dependent argument contexts. -/
theorem native_transfer_computed_structure_fields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls [] m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ m) (.const s ls))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) pivot (.const s ls)) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) fields) pivot := by
  intro out RO
  exact RP.convert (structure_fields_computed_native_origin heq hs hΓ hi hp hx HT hd hw hl hc RN HA RO)

/-- The same frame retains all four root expansion squares after independent
field computations. The historical paths and final beta competitor are supplied
by the surrounding development; no local type-fork hypothesis is required. -/
theorem computed_structure_fields_expansion_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls [] m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ m) (.const s ls))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) pivot (.const s ls))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot target)
    (Rβ : ProofShape.BetaRed (ProofShape.mkApps (.const info.ctorName ls) fields) target)
    (RE : ConstantExpansion (ProofShape.mkApps (.const info.ctorName ls) fields) expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName ls) fields) expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName ls) fields) expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName ls) fields) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original shared ∧
      ProofShape.BetaRed expanded shared :=
  native_pivot_expansion_square heq hs Rbefore Rafter
    (native_transfer_computed_structure_fields heq hs hΓ hi hp hx HT hd hw hl hc RN HA RP) Rβ RE

/-- A guarded parameter-free structure expansion provides all the ordinary
witnesses needed for native origin. Its masked fields can compute independently;
no telescope, level-validity or field-typing premise is left to the caller. -/
theorem parameter_free_structure_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ m T)
    (hi : env.projections s info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ m) (.const s ls))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((List.range info.numFields).map (nativeStructureField s info ls (proofErase Γ m))) fields)
    (RO : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) fields) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.const s ls) out := by
  obtain ⟨A, hm, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  obtain rfl := erase_const_inv EA
  have hc := (StructureReplay.expansion_typed_iff henv hΓ hi (params := []) (by simp [hp]) hx hm).2 hadm
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hc⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  obtain ⟨doms, result, HT⟩ := projection_telescope_exists hi hw
  have hd : doms.length = info.nparams + info.numFields := by
    have H := HT.numFields
    omega
  have EF : (projsOf s m info.numFields).map (proofErase Γ) =
      (List.range info.numFields).map (nativeStructureField s info ls (proofErase Γ m)) := by
    classical
    simp only [projsOf, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro j hj
    have H := structure_proofField_iff hΓ hi (ps := []) (by simp [hp]) (List.mem_range.1 hj) hc
    unfold nativeStructureField
    by_cases hf : StructureReplay.ProofField env univs info ls j
    · rw [if_pos hf, proofErase_eq_proof.2 (H.1 hf)]
    · rw [if_neg hf]
      exact if_neg (fun h => hf (H.2 h))
  exact structure_fields_computed_native_origin heq hs hΓ hi hp hx HT hd hw hl hc RN (EF ▸ HA) RO

end Lean4Lean.VEnv.Strengthening
