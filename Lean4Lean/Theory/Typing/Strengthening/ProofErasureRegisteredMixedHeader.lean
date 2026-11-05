import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMixedFamilySupply
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedConstructorFamily
import Lean4Lean.Theory.Typing.PrefixUnfolding.NormalCongruence

/-! # Registered constructor histories with matching literal family headers

Registered unindexed constructors have a literal parameter/field split and a
result independent of fields. The family header need not share that literal
split under the general environment judgment; the explicit header condition
below isolates that remaining declaration-level requirement.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open _root_.Lean4Lean.InductiveSignature (vars)
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params] {D : PureObservation.Definitions}

/-- A registered unindexed constructor's raw result is exactly its family
opened on the parameter variables and lifted past all fields. This is a
syntactic consequence of registration, without a normalized family header. -/
theorem registered_constructor_mixed_shape
    (hi : env.projections s info) (hx : info.nindices = 0)
    (hl : ls.length = info.uvars) :
    ∃ ps fs, ps.length = info.nparams ∧ fs.length = info.numFields ∧
      info.ctorType.instL ls = VExpr.wrapForalls ps
        (VExpr.wrapForalls fs ((etaOpen ps.length (.const s ls)).liftN fs.length)) := by
  obtain ⟨decl, family, ctor, hfamily, _, hname, _, huvars,
    hnparams, hindices, _, _, hctorType, _, _, _, Hraw, hnodup⟩ :=
    henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  obtain ⟨family', hfamily', htarget, levels, _, _, hargs, hparams⟩ := hvalid
  have hname' : family'.name = family.name := by
    rcases htarget with h | h
    · cases h
    · exact (Option.some.inj h).symm
  have hsame : family' = family := List.eq_of_mem_of_nodup_map
    (VInductDecl.typeNames_nodup hnodup) hfamily' hfamily hname'
  have hargs' : (VExpr.getAppFnArgs.go result []).2.length = decl.nparams := by
    simpa only [hsame, hindices, hx, Nat.add_zero] using hargs
  have hresult : result = VExpr.mkApps (.const family.name (VLevel.params decl.uvars))
      (decl.paramVars (doms.length - decl.nparams)) := by
    have H := (VExpr.mkApps_getAppFnArgs_eq result).symm
    have hh : (VExpr.getAppFnArgs.go result []).1 =
        .const family.name (VLevel.params decl.uvars) := hhead
    rw [hh] at H
    have E : (VExpr.getAppFnArgs.go result []).2 = decl.paramVars (doms.length - decl.nparams) := by
      simpa only [← hargs', List.take_length] using hparams
    exact H.trans (congrArg (VExpr.mkApps _) E)
  let ds := doms.map (VExpr.instL ls)
  let ps := ds.take info.nparams
  let fs := ds.drop info.nparams
  have hds : ds.length = doms.length := List.length_map ..
  have hps : ps.length = info.nparams := by simp only [ps, List.length_take, hds]; omega
  have hfs : fs.length = doms.length - decl.nparams := by
    simp only [fs, List.length_drop, hds, hnparams]
  have hfs' : fs.length = info.numFields := by
    rw [hfs]; change doms.length - decl.nparams = info.ctorType.forallArity - info.nparams
    rw [← hctorType, harity, hnparams]
  refine ⟨ps, fs, hps, hfs', ?_⟩
  have EE : (result.instL ls) = (etaOpen ps.length (.const s ls)).liftN fs.length := by
    rw [hresult, VExpr.instL_mkApps, etaOpen_spine, VExpr.liftN_mkApps]
    simp only [VExpr.instL, VLevel.params_map_inst ls (hl.trans huvars.symm),
      VExpr.liftN, hname, VInductDecl.paramVars, vars, List.map_map,
      Function.comp_def, hps, hnparams, hfs, Nat.zero_add]
    simp only [liftVar, Nat.not_lt_zero, if_false, Nat.add_comm]
  rw [← hctorType, hshape, VExpr.instL_wrapForalls, EE]
  change VExpr.wrapForalls ds _ = _
  conv => lhs; rw [← List.take_append_drop info.nparams ds]
  exact VExpr.wrapForalls_append ..

/-- Matching literal headers are a declaration-level condition: the stored
family type ends in a sort after exactly the constructor's raw parameter prefix.
General registration supplies ordinary equality with a common telescope, not
this syntactic condition or a directed native-header conversion. Establishing
suitable alignment for arbitrary registered headers remains open. -/
def LiteralStructureFamilyHeader (s : Name) (info : VProjectionInfo) (ls : List VLevel) : Prop :=
  ∃ ps tail fi u,
    (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail) ∧
    env.constants s = some fi ∧ ls.length = fi.uvars ∧
    fi.type.instL ls = VExpr.wrapForalls ps (.sort u)

/-- A literal match at the uninstantiated declaration level supplies the header
condition at every universe instance. No context or argument values are involved. -/
theorem LiteralStructureFamilyHeader.of_declarations
    (hfamily : env.constants s = some fi) (hl : ls.length = fi.uvars)
    (hp : ps.length = info.nparams)
    (HTf : fi.type = VExpr.wrapForalls ps (.sort u))
    (HTc : info.ctorType = VExpr.wrapForalls ps tail) :
    LiteralStructureFamilyHeader s info ls := by
  refine ⟨ps.map (VExpr.instL ls), tail.instL ls, fi, u.inst ls, ?_, hfamily, hl, ?_⟩
  · rw [HTc, VExpr.instL_wrapForalls, ← hp,
      ← List.length_map (f := VExpr.instL ls) (as := ps), VExpr.takeForalls_wrapForalls]
  · rw [HTf, VExpr.instL_wrapForalls]
    rfl

/-- Registered constructors with matching literal family headers preserve
exact result ancestry after arbitrary parameter and field computations.
Registration supplies the literal result shape and ordinary constructor typing
supplies all argument-domain checks. No parameter or field needs native recovery;
the explicit header condition is independent of their values and context. -/
theorem registered_mixed_constructor_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : LiteralStructureFamilyHeader s info ls)
    (hp : args.length = info.nparams) (hf : fields.length = info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) (args ++ fields)) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (images ++ fieldImages)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out := by
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  obtain ⟨ps, fs, hps, hfs, HTc⟩ := registered_constructor_mixed_shape hi hx hl
  obtain ⟨ps', tail, fi, u, Htake, Hfamily, hlf, HTf⟩ := HH
  rw [HTc, ← hps, VExpr.takeForalls_wrapForalls] at Htake
  have Eps : ps = ps' := congrArg Prod.fst (Option.some.inj Htake)
  subst ps'
  have hc : env.HasType univs Γ (.const info.ctorName ls)
      (VExpr.wrapForalls (ps ++ fs) ((etaOpen ps.length (.const s ls)).liftN fs.length)) := by
    rw [VExpr.wrapForalls_append, ← HTc]
    exact .const (henv.ordered.projectionConstructor hi) hw hl
  have hargs := (HasType.mkApps_wrapForalls henv hΓ hc ⟨_, ht⟩
    (by simp only [List.length_append, hp, hf, hps, hfs])).1
  have HC : TelInst env univs Γ (ps ++ fs) (args ++ fields) :=
    ⟨by simp only [List.length_append, hp, hf, hps, hfs], hargs⟩
  have HA : TelInst env univs Γ ps args := by
    refine ⟨hp.trans hps.symm, ?_⟩
    intro j hj hjp
    have H := hargs j (by simp only [List.length_append]; omega)
      (by simp only [List.length_append]; omega)
    simpa only [List.getElem_append_left hj, List.getElem_append_left hjp,
      List.take_append_of_le_length (Nat.le_of_lt hj)] using H
  exact static_structure_declared_mixed_constructor_origin heq hs hΓ
    (henv.ordered.projectionConstructor hi) hw hl Hfamily hw hlf HTf HTc HA HC RX RY RN

/-- The original family spine is the exact raw ancestor of every selected
native output of a registered constructor with a matching literal header.
The constructor may itself be proof-valued; only ordinary source typing is used. -/
theorem registered_mixed_constructor_raw_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : LiteralStructureFamilyHeader s info ls)
    (hp : args.length = info.nparams) (hf : fields.length = info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) (args ++ fields)) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (images ++ fieldImages)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const s ls) (args.map (proofErase Γ))) out := by
  have R := registered_mixed_constructor_native_origin heq hs hΓ hi hx HH hp hf ht RX RY RN
  have HW := structure_constructor_native_walk hΓ hi hx
    (by simp only [List.length_append, hp, hf]) ht
  rw [← hp, List.take_append_length] at HW
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have hc := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  obtain ⟨_, hS⟩ := (native_walk_typing hc HW).isType henv hΓ
  rwa [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)] at R

/-- Every selected constructor output transfers to a pivot recovering the
original family. Parameters and fields may compute independently; no retained
parameter certificate or native certificate for an argument image is required.
The remaining explicit condition concerns the stored declaration header only. -/
theorem native_transfer_registered_mixed_constructor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : LiteralStructureFamilyHeader s info ls)
    (hp : args.length = info.nparams) (hf : fields.length = info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) (args ++ fields)) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      pivot (ProofShape.mkApps (.const s ls) (args.map (proofErase Γ)))) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (images ++ fieldImages)) pivot := by
  intro out RN
  exact RP.convert (registered_mixed_constructor_raw_origin heq hs hΓ hi hx HH hp hf ht RX RY RN)

/-- Two independently computed field vectors at fixed arbitrary parameters
transfer all selected native outputs when their registered header matches.
Both source and target guards are derived from their ordinary constructor
histories. No native parameter or major premise, proof-parameter restriction,
or separately supplied constructor telescope is needed. -/
theorem native_transfer_registered_field_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HH : LiteralStructureFamilyHeader s info ls)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) T)
    (hn : ¬ IsProof Γ (structExpand s info ls ps m))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (HB : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields') :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields))
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields')) := by
  apply native_transfer_registered_mixed_constructor heq hs hΓ hi hx HH hp
    (by simp) hc (List.Forall₂.rfl (fun _ _ => .refl)) HA
  exact computed_structure_fields_family (erased_static_structure_eta_expansion_union_descent heq hs)
    hΓ hi hp hx hc hn HB

end Lean4Lean.VEnv.Strengthening
