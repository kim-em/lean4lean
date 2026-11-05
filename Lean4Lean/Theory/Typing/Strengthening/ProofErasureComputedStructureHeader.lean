import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRegisteredMixedHeader

/-! # Registered native histories from computed family headers

A closed computation from the stored family header to the constructor's raw
parameter prefix supplies the family guard used by the mixed observation.
This permits nonliteral family headers without changing constructor ancestry.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private closed_compute_weak
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeReification
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params] {D : PureObservation.Definitions}

/-- The stored family header computes, in the empty context, to a sort-ending
header on the constructor's raw parameter domains. Both the computation and
its ordinary target typing are explicit. General registration supplies ordinary
header equality only; deriving this directed certificate in that generality
remains open. The constructor's own stored type is not replaced or reversed. -/
def ComputedStructureFamilyHeader (D : PureObservation.Definitions)
    (s : Name) (info : VProjectionInfo) (ls : List VLevel) : Prop :=
  ∃ ps tail fi u,
    (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail) ∧
    env.constants s = some fi ∧ ls.length = fi.uvars ∧
    env.IsType univs [] (VExpr.wrapForalls ps (.sort u)) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
      (proofErase [] (fi.type.instL ls)) (proofErase [] (VExpr.wrapForalls ps (.sort u)))

/-- Literal header agreement is a special case of a computed closed header.
The endpoint's ordinary typing follows from the actual family declaration. -/
theorem LiteralStructureFamilyHeader.computed
    (H : LiteralStructureFamilyHeader s info ls) (hw : ∀ l ∈ ls, l.WF univs) :
    ComputedStructureFamilyHeader D s info ls := by
  obtain ⟨ps, tail, fi, u, Htake, hc, hl, HT⟩ := H
  have hf : env.HasType univs [] (.const s ls) (VExpr.wrapForalls ps (.sort u)) :=
    HT ▸ HasType.const hc hw hl
  exact ⟨ps, tail, fi, u, Htake, hc, hl, hf.isType henv (by trivial), HT ▸ ScopedCompute.refl⟩

/-- A closed computed header supplies both ordinary family typing and exact
native recovery in every well-formed context. The closed path is weakened as a
whole; no native guard is substituted through an actual argument value. -/
theorem ComputedStructureFamilyHeader.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : ∀ l ∈ ls, l.WF univs)
    (H : ComputedStructureFamilyHeader D s info ls) :
    ∃ ps tail u,
      (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail) ∧
      env.HasType univs Γ (.const s ls) (VExpr.wrapForalls ps (.sort u)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.const s ls)) (proofErase Γ (VExpr.wrapForalls ps (.sort u))) := by
  obtain ⟨ps, tail, fi, u, Htake, hc, hl, hT, RH⟩ := H
  have hf : env.HasType univs [] (.const s ls) (fi.type.instL ls) := .const hc hw hl
  obtain ⟨v, hOld⟩ := hf.isType henv (by trivial)
  obtain ⟨T', HT', ET'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) (by trivial) hOld rfl rfl RH
  obtain ⟨_, HN⟩ := (proofErase_reflect (by trivial) HT'.hasType.2 hT.choose_spec ET').2
    (not_isProof_of_sort (by trivial) HT'.hasType.2)
  have HE := HT'.toU.trans henv (by trivial) (HN.defeq (by trivial))
  have hf' := hf.defeqU_r henv (by trivial) HE
  have hfΓ := hf'.weak0 henv.ordered (Γ := Γ)
  have RΓ := closed_compute_weak heq hs hΓ hOld hT.choose_spec RH
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL) hOld hΓ
  refine ⟨ps, tail, u, Htake, hfΓ, ?_⟩
  rw [show proofErase Γ (.const s ls) = .const s ls from
    if_neg (not_isProof_telescope_to_sort hΓ hfΓ)]
  exact (ScopedTypeRecovery.const hc hw hl).convert (EC ▸ RΓ)

/-- Beta simplification of the stored family header supplies the closed
certificate. The constructor prefix stays fixed, and the chosen sort-ending
endpoint is ordinarily well formed. No general header-joining premise occurs. -/
theorem ComputedStructureFamilyHeader.of_beta
    (Htake : (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail))
    (hc : env.constants s = some fi) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = fi.uvars)
    (RB : VExpr.BetaRed (fi.type.instL ls) (VExpr.wrapForalls ps (.sort u))) :
    ComputedStructureFamilyHeader D s info ls := by
  have hf : env.HasType univs [] (.const s ls) (fi.type.instL ls) := .const hc hw hl
  obtain ⟨v, hOld⟩ := hf.isType henv (by trivial)
  exact ⟨ps, tail, fi, u, Htake, hc, hl,
    ⟨v, (beta_eq (by trivial) hOld RB).hasType.2⟩,
    .beta (proofErase_beta_forward (by trivial) hOld RB)⟩

/-- A stored family header may wrap the entire parameter telescope in a
constant beta redex. The computed-header certificate follows by contracting
that redex, so literal equality with the constructor prefix is unnecessary. -/
theorem ComputedStructureFamilyHeader.of_constant_wrapper
    (Htake : (info.ctorType.instL ls).takeForalls info.nparams = some (ps, tail))
    (hc : env.constants s = some fi) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = fi.uvars)
    (HT : fi.type.instL ls = .app (.lam (.sort (.succ .zero))
      (VExpr.wrapForalls ps (.sort u)).lift) (.sort .zero)) :
    ComputedStructureFamilyHeader D s info ls := by
  apply ComputedStructureFamilyHeader.of_beta Htake hc hw hl
  rw [HT]
  simpa only [VExpr.lift, VExpr.inst_liftN] using
    (VExpr.BetaRed.beta (A := .sort (.succ .zero))
      (b := (VExpr.wrapForalls ps (.sort u)).lift) (a := .sort .zero))
/-- Constant-wrapped stored family headers are genuinely outside the literal
header condition: their outer application is neither a Pi nor a sort. Combined
with `of_constant_wrapper`, this permits a nonliteral case of the computed
condition. This is not a strict-smallness claim about strengthening obligations. -/
theorem constant_wrapped_family_header_not_literal
    (hc : env.constants s = some fi)
    (HT : fi.type.instL ls = .app (.lam A B) x) :
    ¬ LiteralStructureFamilyHeader s info ls := by
  rintro ⟨ps, tail, fi', u, _, hc', _, HE⟩
  rw [hc] at hc'
  cases Option.some.inj hc'
  rw [HT] at HE
  cases ps <;> cases HE

/-- A closed computation of the family header suffices for exact ancestry
of every selected registered-constructor output. The parameter and field
histories may be arbitrary; the stored family header need not be literal.
The constructor retains its original raw declaration throughout the proof. -/
theorem registered_computed_header_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : ComputedStructureFamilyHeader D s info ls)
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
  obtain ⟨ps', tail, u, Htake, hft, RF⟩ := HH.realize heq hs hΓ hw
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
  have H := NativeFamilyPiHistory.initial heq hs hΓ hft RF
  have hg : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u) := by
    simpa only [VExpr.instOuter_sort] using HasType.mkApps_of_tel hft HA
  have hctor : env.HasType univs Γ (.const info.ctorName ls)
      (VExpr.wrapForalls ps (VExpr.wrapForalls fs
        ((etaOpen ps.length (.const s ls)).liftN fs.length))) := by
    simpa only [VExpr.wrapForalls_append] using hc
  have hct : env.HasType univs [] (.const info.ctorName ls) (info.ctorType.instL ls) :=
    .const (henv.ordered.projectionConstructor hi) hw hl
  obtain ⟨_, hcT⟩ := hct.isType henv (by trivial)
  have Ect := proofErase_closed_context
    ((henv.ordered.closedC (henv.ordered.projectionConstructor hi)).instL) hcT hΓ
  apply H.mixed_native_spine_origin heq hs hΓ hctor HA.1.symm (hfs.trans hf.symm) ht hg ?_ RX RY RN
  intro U RU
  have RC := RU.const_compute (henv.ordered.projectionConstructor hi)
  rwa [← Ect, HTc] at RC

/-- The original raw family spine reaches every selected native output under
the closed computed-header condition. Ordinarily proof-valued constructors
are included; no native recovery premise is imposed on any argument. -/
theorem registered_computed_header_raw_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : ComputedStructureFamilyHeader D s info ls)
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
  have R := registered_computed_header_native_origin heq hs hΓ hi hx HH hp hf ht RX RY RN
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
The closed computed-header condition concerns the family declaration only. -/
theorem native_transfer_computed_header_constructor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (HH : ComputedStructureFamilyHeader D s info ls)
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
  exact RP.convert (registered_computed_header_raw_origin heq hs hΓ hi hx HH hp hf ht RX RY RN)

/-- Two independently computed field vectors at fixed arbitrary parameters
transfer all selected native outputs under a closed computed family header.
Both source and target guards are derived from their ordinary constructor
histories. No native parameter or major premise, proof-parameter restriction,
or separately supplied constructor telescope is needed. -/
theorem native_transfer_computed_header_fields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D s info ls)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) T)
    (hn : ¬ IsProof Γ (structExpand s info ls ps m))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (HB : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields') :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields))
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields')) := by
  apply native_transfer_computed_header_constructor heq hs hΓ hi hx HH hp
    (by simp) hc (List.Forall₂.rfl (fun _ _ => .refl)) HA
  exact computed_structure_fields_family (erased_static_structure_eta_expansion_union_descent heq hs)
    hΓ hi hp hx hc hn HB

end Lean4Lean.VEnv.Strengthening
