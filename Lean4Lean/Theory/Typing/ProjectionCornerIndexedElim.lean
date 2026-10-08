import Lean4Lean.Theory.Typing.ProjectionCornerIndexedSig

/-! # The projection-walk corner at an indexed structure, from a registered case eliminator

The index-general form of `corner_inhabit_elim`. A structure family named among the original
families of a registered case schema has the abstract eliminator `.elim key owner` at motive
universe zero (`elimDF`), whose restored case type is the recursor type of the indexed
one-constructor view `caseViewI` (`restored_structure_recursorType_idx`).
`corner_inhabit_view_idx` then inhabits the projection-walk binder.

The case certificate does not record that the declared family type agrees with the
normalized family header `wrapForalls (params ++ indices) (sort resultLevel)` before the
binders of the later indices; that agreement is needed to type the major's indices along the
view's index telescope, and it does not follow from `FamilyTypesWF` without strengthening.
`corner_inhabit_elim_indexed` therefore takes it, in restored form, as the hypothesis `hhdr`,
to be discharged by a header-agreement clause of the case certificate. -/

namespace Lean4Lean
namespace InductiveSignature

/-- The restored constructor type of a structure's normalized constructor is the constructor
type of its indexed case view at the restored parameter, field and index terms. -/
theorem restore_constructorType_idx {s : InductiveSignature} {r : Restoration}
    {c : Constructor s.families.size}
    (hf : r.heads.find? (fun h => h.auxiliary == s.families[c.owner].name) = none)
    (hn : r.recursorName s.families[c.owner].name = s.families[c.owner].name)
    {restored : VExpr} (h : r.expr (s.constructorType c) = some restored)
    (isUnsafe : Bool) (name : Name) (fam : Family) (hfam : fam.name = s.families[c.owner].name) :
    ∃ RP RF RCI, s.params.mapM r.expr = some RP ∧ (s.fieldTypes c).mapM r.expr = some RF ∧
      c.indices.mapM r.expr = some RCI ∧
      restored = (caseViewI s.uvars isUnsafe fam name RP RF RCI).constructorType
        ⟨name, ⟨0, by simp [caseViewI]⟩, RF.map Field.external, RCI⟩ := by
  simp only [constructorType, InductiveSignature.familyApp] at h
  rw [r.expr_wrapForalls, List.mapM_append, r.expr_mkApps, List.mapM_append,
    r.mapM_expr_vars] at h
  cases hRP : s.params.mapM r.expr with
  | none => simp [hRP] at h
  | some RP =>
  cases hRF : (s.fieldTypes c).mapM r.expr with
  | none => simp [hRP, hRF] at h
  | some RF =>
  cases hRCI : c.indices.mapM r.expr with
  | none => simp [hRP, hRF, hRCI] at h
  | some RCI =>
  simp [hRP, hRF, hRCI, Restoration.expr.go] at h
  simp only [Fin.getElem_fin] at hf hn
  rw [hf] at h
  simp only [hn, Option.some.injEq, exists_eq_left'] at h
  refine ⟨RP, RF, RCI, rfl, rfl, rfl, ?_⟩
  have hRPlen : RP.length = s.params.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
  have hRFlen : RF.length = c.fields.length := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF))]
    simp [fieldTypes]
  rw [← h]
  simp only [constructorType]
  rw [fieldTypes_external _ rfl]
  simp [InductiveSignature.familyApp, caseViewI, hRPlen, hRFlen, hfam]

end InductiveSignature

namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

theorem corner_inhabit_elim_indexed (henv : env.WF) (hch : env.HasCanonicalChoice)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {T₀ : VExpr} (hT₀ : VExpr.LEquiv U T₀ (info.ctorType.instL ls))
    {ps idx : List VExpr} (hpl : ps.length = info.nparams)
    {e' : VExpr} (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx)))
    {j : Nat} {D body' : VExpr}
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (ps ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : env.IsType U Δ D)
    (hguard : ∀ u, env.HasType U Δ D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    {key : Name} {schema : CaseSchema} (hel : env.eliminators key schema)
    (hS : S ∈ schema.originalFamilies)
    (hhdr : ∀ owner : Fin schema.signature.families.size,
      schema.signature.families[owner].name = S →
      ∃ RP RI, schema.signature.params.mapM schema.restoration.expr = some RP ∧
        schema.signature.families[owner].indices.mapM schema.restoration.expr = some RI ∧
        ∃ tc, env.constants S = some tc ∧ env.IsDefEqU schema.signature.uvars [] tc.type
          (VExpr.wrapForalls (RP ++ RI) (.sort schema.signature.families[owner].resultLevel))) :
    ∃ d, env.HasType U Δ d D := by
  obtain ⟨base, source, block, hle, hcert, hconsts, hproj⟩ :=
    henv.eliminatorsCoherent key schema hel
  obtain ⟨expanded, auxiliaries, hdata, hprior, hr, hnames, hdisj⟩ := hcert
  rw [hnames] at hS
  obtain ⟨type, htype, rfl⟩ := List.mem_map.mp hS
  -- the structure's source family and its projection data
  obtain ⟨type', htype', hentry⟩ := List.mem_filterMap.mp (hproj type htype info hinfo)
  obtain ⟨ctor, hctors, hn, rfl⟩ : ∃ ctor, type'.ctors = [ctor] ∧ type'.name = type.name ∧
      info = ⟨source.uvars, source.nparams, type'.numIndices, type'.resultLevel, ctor.name,
        ctor.type⟩ := by
    split at hentry
    · rename_i ctor hc
      simp only [Option.some.injEq, VProjectionEntry.mk.injEq] at hentry
      exact ⟨ctor, hc, hentry.1, hentry.2.symm⟩
    · cases hentry
  simp only at hlslen hT₀ hpl hguard
  -- the normalized family and its unique constructor
  obtain ⟨envTypes, direct, htypes, -, -, hfamilies⟩ := hdata.correspondence
  have htypesLE := VEnv.addConstVals_le_target hle htypes (by
    intro value hvalue
    apply hconsts value
    rw [hdata.types]
    exact List.mem_append_left _ hvalue)
  obtain ⟨normalized, hnmem, hrel⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hfamilies type' (List.mem_append_left _ htype')
  obtain ⟨owner, rfl⟩ := mem_declaration_types hnmem
  have hctorsRel := hrel.constructors
  rw [hctors] at hctorsRel
  obtain ⟨nc, rest, hR, hrest, hnceq⟩ := List.forall₂_cons_right_iff.mp hctorsRel
  cases List.forall₂_nil_right_iff.mp hrest
  obtain ⟨c, hcmem, hcown, hncname, hnctype, hview⟩ := CaseSchema.view_of_single hnceq
  obtain ⟨hcname, -, restored, hrestore, hdefT⟩ := hR
  have hSname : schema.signature.families[owner].name = type.name := hrel.name.trans hn
  have hIlen : schema.signature.families[owner].indices.length = type'.numIndices := by
    have := hrel.indices
    simp only [declarationFamily] at this
    exact this
  have hCIlen : c.indices.length = schema.signature.families[owner].indices.length := by
    have := hdata.model.constructorArity c hcmem
    subst hcown; exact this
  subst hcown
  -- restoration fixes the structure's names
  have hctorName : c.name = ctor.name := hncname.symm.trans hcname
  have hSmem : type.name ∈ familyNames source.types :=
    List.mem_flatMap.mpr ⟨type', htype', by rw [hn]; exact List.mem_cons_self⟩
  have hCmem : c.name ∈ familyNames source.types :=
    List.mem_flatMap.mpr ⟨type', htype', by rw [hctors, hctorName]; simp⟩
  obtain ⟨hfS, hnS⟩ := hdata.restoration_fixed hdisj hSmem
  obtain ⟨hfc, hnc⟩ := hdata.restoration_fixed hdisj hCmem
  rw [← hSname] at hfS hnS
  rw [hnctype] at hrestore
  -- the restored header
  obtain ⟨RP', RI, hRP', hRI, hhdr'⟩ := hhdr c.owner hSname
  let fam : Family := ⟨schema.signature.families[c.owner].name, RI,
    schema.signature.families[c.owner].resultLevel⟩
  obtain ⟨RP, RF, RCI, hRP, hRF, hRCI, rfl⟩ := restore_constructorType_idx hfS hnS hrestore
    schema.signature.isUnsafe ctor.name fam rfl
  -- the case view's constructor type is the registered one
  have huv : schema.signature.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  have hnp : RP.length = source.nparams := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP))]
    exact hdata.model.nparams.trans hdata.nparams
  have hRIlen : RI.length = schema.signature.families[c.owner].indices.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRI)).symm
  have hRCIlen : RCI.length = fam.indices.length := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRCI)), hCIlen]
    exact hRIlen.symm
  have hdef := let ⟨_, h⟩ := hdefT; (⟨_, h.mono htypesLE⟩ : env.IsDefEqU _ _ _ _)
  rw [← hr] at hfS hnS hfc hnc hRP hRF hRCI
  have hRPeq : RP' = RP := Option.some.inj (hRP'.symm.trans hRP)
  subst hRPeq
  have hhdr'' : ∃ tc, env.constants type.name = some tc ∧ env.IsDefEqU source.uvars [] tc.type
      (VExpr.wrapForalls (RP' ++ fam.indices) (.sort fam.resultLevel)) := by
    rw [← huv]; exact hhdr'
  obtain ⟨hTy, harity⟩ := caseViewI_recursorType_isType (U := U) henv hinfo hls hlslen
    (fam := fam) hSname huv hnp hRCIlen hdef hhdr''
  -- the generic case type
  have hheads : ∀ h ∈ schema.restoration.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams := by
    rw [hr]; exact fun h hh => (hdata.restorationScoped.2.2.1 h hh).2
  have hgen := CaseSchema.restored_structure_recursorType_idx hview hRP hRF hRI hRCI hheads
    hfS hnS hfc hnc schema.genericUvars schema.genericLevels (.param 0)
  rw [hctorName] at hgen
  have hlen : ls.length = schema.signature.uvars := hlslen.trans huv.symm
  let sv := caseViewI schema.signature.uvars schema.signature.isUnsafe fam ctor.name RP' RF RCI
  have hinst := Instance.recursorType_specialize
    (⟨schema.genericUvars, schema.genericLevels, .param 0, fun _ => default⟩ : Instance sv)
    U (.zero :: ls) ⟨0, by simp [sv, caseViewI]⟩
  simp only [Instance.specialize, CaseSchema.genericLevels_inst hlen] at hinst
  let gp : Instance sv := ⟨U, ls, .zero, fun _ => default⟩
  have hinst' : VExpr.instL (.zero :: ls)
      ((⟨schema.genericUvars, schema.genericLevels, .param 0, fun _ => default⟩ :
        Instance sv).recursorType ⟨0, by simp [sv, caseViewI]⟩) =
      gp.recursorType ⟨0, by simp [sv, caseViewI]⟩ := by
    rw [hinst]; rfl
  have hT : env.IsType U [] (gp.recursorType ⟨0, by simp [sv, caseViewI]⟩) := hTy
  rw [← hinst'] at hT
  obtain ⟨u, hTyU⟩ := hT
  have hclosed := VExpr.ClosedN.instL_rev (hTyU.closedN henv.ordered trivial)
  have hperm : schema.Permission U c.owner ls .zero :=
    ⟨hlen, hls, trivial, Or.inr (VLevel.equiv_def'.mpr rfl)⟩
  have helim : env.HasType U [] (.elim key c.owner.val (.zero :: ls))
      (gp.recursorType ⟨0, by simp [sv, caseViewI]⟩) := by
    rw [← hinst']
    have hwf : ∀ l ∈ VLevel.zero :: ls, l.WF U := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · trivial
      · exact hls l hl
    exact .elimDF hel hgen hclosed hperm hwf (forall₂_equiv_refl_idx _) hTyU
  exact corner_inhabit_view_idx henv hch hΔ hinfo hls hlslen hT₀ hpl he' hwalk hD hguard
    (fam := fam) hSname huv hnp hRCIlen (hRIlen.trans hIlen) hdef hhdr'' helim

end VEnv
end Lean4Lean
