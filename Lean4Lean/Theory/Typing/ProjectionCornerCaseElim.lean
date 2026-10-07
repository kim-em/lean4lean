import Lean4Lean.Theory.Typing.ProjectionCornerCase
import Lean4Lean.Theory.Typing.EliminatorCoherenceOfWF

/-! # The projection-walk corner from a registered case eliminator

A structure family named among the original families of a registered case schema has a closed
inhabitant of its case type into `Prop`, namely the abstract eliminator `.elim key owner`
specialized at the motive universe zero (`elimDF`). Its restored case type is the ordinary
recursor type of the one-constructor view `caseView` (`restored_structure_recursorType`), whose
constructor type is the restored normalized constructor type, definitionally equal to the
registered constructor type by the certified correspondence. `corner_inhabit_sig` then
inhabits the projection-walk binder. -/

namespace Lean4Lean
namespace InductiveSignature

theorem mem_declaration_types {s : InductiveSignature} {t : VInductiveType}
    (h : t ∈ s.declaration.types) : ∃ owner, t = s.declarationFamily owner := by
  simp only [declaration, List.mem_map] at h
  obtain ⟨⟨family, i⟩, hmem, rfl⟩ := h
  obtain ⟨-, hi, hfam⟩ := List.mem_zipIdx hmem
  simp only [Nat.zero_add, Array.length_toList] at hi
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [hfam]
  simp [declarationFamily]

theorem filterMap_ite_eq {α β : Type _} (p : α → Bool) (f : α → β) (l : List α) :
    l.filterMap (fun x => if p x then some (f x) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

namespace CaseSchema

/-- A normalized family with exactly one declared constructor has a one-constructor case
view. -/
theorem view_of_single {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {nc : VConstVal} (h : (schema.signature.declarationFamily owner).ctors = [nc]) :
    ∃ c : Constructor schema.signature.families.size, c ∈ schema.signature.constructors.toList ∧
      c.owner = owner ∧ nc.name = c.name ∧ nc.type = schema.signature.constructorType c ∧
      (schema.view owner).constructors = #[schema.caseConstructor c] := by
  have key := filterMap_ite_eq (fun ctor : Constructor schema.signature.families.size =>
    decide (ctor.owner.val = owner.val))
    (fun ctor => ({ name := ctor.name, uvars := schema.signature.uvars
                    type := schema.signature.constructorType ctor } : VConstVal))
    schema.signature.constructors.toList
  simp only [decide_eq_true_eq] at key
  simp only [declarationFamily] at h
  rw [key] at h
  obtain ⟨c, hc, rfl⟩ := List.map_eq_singleton_iff.mp h
  have hcmem : c ∈ List.filter _ _ := hc ▸ List.mem_singleton_self c
  obtain ⟨hcmem, hown⟩ := List.mem_filter.mp hcmem
  have hown : c.owner = owner := Fin.ext (by simpa using hown)
  refine ⟨c, hcmem, hown, rfl, rfl, ?_⟩
  have key' := filterMap_ite_eq (fun ctor : Constructor schema.signature.families.size =>
    ctor.owner == owner) schema.caseConstructor schema.signature.constructors.toList
  have hfilter : schema.signature.constructors.toList.filter (fun ctor => ctor.owner == owner) =
      schema.signature.constructors.toList.filter
        (fun ctor => decide (ctor.owner.val = owner.val)) := by
    congr 1; funext ctor
    exact Bool.eq_iff_iff.mpr (by simp [Fin.ext_iff])
  simp only [view]
  rw [key', hfilter, hc]
  rfl

end CaseSchema

/-- Original family and constructor names are not rewritten by their compilation's
restoration. -/
theorem CaseCompilationData.restoration_fixed {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (hdisj : RecursorNamesFresh env source expanded auxiliaries)
    (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == name) = none ∧
      (compilationRestoration source auxiliaries).recursorName name = name := by
  constructor
  · cases hf : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == name) with
    | none => rfl
    | some found =>
      have hm := List.mem_of_find?_eq_some hf
      have hn : found.auxiliary = name := by simpa using List.find?_some hf
      exact (H.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
  · unfold Restoration.recursorName
    cases hr : (compilationRestoration source auxiliaries).recursors.find?
        (fun p => p.1 == name) with
    | none => rfl
    | some pair =>
      have hm := List.mem_of_find?_eq_some hr
      have hn : pair.1 = name := by simpa using List.find?_some hr
      have hs : pair.1 ∈ source.sourceNames := by
        rw [hn]
        have := (familyNames_perm source.types).mem_iff.mp hname
        simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
          VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
          using this
      exact ((hdisj _ (List.mem_map.mpr ⟨pair, hm, rfl⟩)).2.1 hs).elim

/-- The restored constructor type of a structure's normalized constructor is the constructor
type of its case view at the restored parameter and field domains. -/
theorem restore_constructorType {s : InductiveSignature} {r : Restoration}
    {c : Constructor s.families.size} (hCI : c.indices = [])
    (hf : r.heads.find? (fun h => h.auxiliary == s.families[c.owner].name) = none)
    (hn : r.recursorName s.families[c.owner].name = s.families[c.owner].name)
    {restored : VExpr} (h : r.expr (s.constructorType c) = some restored)
    (isUnsafe : Bool) (name : Name) :
    ∃ RP RF, s.params.mapM r.expr = some RP ∧ (s.fieldTypes c).mapM r.expr = some RF ∧
      restored = (caseView s.uvars isUnsafe s.families[c.owner] name RP RF).constructorType
        ⟨name, ⟨0, by simp [caseView]⟩, RF.map Field.external, []⟩ := by
  have hbv : ∀ (n k : Nat), ∀ e ∈ vars n k, ∃ i, e = VExpr.bvar i := by
    intro n k e he; simp only [vars, List.mem_map] at he; obtain ⟨_, _, rfl⟩ := he; exact ⟨_, rfl⟩
  simp only [constructorType, InductiveSignature.familyApp, hCI, List.append_nil] at h
  rw [r.expr_wrapForalls, List.mapM_append, Restoration.expr_mkApps_const_fixed r hf hn
    (hbv _ _)] at h
  cases hRP : s.params.mapM r.expr with
  | none => simp [hRP] at h
  | some RP =>
  cases hRF : (s.fieldTypes c).mapM r.expr with
  | none => simp [hRP, hRF] at h
  | some RF =>
  simp only [hRP, hRF, Option.bind_some, Option.pure_def, bind, Option.bind_eq_bind,
    Option.map_some, Option.some.injEq] at h
  refine ⟨RP, RF, rfl, rfl, ?_⟩
  have hRPlen : RP.length = s.params.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP)).symm
  have hRFlen : RF.length = c.fields.length := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRF))]
    simp [fieldTypes]
  rw [← h]
  simp only [constructorType]
  rw [fieldTypes_external _ rfl]
  simp [InductiveSignature.familyApp, caseView, hRPlen, hRFlen]

end InductiveSignature

namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

theorem corner_inhabit_elim (henv : env.WF) (hch : env.HasCanonicalChoice)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {T₀ : VExpr} (hT₀ : VExpr.LEquiv U T₀ (info.ctorType.instL ls))
    {ps idx : List VExpr} (hpl : ps.length = info.nparams) (hni : info.nindices = 0)
    {e' : VExpr} (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx)))
    {j : Nat} {D body' : VExpr}
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (ps ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : env.IsType U Δ D)
    (hguard : ∀ u, env.HasType U Δ D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    {key : Name} {schema : CaseSchema} (hel : env.eliminators key schema)
    (hS : S ∈ schema.originalFamilies) :
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
  simp only at hlslen hT₀ hpl hni hguard
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
  have hI : schema.signature.families[owner].indices = [] := by
    have := hrel.indices
    simp only [declarationFamily] at this
    exact List.eq_nil_of_length_eq_zero (this.trans hni)
  have hCI : c.indices = [] := by
    have := hdata.model.constructorArity c hcmem
    have h2 : schema.signature.families[c.owner].indices = [] := by subst hcown; exact hI
    rw [h2] at this
    exact List.eq_nil_of_length_eq_zero this
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
  obtain ⟨RP, RF, hRP, hRF, rfl⟩ := restore_constructorType hCI hfS hnS hrestore
    schema.signature.isUnsafe ctor.name
  -- the case view's constructor type is the registered one
  have huv : schema.signature.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  have hnp : RP.length = source.nparams := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hRP))]
    exact hdata.model.nparams.trans hdata.nparams
  have hdef := let ⟨_, h⟩ := hdefT; (⟨_, h.mono htypesLE⟩ : env.IsDefEqU _ _ _ _)
  obtain ⟨hTy, harity⟩ := caseView_recursorType_isType (U := U) henv hinfo hls hlslen hni hSname
    hI huv hnp hdef
  -- the generic case type
  rw [← hr] at hfS hnS hfc hnc hRP hRF
  have hheads : ∀ h ∈ schema.restoration.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams := by
    rw [hr]; exact fun h hh => (hdata.restorationScoped.2.2.1 h hh).2
  have hgen := CaseSchema.restored_structure_recursorType hview hI hCI hRP hRF hheads hfS hnS
    hfc hnc schema.genericUvars schema.genericLevels (.param 0)
  rw [hctorName] at hgen
  have hlen : ls.length = schema.signature.uvars := hlslen.trans huv.symm
  have hinst := Instance.recursorType_specialize
    (⟨schema.genericUvars, schema.genericLevels, .param 0, fun _ => default⟩ :
      Instance (caseView schema.signature.uvars schema.signature.isUnsafe
        schema.signature.families[c.owner] ctor.name RP RF)) U (.zero :: ls)
    ⟨0, by simp [caseView]⟩
  simp only [Instance.specialize, CaseSchema.genericLevels_inst hlen] at hinst
  let sv := caseView schema.signature.uvars schema.signature.isUnsafe
    schema.signature.families[c.owner] ctor.name RP RF
  let gp : Instance sv := ⟨U, ls, .zero, fun _ => default⟩
  have hinst' : VExpr.instL (.zero :: ls)
      ((⟨schema.genericUvars, schema.genericLevels, .param 0, fun _ => default⟩ :
        Instance sv).recursorType ⟨0, by simp [sv, caseView]⟩) =
      gp.recursorType ⟨0, by simp [sv, caseView]⟩ := by
    rw [hinst]; rfl
  have hT : env.IsType U [] (gp.recursorType ⟨0, by simp [sv, caseView]⟩) := hTy
  rw [← hinst'] at hT
  obtain ⟨u, hTyU⟩ := hT
  have hclosed := VExpr.ClosedN.instL_rev (hTyU.closedN henv.ordered trivial)
  have hperm : schema.Permission U c.owner ls .zero :=
    ⟨hlen, hls, trivial, Or.inr (VLevel.equiv_def'.mpr rfl)⟩
  have hrefl : ∀ l : List VLevel, List.Forall₂ (· ≈ ·) l l := by
    intro l; induction l with
    | nil => exact .nil
    | cons a l ih => exact .cons (VLevel.equiv_def'.mpr rfl) ih
  have helim : env.HasType U [] (.elim key c.owner.val (.zero :: ls))
      (gp.recursorType ⟨0, by simp [sv, caseView]⟩) := by
    rw [← hinst']
    have hwf : ∀ l ∈ VLevel.zero :: ls, l.WF U := by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · trivial
      · exact hls l hl
    exact .elimDF hel hgen hclosed hperm hwf (hrefl _) hTyU
  have hdef' : env.IsDefEqU sv.uvars [] (sv.constructorType sv.constructors[(⟨0, by
      simp [sv, caseView]⟩ : Fin sv.constructors.size)]) ctor.type := by
    change env.IsDefEqU schema.signature.uvars [] _ _
    rw [huv]; exact hdef
  exact corner_inhabit_sig henv hch hΔ hinfo hls hlslen hT₀ hpl hni he' hwalk hD hguard
    gp ⟨0, by simp [sv, caseView]⟩ ⟨0, by simp [sv, caseView]⟩ rfl rfl hSname hI rfl rfl hnp
    (by rw [← harity]; exact congrArg (source.nparams + ·) (List.length_map _)) rfl hls (hrefl _) helim hdef'

end VEnv
end Lean4Lean
