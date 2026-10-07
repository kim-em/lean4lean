import Lean4Lean.Theory.Typing.ShapeModel.RuleValidNative

/-!
# Semantic facts about the majors of generic eliminator equations

* `famSem_absurd`: a constant whose type is a telescope ending in a rigid family application has
  no semantic family header.
* `ctor_facts_of_family`: a constructor of the signature whose type ends in a recorded family
  with a semantic header has its signature data and the structure facts of its structures.
* `source_family_recorded`: at an eliminator registration, every source family of the schema is
  recorded in the tables (the other cases contradict semantic family headers).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

/-- A constant whose type ends in an application of a rigid constant has no semantic family
header. -/
theorem famSem_absurd (H : env.WF) {I F : Name} {cv : VConstant}
    (hsem : letI := envSig env; FamSem env I l n) (hcv : env.constants I = some cv)
    {doms args : List VExpr} {ls' : List VLevel}
    (hty : cv.type = VExpr.wrapForalls doms (VExpr.mkApps (.const F ls') args))
    (hrig : env.Rigid F) : False := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  have hnr : ∀ r, SemSig.rules r → r.head ≠ .const F := fun r hr =>
    EnvRule.head_not_rigid H hrig hr
  obtain ⟨ci, Ds, hci, -, hiff⟩ := hsem
  cases hci.symm.trans hcv
  let ls := VLevel.params cv.uvars
  have hb := Interp.nestPi_bots_sort (env := env) (ρ := .nil) (Ds.map (·.instL ls)) (l.inst ls)
  have hb' : Interp env .nil (nestPi ((Ds.map (·.instL ls)).map fun _ => (TShape.bot, TShape.bot))
      (TShape.sort (l.inst ls).eval)) (VExpr.instL ls (Ds.foldr .forallE (.sort l))) := by
    rw [VExpr.instL_foldr_forallE]; exact hb
  have := (hiff ls (by simp [ls]) _).2 hb'
  rw [hty] at this
  change Interp env .nil _ (VExpr.instL ls (doms.foldr .forallE _)) at this
  rw [VExpr.instL_foldr_forallE, VExpr.instL_mkApps] at this
  exact Interp.nestPi_fam_absurd hnr this

/-- The signature data of a constructor whose type ends in a recorded family. -/
theorem ctor_facts_of_family (H : env.WF) {c F : Name} {cv : VConstant} {d : FamData}
    (hcv : env.constants c = some cv) (hfF : familyOfType cv.type = some F) (hIs : IsCtor env c)
    (hF : famOf env F = some d)
    (hsemF : letI := envSig env; FamSem env F d.resultLevel (d.nparams + d.nindices)) :
    letI := envSig env
    ∃ ci, sigCtor env c = some ci ∧ ci.family = F ∧
      ∀ {s info}, env.projections s info → info.ctorName = c → FamTypeSem env s info := by
  letI := envSig env
  refine ⟨⟨F, structNp env c, cv.type.forallArity - structNp env c⟩, ?_, rfl, ?_⟩
  · unfold sigCtor
    rw [if_pos hIs, hcv]
    simp [hfF]
  · intro s info hp hcn
    have h1 := ctorOf_projection H hp
    rw [hcn] at h1
    obtain ⟨ci, doms, idx, hci, -, ht, -⟩ := ctorOf_shape' H h1
    rw [hcv] at hci; cases hci
    rw [ht, familyOfType_shape, Option.some.injEq] at hfF
    subst hfF
    have h2 := famOf_projection H hp
    rw [hF] at h2
    cases h2
    exact famTypeSem_of_famSem H hp hsemF

/-- A source constructor of a certified schema has a constructor shape in its own view. -/
theorem source_ctor_shape {E base : VEnv} {source : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} (hcert : schema.Certified base source block)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      E.constants value.name = some value.toVConstant)
    {F : VInductiveType} (hF : F ∈ source.types) {c : VConstVal} (hc : c ∈ F.ctors) :
    E.constants c.name = some c.toVConstant ∧ CtorShape E c.name (ctorView source F c) := by
  obtain ⟨expanded, g, aux, hdata, _, _, _⟩ := hcert
  have hconst : E.constants c.name = some c.toVConstant :=
    hconsts c (List.mem_append_right _ (by
      rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc⟩))
  obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
  exact ⟨hconst, ctorShape_of_raw (hraw F hF c hc)
    (hdata.sourceWF.2.2.2.1 c (List.mem_flatMap.mpr ⟨F, hF, hc⟩)) hconst⟩

/-- The family of a constructor shape is the family of its type. -/
theorem CtorShape.familyOfType {E : VEnv} {c : Name} {k : CtorData} (h : CtorShape E c k)
    {cv : VConstant} (hcv : E.constants c = some cv) : familyOfType cv.type = some k.family := by
  obtain ⟨ci, doms, idx, hci, -, ht, -⟩ := h
  rw [hcv] at hci; cases hci
  rw [ht, familyOfType_shape]

/-- At an eliminator registration, every source family is recorded. -/
theorem source_family_recorded (H : env.WF) {E base : VEnv} {T : Tables}
    {source : VInductDecl} {block : VInductBlock} {schema : CaseSchema} {key : Name}
    (hgood : Good env E) (hEW : E.WF) (hle : E.addEliminator key schema ≤ env)
    (hbl : base ≤ E) (hcert : schema.Certified base source block)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      E.constants value.name = some value.toVConstant)
    (hT : T.Inv E) (hext : (T.addSchema E source).Extends (envTables env))
    (hfam : ∀ I d, (T.addSchema E source).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    {F : VInductiveType} (hF : F ∈ source.types) :
    ∃ d, (T.addSchema E source).fam F.name = some d := by
  letI := envSig env
  have hleE : E ≤ env := VEnv.addEliminator_le.trans hle
  have hcert' := hcert
  obtain ⟨expanded, g, aux, hdata, hprior, hr, hnames⟩ := hcert'
  obtain ⟨params, _, _, hTypeShape, _, _⟩ := hdata.sourceParameters
  have hFconst : env.constants F.name = some F.toVConstant :=
    hleE.constants (hconsts F.toVConstVal (List.mem_append_left _ (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨F, hF, rfl⟩)))
  have hsemF := famSem_of_typeShape H hgood hleE hEW.ordered ((hTypeShape F hF).mono hbl)
    (hdata.sourceWF.2.2.1 F hF) hFconst
  have hrigF : env.Rigid F.name := VEnv.nativeHeadRigid_iff.mp
    (VEnv.WF.case_original_family_rigid H (hle.eliminators VEnv.addEliminator_self)
      (by rw [hnames]; exact List.mem_map.mpr ⟨F, hF, rfl⟩))
  cases hTF : (T.addSchema E source).fam F.name with
  | some d => exact ⟨d, rfl⟩
  | none =>
  exfalso
  have hTF' : addView T.fam (viewFams source (selFreeIn E T)) F.name = none := hTF
  rw [addView_none] at hTF'
  obtain ⟨hT0, hV0⟩ := hTF'
  have hnsel : selFreeIn E T F ≠ true := fun hs => by
    rw [viewFams_mem hdata.sourceWF.2.1 hF hs] at hV0; cases hV0
  by_cases hres : SchemaCtorReserved E F.name
  · -- the family is a constructor of an earlier schema
    obtain ⟨key', schema', hreg', hmem'⟩ := hres
    obtain ⟨b', src', blk', _, hb'le, hcert'', _, hconsts'⟩ := hEW.eliminator_origin hreg'
    obtain ⟨c', hc', hcn⟩ := (Certified.mem_schemaCtorNames hcert'').mp hmem'
    obtain ⟨F', hF', hc'F'⟩ := List.mem_flatMap.mp hc'
    obtain ⟨hc'const, hshape⟩ := source_ctor_shape hcert'' hconsts' hF' hc'F'
    obtain ⟨_, _, _, hdata', _, _, hnames'⟩ := hcert''
    have hrig' : env.Rigid F'.name := VEnv.nativeHeadRigid_iff.mp
      (VEnv.WF.case_original_family_rigid H (hleE.eliminators hreg')
        (by rw [hnames']; exact List.mem_map.mpr ⟨F', hF', rfl⟩))
    obtain ⟨ci, doms, idx, hci, -, ht, -⟩ := hshape.mono hleE
    rw [hcn, hFconst] at hci
    cases hci
    exact famSem_absurd H hsemF hFconst ht hrig'
  · have hns : ¬(T.fam F.name = none ∧ T.ctor F.name = none ∧
        ∀ c ∈ F.ctors, T.fam c.name = none ∧ T.ctor c.name = none) := fun h => hnsel (by
      simp only [selFreeIn, selFree, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h, hres⟩)
    by_cases hctF : T.ctor F.name = none
    · by_cases hall : ∀ c ∈ F.ctors, T.fam c.name = none ∧ T.ctor c.name = none
      · exact hns ⟨hT0, hctF, hall⟩
      · obtain ⟨c, hc, hcc⟩ : ∃ c ∈ F.ctors, ¬(T.fam c.name = none ∧ T.ctor c.name = none) :=
          Classical.byContradiction fun hne =>
            hall fun c hc => Classical.byContradiction fun h => hne ⟨c, hc, h⟩
        obtain ⟨hcconst, hshape⟩ := source_ctor_shape hcert hconsts hF hc
        by_cases hfc : T.fam c.name = none
        · have hctc : T.ctor c.name ≠ none := fun h => hcc ⟨hfc, h⟩
          obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hctc
          obtain ⟨hks, d, hd, -⟩ := hT.views.ctor hk
          have h1 := hks.familyOfType hcconst
          have h2 := hshape.familyOfType hcconst
          have hkf : k.family = F.name := Option.some.inj (h1.symm.trans h2)
          rw [hkf, hT0] at hd; cases hd
        · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hfc
          have hsemc := hfam _ _ (addView_of_old (new := viewFams source (selFreeIn E T)) hd)
          obtain ⟨ci, doms, idx, hci, -, ht, -⟩ := hshape.mono hleE
          rw [hleE.constants hcconst] at hci
          cases hci
          exact famSem_absurd H hsemc (hleE.constants hcconst) ht hrigF
    · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hctF
      have hk' : ctorOf env F.name = some k := hext.ctor (addView_of_old hk)
      have hsig := sigCtor_of_shape (c := F.name) (.inl (by rw [hk']; simp)) (ctorOf_shape' H hk')
      exact fam_not_ctor H hsemF hsig

end

end Lean4Lean.ShapeModel
