import Lean4Lean.Theory.Typing.Countermodel.Typing

/-!
# Well-formedness of the countermodel environment

`envCM_wf : VEnv.WF envCM` is proved by the declaration trace

```text
axiom C, axiom F, axiom c, axiom P, axiom leftMap, axiom rightMap, induct I, induct J
```

Each inductive step is the generic `FamSpec.induct_wf`, which builds the
complete ordinary-compilation certificate (`SourceWF`, `FormationWF`,
`OrdinaryShape`, `Compiles`, `CompiledInductive`, `VInductBlock.WF`) for one
singleton family. The lookups it needs in the intermediate environments are
hypotheses, discharged by computation for the two concrete families.
-/

namespace Lean4Lean.Countermodel

open VEnv InductiveSignature

namespace FamSpec

/-- Lookups and name facts used by the installation certificate. -/
structure InductHyps (sp : FamSpec) (Eb ET EC ER EA : VEnv) : Prop where
  hT : Eb.addConstVals sp.decl.typeConstants = some ET
  hC : ET.addConstVals sp.decl.constructorConstants = some EC
  hR : ((EC.addEliminators sp.block.eliminators).addProjections sp.decl.projectionEntries).addConstVals
    sp.block.recursors = some ER
  hA : VInductBlock.install Eb sp.block = some EA
  bB : Base Eb
  bT : Base ET
  mT : sp.MapOK ET
  fT : sp.FamOK ET
  bC : Base (EC.addProjections sp.decl.projectionEntries)
  mC : sp.MapOK (EC.addProjections sp.decl.projectionEntries)
  fC : sp.FamOK (EC.addProjections sp.decl.projectionEntries)
  cC : sp.CtorOK (EC.addProjections sp.decl.projectionEntries)
  bR : Base ER
  mR : sp.MapOK ER
  fR : sp.FamOK ER
  cR : sp.CtorOK ER
  rR : sp.RecOK ER
  fam_ne_ctor : sp.fam ≠ sp.ctor
  fam_ne_rec : sp.fam ≠ sp.recName
  ctor_ne_rec : sp.ctor ≠ sp.recName
  F_ne : nF ≠ sp.fam
  c_ne : nc ≠ sp.fam
  P_ne : nP ≠ sp.fam
  map_ne : sp.map ≠ sp.fam

variable {sp : FamSpec} {Eb ET EC ER EA : VEnv} (H : InductHyps sp Eb ET EC ER EA)
include H

theorem scf_Fc : eFc.SourceConstFree (sp.decl.types.map (·.name)) :=
  .app (.const _ _ (by simpa [decl, indType] using H.F_ne))
    (.const _ _ (by simpa [decl, indType] using H.c_ne))

theorem scf_Pv : (VExpr.app eP (.bvar 0)).SourceConstFree (sp.decl.types.map (·.name)) :=
  .app (.const _ _ (by simpa [decl, indType] using H.P_ne)) (.bvar 0)

theorem sourceNames_nodup : sp.decl.sourceNames.Nodup := by
  simp [VInductDecl.sourceNames, VInductDecl.typeConstants, VInductDecl.constructorConstants,
    decl, indType, ctorVal, H.fam_ne_ctor]

theorem typeFam_wf_b : ∃ u, Eb.HasType 0 [] typeFam (.sort u) := ⟨_, typeFam_wf H.bB⟩

theorem sourceWF : VInductDecl.SourceWF Eb sp.decl := by
  refine ⟨by simp [decl], sourceNames_nodup H, by simp [decl, indType],
    by simp [VInductDecl.constructorConstants, decl, indType, ctorVal], ET, EC, H.hT, H.hC,
    ?_, ?_⟩
  · intro type htype
    simp [decl] at htype
    subst htype
    exact typeFam_wf_b H
  · intro ctor hctor
    simp [VInductDecl.constructorConstants, decl, indType] at hctor
    subst hctor
    exact ctorType_wf H.bT H.mT H.fT

theorem typeShape : sp.decl.TypeShape Eb [] sp.indType := by
  obtain ⟨u, h⟩ := typeFam_wf_b H
  exact ⟨typeFam, [], typeFam, [eC, .app eF (.bvar 0), .app eF (.bvar 1)], .sort .zero, _,
    h, rfl, rfl, .zero, tySort0 H.bB⟩

theorem ctorResult_valid :
    sp.decl.ValidIndAppAt (some sp.fam) 2 sp.ctorResult := by
  refine ⟨sp.indType, by simp [decl], .inr rfl, [], rfl, rfl, rfl, rfl, ?_⟩
  intro arg harg
  simp only [ctorResult, VExpr.getAppFnArgs_app, VExpr.getAppFnArgs_const, decl,
    List.drop_zero, List.nil_append, List.cons_append, List.mem_cons,
    List.mem_singleton] at harg
  have hmap : sp.map ∉ sp.decl.types.map (·.name) := by
    simpa [decl, indType] using H.map_ne
  have hc : nc ∉ sp.decl.types.map (·.name) := by simpa [decl, indType] using H.c_ne
  rcases harg with rfl | rfl | rfl | h
  · exact .const _ _ hc
  · exact .bvar _
  · exact .app (.const _ _ hmap) (.bvar _)
  · simp at h

theorem ctorTail : sp.decl.CtorTailWF ET sp.indType [] 0 sp.ctorType := by
  have hFc : ET.HasType 0 [] eFc (.sort lvl1) := tyFc H.bT
  have hPv : ET.HasType 0 [eFc] (.app eP (.bvar 0)) (.sort .zero) :=
    tyPapp H.bT (HasType.bvar .zero)
  have hv : ET.HasType 0 [.app eP (.bvar 0), eFc] (.bvar 1) eFc := HasType.bvar (.succ .zero)
  have hres : ET.HasType 0 [.app eP (.bvar 0), eFc] sp.ctorResult (.sort .zero) :=
    tyFamApp H.fT (tyc H.bT) hv (tyMapApp H.mT hv)
  have hbody : ET.HasType 0 [eFc] (.forallE (.app eP (.bvar 0)) sp.ctorResult)
      (.sort (.imax .zero .zero)) := .forallE hPv hres
  refine .field hFc (.inl rfl) (.inr (.unfold hFc (.nonrecursive (scf_Fc H)))) hFc hbody ?_
  refine .field hPv (.inl rfl) (.inr (.unfold hPv (.nonrecursive (scf_Pv H)))) hPv hres ?_
  exact .result (ctorResult_valid H) hres

theorem ctorShape : sp.decl.CtorShape ET [] sp.indType sp.ctorVal := by
  obtain ⟨u, h⟩ := ctorType_wf (U := 0) H.bT H.mT H.fT
  exact ⟨sp.ctorType, [], sp.ctorType, _, [], h, rfl, .zero, .zero, ctorTail H⟩

theorem rawCtorShape : sp.decl.RawCtorShape sp.indType sp.ctorVal :=
  ⟨[eFc, .app eP (.bvar 0)], sp.ctorResult, rfl, by simp [decl],
    (ctorResult_valid H).raw, rfl⟩

theorem formationWF : VInductDecl.FormationWF Eb sp.decl := by
  refine ⟨[], .zero, ET, H.hT, ?_, ?_, ?_⟩
  · intro type htype
    simp [decl] at htype
    subst htype
    exact ⟨rfl, typeShape H⟩
  · intro type htype ctor hctor
    simp [decl] at htype
    subst htype
    simp [indType] at hctor
    subst hctor
    exact ⟨⟨[], sp.ctorType, rfl, .zero⟩, ctorShape H⟩
  · intro type htype ctor hctor
    simp [decl] at htype
    subst htype
    simp [indType] at hctor
    subst hctor
    exact rawCtorShape H

omit H in
def recursorShape : sp.decl.RecursorShape sp.indType sp.recVal where
  ownerIdx := 0
  owner_lt := by simp [decl]
  owner_eq := rfl
  name := rfl
  uvars := .inr rfl
  params := []
  motives := [sp.motiveType]
  minors := [sp.minorType]
  indices := [eC, .app eF (.bvar 0), .app eF (.bvar 1)]
  major := [sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)]
  afterParams := sp.recType
  afterMotives := .forallE sp.minorType (.forallE eC (.forallE (.app eF (.bvar 0))
    (.forallE (.app eF (.bvar 1)) (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0))
      (app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))))))
  afterMinors := .forallE eC (.forallE (.app eF (.bvar 0))
    (.forallE (.app eF (.bvar 1)) (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0))
      (app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))))
  afterIndices := .forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0))
      (app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
  result := app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
  params_take := rfl
  motives_take := rfl
  minors_take := rfl
  indices_take := rfl
  major_take := rfl
  result_eq := rfl

omit H in
theorem rhs_guarded :
    ruleRhsBody.GuardedIota (sp.block.recursors.map (·.name)) [] 0 :=
  .app (.app .bvar .bvar) .bvar

omit H in
def iotaRule (E : VEnv) : sp.decl.IotaRule E sp.block sp.indType sp.ctorVal sp.rule where
  recursor := sp.recVal
  recursor_mem := by simp [block, recursors_eq]
  recursor_name := rfl
  rule_uvars := rfl
  domains := sp.ruleDomains
  lhsBody := sp.ruleLhsBody
  rhsBody := ruleRhsBody
  typeBody := sp.ruleTypeBody
  lhs_wrapped := rfl
  rhs_wrapped := rfl
  type_wrapped := rfl
  recursorLevels := [.param 0]
  leadingArgs := [.bvar 3, .bvar 2, ec, .bvar 1, .app sp.eMap (.bvar 1)]
  ctorLevels := []
  ctorArgs := [.bvar 1, .bvar 0]
  lhs_pattern := rfl
  recursor_levels := rfl
  ctor_levels := rfl
  leading_arity := rfl
  constructor_arity := by simp [decl]
  parameter_args := rfl
  domains_arity := rfl
  recursiveFields := []
  fieldPositions := []
  fieldPositions_eq := rfl
  fieldPositions_ordered := .nil
  fields_at_positions := by simp
  recursiveArgs := []
  recursiveArgs_eq := rfl
  recursive_args := List.nil_sublist _
  fieldVars := []
  fieldVars_eq := rfl
  fields_in_scope := by simp
  minorVar := 2
  minor_in_scope := by simp [ruleDomains]
  rhsArgs := [.bvar 1, .bvar 0]
  rhs_spine := rfl
  field_args := rfl
  recursive_results := rfl
  rhs_guarded := rhs_guarded

theorem block_names_nodup :
    ((sp.block.types ++ sp.block.ctors ++ sp.block.recursors).map (·.name)).Nodup := by
  simp [block, recursors_eq, VInductDecl.typeConstants, VInductDecl.constructorConstants,
    decl, indType, ctorVal, recVal, H.fam_ne_ctor, H.fam_ne_rec, H.ctor_ne_rec]

theorem ordinaryShape : sp.decl.OrdinaryShape Eb sp.block where
  types := rfl
  ctors := rfl
  projections := rfl
  recursors := by
    simp only [block, recursors_eq, decl]
    exact .cons ⟨recursorShape⟩ .nil
  rules := ⟨ET, EC, H.hT, H.hC, by
    simp only [block, equations_eq, VInductDecl.ownedConstructors, decl, indType,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
    exact .cons ⟨iotaRule _⟩ .nil⟩
  names := block_names_nodup H

theorem models : sp.sig.Models Eb sp.decl where
  uvars := rfl
  nparams := rfl
  safety := rfl
  families := .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ .nil
  constructors := by
    refine ⟨ET, H.hT, .cons ⟨rfl, rfl, ?_⟩ .nil⟩
    obtain ⟨u, h⟩ := ctorType_wf (U := 0) H.bT H.mT H.fT
    exact ⟨_, h⟩
  positiveFields := by
    refine .inr ⟨ET, H.hT, ?_⟩
    intro ctor hctor i hi
    simp only [sig] at hctor
    rcases List.mem_singleton.1 hctor with rfl
    match i, hi with
    | 0, _ => exact ⟨eFc, ⟨_, tyFc H.bT⟩, .inl (scf_Fc H)⟩
    | 1, _ => exact ⟨.app eP (.bvar 0), ⟨_, tyPapp H.bT (HasType.bvar .zero)⟩, .inl (scf_Pv H)⟩
  constructorArity := by
    intro ctor hctor
    simp only [sig] at hctor
    rcases List.mem_singleton.1 hctor with rfl
    rfl

theorem admissible : sp.inst.Admissible ET where
  levels_length := rfl
  levels_wf := by simp [inst]
  target_wf := by simp [inst, VLevel.WF]
  elimination := by
    refine .inr (.inr ⟨⟨rfl, by simp [sig], ?_⟩, 0, rfl, by simp [inst]⟩)
    intro ctor hctor i hi
    simp only [sig] at hctor
    rcases List.mem_singleton.1 hctor with rfl
    match i, hi with
    | 0, _ => exact .inr (show VExpr.bvar 1 ∈ [ec, .bvar 1, .app sp.eMap (.bvar 1)] by simp)
    | 1, _ => exact .inl (tyPapp H.bT (HasType.bvar .zero))

theorem recursiveTypesWF :
    sp.inst.RecursiveTypesWF (EC.addProjections sp.decl.projectionEntries) := by
  intro index j hj
  have h0 : index = ⟨0, by simp [sig]⟩ := Fin.ext (by have := index.isLt; simp [sig] at this; omega)
  subst h0
  exact absurd hj (Nat.not_lt_zero j)

theorem familyTypesWF :
    sp.sig.FamilyTypesWF (EC.addProjections sp.decl.projectionEntries) sp.decl.uvars := by
  intro owner
  have h0 : owner = ⟨0, by simp [sig]⟩ := Fin.ext (by have := owner.isLt; simp [sig] at this; omega)
  subst h0
  refine ⟨⟨⟨⟨trivial, ⟨_, tyC H.bC⟩⟩, ⟨_, ty_idx_F0 H.bC H.fC⟩⟩, ⟨_, ty_idx_F1 H.bC H.fC⟩⟩, ?_⟩
  exact ty_idx_fam H.bC H.fC (Γ := [])

theorem compiles : InductiveSignature.Compiles Eb sp.decl sp.block :=
  ⟨⟨sp.sig, sp.inst, ET, models H, H.hT, admissible H,
    ⟨EC, H.hC, recursiveTypesWF H, familyTypesWF H⟩, fun ⟨0, _⟩ => rfl, rfl, rfl⟩⟩

theorem blockWF : VInductBlock.WF Eb sp.block := by
  refine ⟨ET, EC, ER, H.hT, H.hC, H.hR, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    simp [block, VInductDecl.typeConstants, decl] at hci
    subst hci
    exact typeFam_wf_b H
  · intro ci hci
    simp [block, VInductDecl.constructorConstants, decl, indType] at hci
    subst hci
    exact ctorType_wf H.bT H.mT H.fT
  · intro ci hci
    simp [block, recursors_eq] at hci
    subst hci
    exact (recType_wf H.bC H.mC H.fC H.cC).mono (VEnv.addProjections_mono VEnv.addEliminators_le)
  · intro df hdf
    simp [block, equations_eq] at hdf
    subst hdf
    exact rule_wf H.bR H.mR H.fR H.cR H.rR

theorem compiledInductive : CompiledInductive Eb sp.decl sp.block :=
  CompiledInductive.ordinary (sourceWF H) (formationWF H) (compiles H) (blockWF H) rfl rfl rfl
    (block_names_nodup H)

theorem declWF : sp.decl.WF Eb := ⟨sourceWF H, .ordinary (formationWF H)⟩

theorem eliminatorsWF : VInductBlock.EliminatorsWF Eb sp.decl sp.block := by
  refine ⟨ET, EC, H.hT, H.hC, sp.fam, _, rfl, ?_, rfl, ?_⟩
  · exact CaseSchema.ofCaseCompilation_certified
      (CaseCompilationData.ofOrdinary (sourceWF H) (formationWF H) (models H) H.hT H.hC
        (familyTypesWF H) rfl rfl rfl) .nil recursorNamesFresh_nil
  · apply CaseSchema.projNamesRegistered_of_projFree
    · intro owner
      have h0 : owner = ⟨0, by simp [sig, CaseSchema.ofCompilation]⟩ :=
        Fin.ext (by have := owner.isLt; simp [sig, CaseSchema.ofCompilation] at this; omega)
      subst h0
      rfl
    · intro owner
      have h0 : owner = ⟨0, by simp [sig, CaseSchema.ofCompilation]⟩ :=
        Fin.ext (by have := owner.isLt; simp [sig, CaseSchema.ofCompilation] at this; omega)
      subst h0
      rfl

theorem induct_wf : VDecl.WF Eb (.induct sp.decl) EA :=
  .induct (declWF H) (.intro (declWF H)
    (.ordinary ⟨ordinaryShape H, compiles H, compiledInductive H⟩) (blockWF H) (eliminatorsWF H) H.hA)

end FamSpec
end Lean4Lean.Countermodel

namespace Lean4Lean.Countermodel
open VEnv

/-! ## The concrete declaration trace -/

def axC : VConstVal := { name := nC, uvars := 0, type := typeC }
def axF : VConstVal := { name := nF, uvars := 0, type := typeF }
def axc : VConstVal := { name := nc, uvars := 0, type := typec }
def axP : VConstVal := { name := nP, uvars := 0, type := typeP }
def axL : VConstVal := { name := nL, uvars := 0, type := typeMap }
def axR : VConstVal := { name := nR, uvars := 0, type := typeMap }

/-- Intermediate environments of the two installations. -/
def ETI : VEnv := (E6.addConstVals specI.decl.typeConstants).getD .empty
def ECI : VEnv := (ETI.addConstVals specI.decl.constructorConstants).getD .empty
def ERI : VEnv :=
  (((ECI.addEliminators specI.block.eliminators).addProjections specI.decl.projectionEntries).addConstVals
    specI.block.recursors).getD .empty
def ETJ : VEnv := (E7.addConstVals specJ.decl.typeConstants).getD .empty
def ECJ : VEnv := (ETJ.addConstVals specJ.decl.constructorConstants).getD .empty
def ERJ : VEnv :=
  (((ECJ.addEliminators specJ.block.eliminators).addProjections specJ.decl.projectionEntries).addConstVals
    specJ.block.recursors).getD .empty

theorem hypsI : specI.InductHyps E6 ETI ECI ERI E7 where
  hT := rfl
  hC := rfl
  hR := rfl
  hA := rfl
  bB := ⟨rfl, rfl, rfl, rfl⟩
  bT := ⟨rfl, rfl, rfl, rfl⟩
  mT := ⟨rfl⟩
  fT := ⟨rfl⟩
  bC := ⟨rfl, rfl, rfl, rfl⟩
  mC := ⟨rfl⟩
  fC := ⟨rfl⟩
  cC := ⟨rfl⟩
  bR := ⟨rfl, rfl, rfl, rfl⟩
  mR := ⟨rfl⟩
  fR := ⟨rfl⟩
  cR := ⟨rfl⟩
  rR := ⟨rfl⟩
  fam_ne_ctor := by decide
  fam_ne_rec := by decide
  ctor_ne_rec := by decide
  F_ne := by decide
  c_ne := by decide
  P_ne := by decide
  map_ne := by decide

theorem hypsJ : specJ.InductHyps E7 ETJ ECJ ERJ E8 where
  hT := rfl
  hC := rfl
  hR := rfl
  hA := rfl
  bB := ⟨rfl, rfl, rfl, rfl⟩
  bT := ⟨rfl, rfl, rfl, rfl⟩
  mT := ⟨rfl⟩
  fT := ⟨rfl⟩
  bC := ⟨rfl, rfl, rfl, rfl⟩
  mC := ⟨rfl⟩
  fC := ⟨rfl⟩
  cC := ⟨rfl⟩
  bR := ⟨rfl, rfl, rfl, rfl⟩
  mR := ⟨rfl⟩
  fR := ⟨rfl⟩
  cR := ⟨rfl⟩
  rR := ⟨rfl⟩
  fam_ne_ctor := by decide
  fam_ne_rec := by decide
  ctor_ne_rec := by decide
  F_ne := by decide
  c_ne := by decide
  P_ne := by decide
  map_ne := by decide

/-- The declaration trace, most recent first. -/
def declsCM : List VDecl :=
  [.induct specJ.decl, .induct specI.decl, .axiom axR, .axiom axL, .axiom axP, .axiom axc,
    .axiom axF, .axiom axC]

theorem envCM_wf' : VEnv.WF' declsCM envCM := by
  have h1 : VEnv.WF' [.axiom axC] E1 := .decl (.axiom typeC_wf E1_eq) .empty
  have h2 : VEnv.WF' [.axiom axF, .axiom axC] E2 := .decl (.axiom (typeF_wf rfl) E2_eq) h1
  have h3 : VEnv.WF' [.axiom axc, .axiom axF, .axiom axC] E3 :=
    .decl (.axiom (typec_wf rfl) E3_eq) h2
  have h4 : VEnv.WF' [.axiom axP, .axiom axc, .axiom axF, .axiom axC] E4 :=
    .decl (.axiom (typeP_wf rfl rfl rfl) E4_eq) h3
  have h5 : VEnv.WF' [.axiom axL, .axiom axP, .axiom axc, .axiom axF, .axiom axC] E5 :=
    .decl (.axiom (typeMap_wf rfl rfl rfl) E5_eq) h4
  have h6 : VEnv.WF' [.axiom axR, .axiom axL, .axiom axP, .axiom axc, .axiom axF,
      .axiom axC] E6 :=
    .decl (.axiom (typeMap_wf rfl rfl rfl) E6_eq) h5
  have h7 : VEnv.WF' [.induct specI.decl, .axiom axR, .axiom axL, .axiom axP, .axiom axc,
      .axiom axF, .axiom axC] E7 := .decl (FamSpec.induct_wf hypsI) h6
  exact .decl (FamSpec.induct_wf hypsJ) h7

/-- **Deliverable 1.** The countermodel environment is well formed. -/
theorem envCM_wf : VEnv.WF envCM := ⟨_, envCM_wf'⟩

end Lean4Lean.Countermodel
