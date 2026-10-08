import Lean4Lean.Verify.Inductive.Nested.AssemblyProviderEvidence
import Lean4Lean.Verify.Inductive.Nested.RestoredEquations
import Lean4Lean.Verify.Inductive.Nested.HitShapeInputs
import Lean4Lean.Verify.Inductive.Nested.FinalShapes
import Lean4Lean.Theory.Inductive.NativeIotaRestoration

/-! Final assembly certificate of a validated nested run: the pieces.

`NestedValidatedRunResult.assemblyNative` asks for a
`NestedFinalAssemblyCertificate` whose production is the run's.
`NestedValidatedRunResult.assemblyNative_of_run` (`Nested/RuleJunction.lean`)
assembles one from the run, given the rule junction `Hrules` and the recursor
provenance `Hprovenance`. This file derives everything else from the run:
the `CompilationData` and the certified specializations
(`compilationData_of_tables`, given the restored equation list) and the
realization of every concrete restored recursor entry, including its
specialization, rules (`restoredRuleRealizations`) and major inductive
(`restoredMajorInduct`). Freshness of the restorable names in the final
environment is only used outside a list `X` of names (in the application, the
renamed auxiliary recursor names, see `Nested/AuxRecNames.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature


namespace InductiveSignature





theorem Restoration.recursorName_ne_of_mem {r : Restoration}
    (hne : ∀ p ∈ r.recursors, p.2 ≠ p.1) {name : Name}
    (h : name ∈ r.recursors.map Prod.fst) : r.recursorName name ≠ name := by
  unfold Restoration.recursorName
  split
  · next pair hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [beq_iff_eq] at heq
    rw [← heq]
    exact hne pair hmem
  · next hfind =>
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
    have := List.find?_eq_none.mp hfind pair hpair
    simp at this


end InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

private theorem forall₂_imp_mem_right {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, b ∈ l₂ → R a b → S a b) → List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H =>
    .cons (H _ _ List.mem_cons_self h)
      (forall₂_imp_mem_right t fun a b hb h => H a b (List.mem_cons_of_mem _ hb) h)

/-! ### The installed restored recursors -/

/-- The restored recursor of one inductive restoration step is an entry of a
fresh trace of that step. -/
theorem RestoredInductiveDeclResult.freshTraceWithRecInfo
    (H : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ConstantInfo.recInfo H.recursor.restored.newInfo ∈ entries := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : StateForMTrace
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshTrace hwfHeader with
    ⟨constructors, Hconstructors⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  refine ⟨header :: constructors ++ [recursor], ?_, by simp [recursor]⟩
  rw [htarget]
  exact FreshConstantTrace.cons hheaderFresh
    (Hconstructors.append (.cons hrecFresh .nil))

theorem StateForMTrace.inductiveFreshTraceWithRecInfos
    (H : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ t ∈ types, ∃ (s t' : Environment) (Hs : RestoredRecursorStep result loweredEnv
        auxRec allIndNames (Lean.mkRecName t.name) s t'),
        ConstantInfo.recInfo Hs.restored.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshTraceWithRecInfo hwf with ⟨headEntries, Hhead, hmem⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail, htail⟩
    refine ⟨headEntries ++ tailEntries, Hhead.append Htail, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨_, _, Hstep.restored.recursor, by simp [hmem]⟩
    · rcases htail t ht with ⟨s, t', Hs, hs⟩
      exact ⟨s, t', Hs, by simp [hs]⟩

theorem StateForMTrace.recursorFreshTraceWithRecInfos
    (H : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ n ∈ names, ∃ (s t : Environment) (Hs : RestoredRecursorStep result loweredEnv
        auxRec allIndNames n s t),
        ConstantInfo.recInfo Hs.restored.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hnames⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    intro n hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact ⟨_, _, Hstep, by simp [ci]⟩
    · rcases hnames n hn with ⟨s, t, Hs, hs⟩
      exact ⟨s, t, Hs, by simp [hs]⟩

/-- Every restoration step at a restored recursor name of a complete nested
restoration installs its restored recursor in the output environment. -/
theorem RestoredNestedDeclarationsResult.find_restoredRecursor
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF)
    {n : Name} (hn : n ∈ types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t) :
    out.2.find? Hstep.restored.newInfo.name =
      some (.recInfo Hstep.restored.newInfo) := by
  rcases H.inductives.inductiveFreshTraceWithRecInfos hwf with
    ⟨primaryEntries, Hprimary, hprimary⟩
  rcases H.auxiliaries.recursorFreshTraceWithRecInfos (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliary⟩
  have Htrace := Hprimary.append Hauxiliary
  have hmem : ∃ (s' t' : Environment) (Hs : RestoredRecursorStep result loweredEnv
      auxRec allIndNames n s' t'),
      ConstantInfo.recInfo Hs.restored.newInfo ∈ primaryEntries ++ auxiliaryEntries := by
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
      obtain ⟨s', t', Hs, hs⟩ := hprimary t ht
      exact ⟨s', t', Hs, List.mem_append_left _ hs⟩
    · obtain ⟨s', t', Hs, hs⟩ := hauxiliary n hn
      exact ⟨s', t', Hs, List.mem_append_right _ hs⟩
  obtain ⟨s', t', Hs, hs⟩ := hmem
  have hsame := (Hs.info_eq Hstep).2
  rw [← hsame]
  exact Htrace.findEntry hwf hs

/-- Every installed entry of a staged constant list has the name of its
abstract value. -/
theorem AddConstants.name_eq
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ entry ∈ entries, entry.1.name = entry.2.name := by
  induction H with
  | nil => simp
  | cons _ _ htr _ _ _ _ ih =>
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · exact htr.2
    · exact ih entry hentry

/-- The recursor entries of a final assembly shape are installed in the
output environment under the names of their abstract values. -/
theorem NestedFinalAssemblyShape.find_recursorEntry
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety)
    (hwf : sourceProdEnv.constants.WF) :
    ∀ entry ∈ C.recursorEntries,
      outEnv.find? entry.2.name = some entry.1 := by
  intro entry hentry
  rcases H.freshTrace hwf with ⟨actual, Hactual⟩
  have hperm := C.productionOrder actual Hactual
  have hmem : entry.1 ∈ actual := hperm.symm.mem_iff.mp
    (List.mem_map.mpr ⟨entry, List.mem_append_right _ hentry, rfl⟩)
  rw [← C.canonical.recursorsAdded.name_eq entry hentry]
  exact Hactual.findEntry hwf hmem

/-- `compilationData_of_hitShape'` at a given specialization list of
`restorationTablesRestoringAll` (rather than at an existentially chosen one):
the restored recursors and equations of the canonical restored block of a
shape whose rule lists are the restored generated equations (`hequations`;
see `restoredEquations_of_hitShape` and `restoredEquations_of_realizationModulo`)
form a `CompilationData`, and the specializations are certified. -/
theorem NestedValidatedRunResult.compilationData_of_tables
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hrestoring : List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length))
    (HauxRestoring : List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
            (VLevel.params sourceDecl.uvars)))
        generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hequations : E.production.compilationInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (C.primaryRules ++ C.auxiliaryRules)) :
    CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      Nonempty (CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
        sourceDecl E.production.loweredDecl E.production.compilationSignature
        E.production.compilationInstance auxiliaries
        (canonicalRestoredBlock sourceDecl C.primaryRecursors
          C.auxiliaryRecursors C.primaryRules C.auxiliaryRules)) := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hP := E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnames, hheadNames, hcertified, -, hwellFormed, hscoped, hdirect, -⟩ := hP
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames
  have hrecursors := E.restoredRecursors_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have htotal := E.normalizedTotal_of wf Hsources hheadNames
  have HsourceCtors := E.sourceConstructors_of_evidence wf hadded henvTypes Haux Hexpansion
    hnodup hfresh hrecFresh
    ⟨E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring hlevels,
      fun n hn => htotal n (List.mem_of_mem_take hn)⟩
  have HauxFamilies := E.auxiliaryFamiliesField_of_evidence wf hadded henvTypes Haux
    Hexpansion
    (E.auxiliaryConstructors_of_evidence wf Hsources hadded henvTypes Haux Hexpansion
      HauxRestoring hnodup (fun n hn => htotal n (List.mem_of_mem_drop hn)))
  exact ⟨hcertified, ⟨E.compilationData_of_specializations C hC hadded hnames hwellFormed
    hscoped hdirect
    { sourceConstructors := HsourceCtors
      auxiliaryFamilies := HauxFamilies
      recursors := hrecursors
      equations := hequations }⟩⟩

/-- The recursor entries of a final assembly shape of a validated nested run,
in owner order: each entry's concrete constant is the restored recursor of a
restoration step at the owner's lowered recursor name, and its abstract value
is the abstract restoration of the owner's generated recursor and the
translation of that restored recursor. -/
theorem NestedValidatedRunResult.restoredRecursorEntryInfos
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hwf : sourceProdEnv.constants.WF) :
    List.Forall₂ (fun owner (entry : ConstantInfo × VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
          entry.1 = .recInfo Hstep.restored.newInfo ∧
          (compilationRestoration sourceDecl auxiliaries).recursor
            (E.production.production.completed.canonicalGeneration.recursor owner) =
              some entry.2 ∧
          RestoredRecursorStepValue
            ((C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections sourceDecl.projectionEntries) Hstep
            entry.2)
      (List.finRange
        E.production.production.completed.generationSignature.families.size)
      C.recursorEntries := by
  have Hentries := E.restoredRecursorEntries_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  rw [← C.recursorValues, List.forall₂_map_right_iff] at Hentries
  have hnames := E.recursorNames_order C.sourceNonempty
  have hrecursorEntries : ∀ entry ∈ C.recursorEntries,
      outEnv.find? entry.2.name = some entry.1 := C.find_recursorEntry hwf
  refine forall₂_imp_mem_right Hentries ?_
  rintro owner entry hentry ⟨hrec, s, t, Hstep, Hw⟩
  refine ⟨s, t, Hstep, ?_, hrec, Hw⟩
  have hn : E.production.production.completed.canonicalGeneration.recursorName owner ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange owner)
  have hfind := E.restoration.find_restoredRecursor hwf hn Hstep
  have hname : entry.2.name = Hstep.restored.newInfo.name :=
    Hw.1.trans Hstep.restored.restoration.name.symm
  have hfind' := hrecursorEntries entry hentry
  rw [hname] at hfind'
  exact Option.some.inj (hfind'.symm.trans hfind)

/-! ### The major inductive of a restored recursor -/

/-- **The major inductive of a restored recursor** is the restored head of its
generated owner family. -/
theorem NestedValidatedRunResult.restoredMajorInduct
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t) :
    Hstep.restored.newInfo.getMajorInduct =
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.production.compilationSignature.families[owner].name := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.production.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.production.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, -, h1, -⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, h1⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement VEnv.empty lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  -- the lowered family name is the signature's
  have hfamName : (E.production.loweredDecl.types[owner.val]'hi').name =
      E.production.compilationSignature.families[owner].name := by
    obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
    have h1 := E.production.production.completed.generated_getMajorInduct owner.val hi
    rw [hinfo] at h1
    exact h1.symm.trans (E.recursorMetadataOfStep owner Hstep).major
  rw [hmi, ← hfamName]
  rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfind, hfn⟩
  · have hfind : r.heads.find? (fun h => h.auxiliary ==
        (E.production.loweredDecl.types[owner.val]'hi').name) = none :=
      Restoration.heads_find?_eq_none hnot
    simp only [Restoration.restoredHeadName, r] at hfind ⊢
    rw [hfind, hceq]
  · obtain ⟨b, hb, hbaux, envS, domains, lvls, Ys, -, hab, -, -⟩ := D.familyKey _ nested hfind
    have hhead : nested.getAppFn = .const b.source.name lvls := by
      obtain ⟨xs, hxs⟩ := D.paramsFVars
      rw [hxs, Expr.abstractN_eq] at hab
      exact abstractN_getAppFn_const nested 0
        (by rw [hab, Expr.getAppFn_mkAppList_const])
    rw [hfn] at hhead
    have hcb : c = b.source.name := (Expr.const.inj hhead).1
    have hmem : (⟨b.auxiliary, sourceDecl.uvars, sourceDecl.nparams, b.source.name, b.levels,
        b.arguments⟩ : HeadSpecialization) ∈ r.heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have hfindB := Restoration.find?_of_nodup hscoped.1 hmem
    rw [hbaux] at hfindB
    simp only [Restoration.restoredHeadName] at hfindB ⊢
    rw [hfindB, hcb]

/-- The specialization clause of `RestoredRecursorRealization`. -/
def RestoredRecursorSpecialization {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (venv : VEnv) (owner : Fin s.families.size)
    (rec : Lean.RecursorVal) : Prop :=
  ∃ head,
    g.restoredFamilyHead r owner = some head ∧
    rec.getMajorInduct = head.name ∧
    (∀ level ∈ head.levels, level.WF g.uvars) ∧
    (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
    r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0)) ∧
    List.Forall₂ (RestoredRuleRealization g r venv rec.levelParams head)
      (s.ownedConstructors owner) rec.rules

/-- **One restored recursor realization**, modulo its specialization clause:
the restored recursor of a restoration step at a generated owner's lowered
recursor name realizes the owner's restored generated recursor. -/
theorem NestedValidatedRunResult.restoredRecursorRealization_of_step
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name))
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t)
    {trEnv venv : VEnv} (hle : trEnv ≤ venv) {w : VConstVal}
    (hrec : (compilationRestoration sourceDecl auxiliaries).recursor
      (E.production.compilationInstance.recursor owner) = some w)
    (Hw : RestoredRecursorStepValue trEnv Hstep w)
    (Hspec : RestoredRecursorSpecialization E.production.compilationInstance
      (compilationRestoration sourceDecl auxiliaries) venv owner Hstep.restored.newInfo) :
    RestoredRecursorRealization E.production.compilationInstance
      (compilationRestoration sourceDecl auxiliaries) (sourceDecl.types.map (·.name))
      venv owner Hstep.restored.newInfo := by
  have M := E.recursorMetadataOfStep owner Hstep
  have R := Hstep.restored.restoration
  obtain ⟨hwname, hwuvars, Ht⟩ := Hw
  refine {
    name := ?_
    uvars := ?_
    type := ?_
    numParams := R.numParams.trans M.numParams
    numIndices := R.numIndices.trans M.numIndices
    numMotives := R.numMotives.trans M.numMotives
    numMinors := R.numMinors.trans M.numMinors
    all := ?_
    isUnsafe := R.isUnsafe.trans M.isUnsafe
    specialization := Hspec
    k := fun hk => M.k (R.k ▸ hk) }
  · rw [D.recursorName, R.name, Hstep.restored.mappedName]
    exact nameMap_getD_eq _ _ _
  · rw [R.levelParams]; exact M.uvars
  · simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hrec
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.recursor owner).type with
    | none => simp [ht] at hrec
    | some type =>
      simp only [ht, Option.bind_some, Option.some.injEq] at hrec
      subst hrec
      exact ⟨type, ht, Ht.mono hle⟩
  · rw [R.all, hnames]

private theorem mem_zipIdx_of_mem' {l : List α} {x : α} (h : x ∈ l) :
    ∃ i, (x, i) ∈ l.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩

/-- **The restored rules of one restored recursor.** Given the restored
family head of its owner (with the constructor restorations of
`CompilationData.restoredFamilyHead_spec`), every rule of the restored
recursor of a restoration step realizes its generated constructor, against
the canonical restored rule list, in an abstract environment in which the
restored recursor is installed and the restorable names outside `X` are
fresh, provided no lowered auxiliary recursor name `A.rec` lies in `X` (for
`X` the renamed recursor names: `auxRecName_not_renamed`). -/
theorem NestedValidatedRunResult.restoredRuleRealizations
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {auxiliaries : List ContainerSpecialization} {venv : VEnv} {rules : List VDefEq}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hctorNames : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          (a.constructorName ctor))
    (hrecNames : ∀ owner, E.production.compilationInstance.recursorName owner =
      E.production.compilationSignature.families[owner].name.str "rec")
    (hheadsNotRec : ∀ owner, ∀ head ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      head.auxiliary ≠ E.production.compilationInstance.recursorName owner)
    {X : List Name}
    (hfreshFinal : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → venv.constants n = none)
    (hauxRec : ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∉ X)
    (hequations : E.production.compilationInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some rules)
    (Hrules : List.Forall₂
      (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries) venv)
      (List.finRange E.production.compilationSignature.constructors.size) rules)
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t)
    (hinstalled : venv.constants Hstep.restored.newInfo.name ≠ none)
    (head : RestoredFamilyHead)
    (Hctor : ∀ index : Fin E.production.compilationSignature.constructors.size,
      E.production.compilationSignature.constructors[index].owner = owner →
        (((compilationRestoration sourceDecl auxiliaries).heads.find?
            (fun h => h.auxiliary ==
              E.production.compilationSignature.families[owner].name) = none ∧
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.production.compilationSignature.constructors[index].name =
              E.production.compilationSignature.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, E.production.compilationSignature.families[owner].name =
              a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, E.production.compilationSignature.constructors[index].name =
              a.constructorName ctor) ∧
        (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.compilationInstance.constructorApp
            E.production.compilationSignature.constructors[index]
            (E.production.compilationSignature.families.size +
              E.production.compilationSignature.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
              E.production.compilationSignature.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (E.production.compilationSignature.families.size +
                E.production.compilationSignature.constructors.size +
                E.production.compilationSignature.constructors[index].fields.length)) ++
              vars E.production.compilationSignature.constructors[index].fields.length 0))) :
    List.Forall₂ (InductiveSignature.RestoredRuleRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries) venv
        Hstep.restored.newInfo.levelParams head)
      (E.production.compilationSignature.ownedConstructors owner)
      Hstep.restored.newInfo.rules := by
  let P := E.production.production.completed
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have RR := P.ruleRealizations P.ruleRhsTranslations owner hi
  rw [hinfo] at RR
  have hmap := P.ownedConstructors_map_val owner hi
  rw [hinfo] at hmap
  have R := Hstep.restored.restoration
  have hlenNew : Hstep.restored.newInfo.rules.length = Hstep.oldInfo.rules.length :=
    R.rules.length
  have hlenOwned : (E.production.compilationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h2 : (P.generationSignature.ownedConstructors owner).length =
        Hstep.oldInfo.rules.length := by
      simpa using congrArg List.length hmap
    exact h2
  -- the equation list, pointwise
  have Heqs := List.mapM_eq_some.mp hequations
  have hlenRules : rules.length = E.production.compilationSignature.constructors.size := by
    have h1 := Lean4Lean.List.Forall₂.length_eq Hrules
    have h2 : (List.finRange E.production.compilationSignature.constructors.size).length =
        E.production.compilationSignature.constructors.size := List.length_finRange
    exact h1.symm.trans h2
  apply Lean4Lean.List.forall₂_of_getElem (hlenOwned.trans hlenNew.symm)
  intro j hj hjNew
  have hjOld : j < Hstep.oldInfo.rules.length := hlenOwned ▸ hj
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  let index := (E.production.compilationSignature.ownedConstructors owner)[j]
  have hindexOwner : E.production.compilationSignature.constructors[index].owner = owner := by
    have hmem : index ∈ E.production.compilationSignature.ownedConstructors owner :=
      List.getElem_mem hj
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
    exact hmem.2
  have RRj := Lean4Lean.List.forall₂_getElem RR j hj hjOld
  have Rj := R.rules.entry j hjOld hjNew
  obtain ⟨hclass, happ⟩ := Hctor index hindexOwner
  -- the restored constructor name
  have hrecMem : ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∈
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
    intro a ha
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem' ha
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨(a, i), hi, rfl⟩, rfl⟩
  -- the restored constructor name
  have hctor : (Hstep.restored.newInfo.rules[j]'hjNew).ctor =
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.production.compilationSignature.constructors[index].name := by
    rw [Rj.ctor, RRj.ctor]
    rcases hclass with ⟨hfind, hheadId⟩ | ⟨a, ha, hfam, ctor, hctor, hcName⟩
    · have hnotRec : E.production.compilationInstance.recursorName owner ∉
          (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
        intro hmem
        obtain ⟨pair, hpair, hpairName⟩ := List.mem_map.mp hmem
        obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hpair
        have ha : a ∈ auxiliaries := List.fst_mem_of_mem_zipIdx hai
        have hfamName : E.production.compilationSignature.families[owner].name =
            a.auxiliary := by
          have h := hpairName.trans (hrecNames owner)
          exact (Name.str.inj h).1.symm
        have hmemHead : (⟨a.auxiliary, sourceDecl.uvars, sourceDecl.nparams, a.source.name,
            a.levels, a.arguments⟩ : HeadSpecialization) ∈
              (compilationRestoration sourceDecl auxiliaries).heads :=
          List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
        have := List.find?_eq_none.mp hfind _ hmemHead
        simp only [beq_iff_eq] at this
        exact this (by simpa using hfamName.symm)
      have hsame : Hstep.restored.newRecName =
          E.production.compilationInstance.recursorName owner := by
        rw [Hstep.restored.mappedName, nameMap_getD_eq, ← D.recursorName]
        exact Restoration.recursorName_of_not_mem hnotRec
      simp only [hsame, beq_self_eq_true, if_true]
      exact hheadId.symm
    · have hold : E.production.compilationInstance.recursorName owner =
          a.auxiliary.str "rec" := by
        rw [hrecNames owner, hfam]
      have hfreshOld : venv.constants (E.production.compilationInstance.recursorName owner) =
          none := by
        rw [hold]
        exact hfreshFinal _ (List.mem_append_right _ (hrecMem a ha)) (hauxRec a ha)
      have hne : (Hstep.restored.newRecName ==
          E.production.compilationInstance.recursorName owner) = false := by
        have : Hstep.restored.newRecName ≠
            E.production.compilationInstance.recursorName owner := by
          intro h
          apply hinstalled
          rw [R.name, h]
          exact hfreshOld
        simpa using this
      simp only [hne, Bool.false_eq_true, if_false]
      show result.restoreCtorName E.loweredEnv
          E.production.compilationSignature.constructors[index].name = _
      rw [hcName]
      exact hctorNames a ha ctor hctor
  have hindexLt : index.val < rules.length := by rw [hlenRules]; exact index.isLt
  have hindexEq : index.val < E.production.compilationInstance.equations.length := by
    simp [InductiveSignature.Instance.equations]
  have Heq := Lean4Lean.List.forall₂_getElem Heqs index.val hindexEq hindexLt
  have hgetEq : E.production.compilationInstance.equations[index.val]'hindexEq =
      E.production.compilationInstance.equation index := by
    simp [InductiveSignature.Instance.equations]
  rw [hgetEq] at Heq
  refine {
    ctor := hctor
    nfields := Rj.nfields.trans RRj.nfields
    constructorApplication := by rw [hctor]; exact happ
    equation := ⟨rules[index.val]'hindexLt, Heq, ?_, ?_⟩ }
  · have hleft : (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.equation index).lhs =
          some (rules[index.val]'hindexLt).lhs := by
      simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at Heq
      cases hl : (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.compilationInstance.equation index).lhs with
      | none => simp [hl] at Heq
      | some lhs =>
        simp only [hl, Option.bind_some] at Heq
        cases hr : (compilationRestoration sourceDecl auxiliaries).expr
            (E.production.compilationInstance.equation index).rhs with
        | none => simp [hr] at Heq
        | some rhs =>
          simp only [hr, Option.bind_some] at Heq
          cases hty : (compilationRestoration sourceDecl auxiliaries).expr
              (E.production.compilationInstance.equation index).type with
          | none => simp [hty] at Heq
          | some ty =>
            simp only [hty, Option.bind_some, Option.some.injEq] at Heq
            rw [← Heq]
    exact Restoration.wrapLams_head_const
      (hheadsNotRec E.production.compilationSignature.constructors[index].owner)
      (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  · -- the right-hand side, from the realization at the same flattened index
    have hfinLt : index.val <
        (List.finRange E.production.compilationSignature.constructors.size).length := by
      rw [List.length_finRange]; exact index.isLt
    have HR := Lean4Lean.List.forall₂_getElem Hrules index.val hfinLt hindexLt
    have hfv : ((List.finRange E.production.compilationSignature.constructors.size)[index.val]'
        hfinLt).val = index.val := by simp
    obtain ⟨owner', j', s', t', Hstep', hj', hk0, -, Ht, -, -⟩ := HR
    have hk' : index.val = recursorMinorOffset E.production.indTypes owner'.val + j' :=
      hfv.symm.trans hk0
    obtain ⟨hi', hinfo'⟩ := E.generatedEntryOfStep owner' Hstep'
    have hsrcOf : ∀ (o : Nat) (ho : o < P.entries.length), o < E.production.indTypes.size := by
      intro o ho
      have hrec : o < P.recInfos.size := by rw [← P.generated.length]; exact ho
      rw [← P.recInfos_size_eq_source]; exact hrec
    have hcntOf : ∀ (o : Nat) (ho : o < P.entries.length),
        (P.generated.entry o ho).info.rules.length =
          E.production.indTypes[o]!.ctors.length :=
      fun o ho => (P.generated.entry o ho).rules.length
    have hlocal : j < E.production.indTypes[owner.val]!.ctors.length := by
      rw [← hcntOf owner.val hi, hinfo]; exact hjOld
    have hlocal' : j' < E.production.indTypes[owner'.val]!.ctors.length := by
      rw [← hcntOf owner'.val hi', hinfo', ← Hstep'.restored.restoration.rules.length]
      exact hj'
    obtain ⟨howner, hjj⟩ := recursorMinorOffset_unique E.production.indTypes
      (hsrcOf owner.val hi) (hsrcOf owner'.val hi') hlocal hlocal' (hval.symm.trans hk')
    subst hjj
    have hownerEq : owner' = owner := Fin.ext howner.symm
    subst hownerEq
    have hnew := (Hstep'.info_eq Hstep).2
    have key : ∀ (info : RecursorVal) (h : j < info.rules.length),
        info = Hstep.restored.newInfo →
        TrExprS venv info.levelParams [] (info.rules[j]'h).rhs
          (rules[index.val]'hindexLt).rhs →
        TrExprS venv Hstep.restored.newInfo.levelParams []
          (Hstep.restored.newInfo.rules[j]'hjNew).rhs (rules[index.val]'hindexLt).rhs := by
      intro info h hinfo'' H
      subst hinfo''
      exact H
    exact key _ hj' hnew Ht

end VerifyInductive
end Lean4Lean
