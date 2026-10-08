import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorTranslations
import Lean4Lean.Verify.Inductive.Nested.Lowering.Recognition
import Lean4Lean.Verify.Inductive.Install.LiteralNames

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One operational auxiliary recursor restoration step: the translated
recursor constant and the abstract rule batch of the step, of the restored
length. The record fixes no equation syntax; the final producer result
supplies the finite canonical compilation of the rules. -/
structure AuxiliaryRecursorGuardedRules
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv)
    (priorRecursors : List VConstVal) where
  recursor : VConstVal
  rules : List VDefEq
  translated : TrConstVal safety trEnv
    (.recInfo Hstep.restored.newInfo) recursor
  rulesLength : rules.length = Hstep.restored.newInfo.rules.length

/-- Trace-aligned steps of an auxiliary restoration fold. The chosen
rule batches are retained explicitly, but this judgment alone does not
constrain their left-hand sides or establish their concrete realization. -/
inductive AuxiliaryRecursorsGuardedRules
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv : VEnv) :
    ∀ {names sourceEnv targetEnv},
      FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv →
      List VConstVal → List VDefEq →
      List VConstVal → List VDefEq → Prop
  | nil (sourceEnv) (recursors rules) :
      AuxiliaryRecursorsGuardedRules decl block main safety trEnv
        (FoldSteps.nil (P :=
          RestoredRecursorStep result loweredEnv auxRec allIndNames)
          (source := sourceEnv)) recursors rules recursors rules
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hsemantic : AuxiliaryRecursorGuardedRules decl block main safety trEnv
        Hstep priorRecursors)
      (Hrest : AuxiliaryRecursorsGuardedRules decl block main safety trEnv
        Htail (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules) :
      AuxiliaryRecursorsGuardedRules decl block main safety trEnv
        (.cons Hstep Htail) priorRecursors priorRules
          finalRecursors finalRules

/-- Semantic payload for one restored primary recursor. -/
structure SourceRecursorTranslation
    (decl : VInductDecl) (owner : VInductiveType)
    (safety : DefinitionSafety)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (sourceVEnv : VEnv) where
  recursor : VConstVal
  safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type
  name : recursor.name = Hstep.restored.newRecName
  wf : recursor.toVConstant.WF sourceVEnv
  shape : Nonempty (decl.NestedRecursorShape owner recursor)

/-- Independent source-level meaning of one primary recursor.  In particular,
this object mentions neither the lowered declaration nor any production
restoration step: it is the abstract specification which the executable
recursor construction must refine. -/
structure SourceRecursorSpec
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (canonicalEnv : VEnv) where
  recursor : VConstVal
  name : recursor.name = sourceDecl.recursorName owner
  isType : canonicalEnv.IsType recursor.uvars [] recursor.type
  shape : Nonempty (sourceDecl.NestedRecursorShape owner recursor)

/-- Executable-to-specification refinement for a restored primary recursor.
The source recursor is fixed by `SourceRecursorSpec`; this record
states that the concrete restoration step has exactly its universe arity and
translates its restored telescope to exactly its abstract type. -/
structure SourceRecursorRefinement
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) : Prop where
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type

/-- One abstract source recursor realized by a particular restored concrete
recursor.  The equality field prevents the source witness and refinement
proof from drifting to different constants. -/
structure TrSourceRecursor
    (sourceDecl : VInductDecl) (sourceOwner : VInductiveType)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) where
  source : SourceRecursorSpec sourceDecl sourceOwner canonicalEnv
  recursor_eq : source.recursor = recursor
  refinement : SourceRecursorRefinement Hstep canonicalEnv recursor

/-- Source semantics for the inductive families in one restoration trace. -/
inductive SourceFamilyTranslations
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety)
    (sourceVEnv envTypes envCtors : VEnv) :
    ∀ {types sourceProdEnv targetProdEnv},
      FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors
        (FoldSteps.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : SourceRecursorTranslation decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : SourceFamilyTranslations decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors (.cons Hstep Htail) (owner :: owners)
        (Hrecursor.recursor :: recursors)

/-- All canonical-stage semantic data for one exact operational family
restoration step.  Bundling the fields keeps mutual-trace assembly independent
of how headers, constructors, and primary recursors are proved. -/
structure SourceFamilyTranslation
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety) (sourceVEnv envTypes envCtors : VEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  owner : VInductiveType
  header : TrSourceConst sourceVEnv lparams indType.name indType.type
    owner.toVConstVal
  constructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
    Hstep.oldInfo.ctors Hstep.restored.headerEnv
      Hstep.restored.constructorEnv indType.ctors owner.ctors
  recursor : SourceRecursorTranslation decl owner safety
    Hstep.restored.recursor envCtors

theorem SourceFamilyTranslations.types
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (TrInductiveType sourceVEnv envTypes lparams)
      sourceTypes owners := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hheader, Hconstructors.forall₂⟩ ih

/-- Header well-formedness is already pointwise data in the exact restored
source trace; no separate final-assembly premise is needed. -/
theorem SourceFamilyTranslations.typeConstantsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners) :
    ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF sourceVEnv := by
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨owner, howner, rfl⟩
  have howner' : owner ∈ owners := by
    rw [← htypes]
    exact howner
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types owner howner' with
    ⟨_source, _hsource, Howner⟩
  exact Howner.header.wf

/-- Constructor well-formedness is likewise fixed by the canonical
post-header interpretation of the restoration trace. -/
theorem SourceFamilyTranslations.constructorConstantsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners) :
    ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF envTypes := by
  intro ci hci
  simp only [VInductDecl.constructorConstants] at hci
  rcases List.mem_flatMap.mp hci with ⟨owner, howner, hctor⟩
  have howner' : owner ∈ owners := by
    rw [← htypes]
    exact howner
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types owner howner' with
    ⟨_source, _hsource, Howner⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Howner.ctors ci hctor with
    ⟨_sourceCtor, _hsourceCtor, Hctor⟩
  exact Hctor.wf

/-- Primary restored recursors are typed in the canonical environment that
already contains every mutual constructor. -/
theorem SourceFamilyTranslations.primaryRecursorsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    ∀ ci ∈ recursors, ci.toVConstant.WF envCtors := by
  induction H with
  | nil => simp
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    intro ci hci
    simp only [List.mem_cons] at hci
    rcases hci with rfl | hrest
    · exact Hrecursor.wf
    · exact ih ci hrest

/-- Reconstruct the independent source declaration translation from the
canonical-stage semantic trace.  The executable restoration trace fixes all
pointwise source/target correspondences; only the canonical abstract stage
extensions and declaration metadata are supplied separately. -/
theorem SourceFamilyTranslations.core
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners)
    (huvars : decl.uvars = lparams.length)
    (hnparams : decl.nparams = nparams)
    (hisUnsafe : decl.isUnsafe = isUnsafe)
    (htypesAdded : sourceVEnv.addConstVals decl.typeConstants = some envTypes)
    {envCtors' : VEnv}
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors') :
    TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe decl
      envTypes envCtors' := by
  refine {
    uvars := huvars
    nparams := hnparams
    isUnsafe := hisUnsafe
    typesAdded := htypesAdded
    ctorsAdded := hctorsAdded
    types := ?_ }
  rw [htypes]
  exact H.types

/-- Installation semantics for one complete restored source family: header,
its exact constructor fold, and its primary recursor. -/
def canonicalRestoredBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  projections := decl.projectionEntries
  recursors := primaryRecursors ++ auxiliaryRecursors
  rules := primaryRules ++ auxiliaryRules

theorem addConstant_find_self
    (env : Environment) (info : ConstantInfo)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none) :
    (Lean4Lean.AddInductive.addConstant env info).find? info.name = some info := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change (env.constants.insert info.name info).find?' info.name = some info
  rw [(hwf.insert info.name info hfresh).find?'_eq_find?, hwf.find?_insert]
  simp

theorem addConstant_find_of_ne
    (env : Environment) (info : ConstantInfo) (name : Name)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none)
    (hne : info.name ≠ name) (hfind : env.find? name = some found) :
    (Lean4Lean.AddInductive.addConstant env info).find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh hfind
  change (env.constants.insert info.name info).find?' name = some found
  rw [(hwf.insert info.name info hfresh).find?'_eq_find?, hwf.find?_insert]
  split
  · rename_i heq
    exact False.elim (hne (by simpa using heq))
  · exact hfind

theorem addConstant_find_cases
    (env : Environment) (info : ConstantInfo) (name : Name)
    (hwf : env.constants.WF) (hfresh : env.find? info.name = none)
    (hfind : (Lean4Lean.AddInductive.addConstant env info).find? name =
      some found) :
    (name = info.name ∧ found = info) ∨ env.find? name = some found := by
  have hfreshMap : env.constants.find? info.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change (env.constants.insert info.name info).find?' name = some found at hfind
  rw [(hwf.insert info.name info hfreshMap).find?'_eq_find?,
    hwf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    left
    simp only [Option.some.injEq] at hfind
    have hEq : info.name = name := by simpa using heq
    exact ⟨hEq.symm, hfind.symm⟩
  · right
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

/-- A lockstep installation preserves every lookup from its source production
environment. -/
theorem AddConstants.preservesFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    outEnv.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hfind] at hn
      contradiction
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    apply ih hnextWF
    change (Lean4Lean.AddInductive.addConstant envHead ci).find? name = some found
    exact addConstant_find_of_ne envHead ci name hwf hn hne hfind

/-- Every lookup in the target of a lockstep installation either came from
the source environment or is one of the exact newly installed production
entries. -/
theorem AddConstants.origin
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : outEnv.find? name = some found) :
    env.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.1.name ∧ found = entry.1 := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · rcases addConstant_find_cases envHead ci name hwf hn hnext with
        ⟨hname, hfound⟩ | hold
      · exact Or.inr ⟨(ci, ci'), by simp, hname, hfound⟩
      · exact Or.inl hold
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

theorem AddConstants.entryNames
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hentry : entry ∈ entries) : entry.1.name = entry.2.name := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact htr.2
    · exact ih htail

/-- A successful lockstep installation makes every constructor recognized as
belonging to a fresh auxiliary family absent from the original abstract
environment. -/
theorem AddConstants.restoreAuxConstructorsFresh
    (H : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (Hfamilies : RestoreAuxFamiliesFresh result sourceProdEnv) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  intro name nested auxFamily hrecognized
  rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
      hrecognized with ⟨⟨info, hlookup, hfamily, hmap⟩⟩
  rcases H.origin hwf hlookup with hold | hnew
  · rcases Howners name info hold with ⟨owner, howner⟩
    have hfresh := Hfamilies info.induct nested hmap
    rw [howner] at hfresh
    contradiction
  · rcases hnew with ⟨entry, hentry, hname, hfound⟩
    have habstractFresh := (VEnv.addConstVals_names_fresh H.abstract).2
      entry.2 (List.mem_map.mpr ⟨entry, hentry, rfl⟩)
    have hentryNames := H.entryNames hentry
    rw [hname, hentryNames]
    exact habstractFresh

/-- Every production entry named by an `AddConstants` certificate is present
with its exact metadata in the final environment. -/
theorem AddConstants.findOfMem
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hentry : (info, value) ∈ entries) :
    outEnv.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    simp only [List.mem_cons] at hentry
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    rcases hentry with hhead | htail
    · have hinstalled : outProd.find? ci.name = some ci := by
        apply Htail.preservesFind hnextWF
        change (Lean4Lean.AddInductive.addConstant envHead ci).find? ci.name = some ci
        exact addConstant_find_self envHead ci hwf hn
      have hi : info = ci := congrArg Prod.fst hhead
      simpa [hi] using hinstalled
    · exact ih hnextWF htail

/-- Exact lookup effect of the executable mutual-header installation fold. -/
structure InductiveInfosAdded
    (source : Environment) (infos : List InductiveVal)
    (target : Environment) : Prop where
  mapWF : target.constants.WF
  preserves : ∀ {name found}, source.find? name = some found →
    target.find? name = some found
  origin : ∀ {name found}, target.find? name = some found →
    source.find? name = some found ∨
      ∃ info ∈ infos, name = info.name ∧ found = .inductInfo info
  installed : ∀ info ∈ infos,
    target.find? info.name = some (.inductInfo info)
  sourceFresh : ∀ info ∈ infos, source.find? info.name = none
  namesNodup : (infos.map (fun info => info.name)).Nodup

theorem declareInductiveTypeInfos_refines
    (allowPrimitive : Bool) (infos : List InductiveVal) (env : Environment)
    (hwf : env.constants.WF) :
    (Lean4Lean.AddInductive.declareInductiveTypeInfos
      allowPrimitive infos env).WF fun out =>
        InductiveInfosAdded env infos out := by
  induction infos generalizing env with
  | nil =>
    simp only [Lean4Lean.AddInductive.declareInductiveTypeInfos]
    exact Except.WF.pure ⟨hwf, fun h => h, fun h => Or.inl h,
      by simp, by simp, by simp⟩
  | cons info infos ih =>
    rw [Lean4Lean.AddInductive.declareInductiveTypeInfos]
    exact (checkName.WF hwf info.name allowPrimitive).bind fun _ hchecked => by
      have hfresh := hchecked.1
      have hfreshMap : env.constants.find? info.name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
      let nextEnv := Lean4Lean.AddInductive.addConstant env (.inductInfo info)
      have hnextWF : nextEnv.constants.WF := by
        change (env.constants.insert info.name (.inductInfo info)).WF
        exact hwf.insert info.name (.inductInfo info) hfreshMap
      exact (ih nextEnv hnextWF).mono fun out Htail => by
        refine ⟨Htail.mapWF, ?_, ?_, ?_, ?_, ?_⟩
        · intro name found hfind
          have hne : info.name ≠ name := by
            intro heq
            subst name
            rw [hfind] at hfresh
            contradiction
          exact Htail.preserves
            (addConstant_find_of_ne env (.inductInfo info) name hwf
              hfresh hne hfind)
        · intro name found hfind
          rcases Htail.origin hfind with hnext | ⟨tail, htail, hname, hfound⟩
          · rcases addConstant_find_cases env (.inductInfo info) name hwf
                hfresh hnext with hhead | hold
            · right
              exact ⟨info, by simp, hhead.1, hhead.2⟩
            · exact Or.inl hold
          · right
            exact ⟨tail, by simp [htail], hname, hfound⟩
        · have hinstalledHead := Htail.preserves
            (addConstant_find_self env (.inductInfo info) hwf hfresh)
          intro member hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact hinstalledHead
          · exact Htail.installed member htail
        · intro member hmember
          simp only [List.mem_cons] at hmember
          rcases hmember with rfl | htail
          · exact hfresh
          · have hnextFresh := Htail.sourceFresh member htail
            by_cases hsame : info.name = member.name
            · have hnextFind :
                  nextEnv.find? info.name = some (.inductInfo info) := by
                have hself :=
                  addConstant_find_self env (.inductInfo info) hwf hfresh
                change (Lean4Lean.AddInductive.addConstant env
                  (.inductInfo info)).find? info.name =
                    some (.inductInfo info) at hself
                simpa only [nextEnv] using hself
              rw [← hsame, hnextFind] at hnextFresh
              contradiction
            · by_contra hsource
              cases hsourceFind : env.find? member.name with
              | none => exact hsource hsourceFind
              | some found =>
                have hnextFind := addConstant_find_of_ne env
                  (.inductInfo info) member.name hwf hfresh hsame hsourceFind
                rw [hnextFind] at hnextFresh
                contradiction
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, Htail.namesNodup⟩
          intro hmemberName
          rcases List.mem_map.mp hmemberName with
            ⟨member, hmember, hname⟩
          have hnextFresh := Htail.sourceFresh member hmember
          have hnextFind :
              nextEnv.find? info.name = some (.inductInfo info) := by
            have hself :=
              addConstant_find_self env (.inductInfo info) hwf hfresh
            change (Lean4Lean.AddInductive.addConstant env
              (.inductInfo info)).find? info.name =
                some (.inductInfo info) at hself
            simpa only [nextEnv] using hself
          rw [hname, hnextFind] at hnextFresh
          contradiction

theorem InductiveMemberInfos.mapEnvironment
    (H : InductiveMemberInfos source names)
    (hpreserves : ∀ {name found}, source.find? name = some found →
      target.find? name = some found) :
    InductiveMemberInfos target names := by
  induction H with
  | nil => exact .nil
  | cons hlookup Htail ih => exact .cons (hpreserves hlookup) ih

private theorem inductiveMemberInfos_of_forall
    (infos : List InductiveVal)
    (hlookup : ∀ info ∈ infos,
      env.find? info.name = some (.inductInfo info)) :
    InductiveMemberInfos env (infos.map (fun info => info.name)) := by
  induction infos with
  | nil => exact .nil
  | cons info infos ih =>
    exact .cons (hlookup info (by simp))
      (ih fun member hmem => hlookup member (by simp [hmem]))

theorem InductiveInfosAdded.newMembers
    (H : InductiveInfosAdded source infos target) :
    InductiveMemberInfos target (infos.map (fun info => info.name)) :=
  inductiveMemberInfos_of_forall infos H.installed

/-- A lockstep installation consisting only of constructors, recursors, or
other non-inductive constants preserves closure of all mutual blocks. -/
theorem AddConstants.closesMutuals
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env)
    (hnind : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
      ∀ (value : InductiveVal),
      entry.1 ≠ ConstantInfo.inductInfo value) :
    MutualInductivesClosed outEnv := by
  induction H with
  | nil => exact hclosed
  | @cons venv ci ci' venv' rest outEnv outVEnv env hn _ _ _ _ _ Htail ih =>
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (env.add ci).constants.WF := by
      change (env.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    have hclosedNext : MutualInductivesClosed (env.add ci) := by
      change MutualInductivesClosed
        (Lean4Lean.AddInductive.addConstant env ci)
      exact hclosed.addNonInductive hwf hn
        (fun value => hnind (ci, ci') (by simp) value)
    exact ih hnextWF hclosedNext fun entry hentry value =>
      hnind entry (by simp [hentry]) value

theorem RecursorCheckingEnvironment.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : RecursorCheckingEnvironment H outEnv)
    (hclosed : MutualInductivesClosed headerEnv) :
    MutualInductivesClosed outEnv :=
  R.installed.closesMutuals H.context.checking.tr.map_wf hclosed
    R.nonInductive


theorem GeneratedRecursors.closesMutuals
    (H : GeneratedRecursors safety sourceEnv lparams elimLevel c stats
      indTypes recInfos entries)
    (Hinstalled : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (hclosed : MutualInductivesClosed env) :
    MutualInductivesClosed outEnv := by
  apply Hinstalled.closesMutuals hwf hclosed
  intro entry hmem inductiveValue
  rcases entry with ⟨info, value⟩
  exact H.nonInductive info value hmem inductiveValue

theorem InductiveInfosAdded.closesMutuals
    (H : InductiveInfosAdded source infos target)
    (hold : MutualInductivesClosed source)
    (huniform : ∀ info ∈ infos,
      info.all = infos.map (fun member => member.name))
    (hparams : ∀ info ∈ infos, info.numParams = numParams) :
    MutualInductivesClosed target := by
  intro targetName value hfind
  rcases H.origin hfind with holdLookup |
      ⟨info, hinfo, hname, hvalue⟩
  · have Hclosure := hold targetName value holdLookup
    exact ⟨Hclosure.members.mapEnvironment H.preserves, Hclosure.target,
      Hclosure.names, by
        intro member info hmember hfind
        have holdMember : source.find? member =
            some (.inductInfo info) := by
          rcases H.origin hfind with holdMember |
              ⟨newInfo, hnewInfo, hname, hfound⟩
          · exact holdMember
          · rcases Hclosure.members.find hmember with
              ⟨oldInfo, holdInfo⟩
            have hfresh := H.sourceFresh newInfo hnewInfo
            rw [← hname, holdInfo] at hfresh
            contradiction
        exact Hclosure.parameters member info hmember holdMember⟩
  · cases hvalue
    have hmembers := H.newMembers
    rw [← huniform value hinfo] at hmembers
    exact ⟨hmembers, by
      rw [hname]
      rw [huniform value hinfo]
      exact List.mem_map.mpr ⟨value, hinfo, rfl⟩, by
        rw [huniform value hinfo]
        exact H.namesNodup, by
          intro member memberInfo hmember hmemberLookup
          rw [huniform value hinfo] at hmember
          rcases List.mem_map.mp hmember with
            ⟨sourceMember, hsourceMember, hsourceName⟩
          have hsourceLookup := H.installed sourceMember hsourceMember
          rw [hsourceName, hmemberLookup] at hsourceLookup
          have hinfoEq : memberInfo = sourceMember :=
            ConstantInfo.inductInfo.inj (Option.some.inj hsourceLookup)
          subst memberInfo
          exact (hparams sourceMember hsourceMember).trans
            (hparams value hinfo).symm⟩

private theorem zipWith_left_projection
    (g : α → γ) {as : List α} {bs : List β}
    (hlength : bs.length = as.length) :
    List.zipWith (fun a _ => g a) as bs = as.map g := by
  induction as generalizing bs with
  | nil => simpa using hlength
  | cons a as ih =>
    cases bs with
    | nil => simp at hlength
    | cons b bs =>
      have hlength' : bs.length = as.length := by
        simp only [List.length_cons] at hlength
        omega
      simp [ih hlength']

theorem inductiveTypeInfos_uniformAll
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size) :
    ∀ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
      numNested isUnsafe lparams).toList,
      info.all =
        (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
          isUnsafe lparams).toList.map (fun member => member.name) := by
  intro info hinfo
  simp [AddInductive.inductiveTypeInfos, hsize] at hinfo ⊢
  have hall := List.property_of_mem_zipWith
    (fun (indType : InductiveType) (numIndices : Nat) =>
      show InductiveVal from {
        name := indType.name
        levelParams := lparams
        type := indType.type
        numParams := numParams
        numIndices := numIndices
        all := indTypes.toList.map (fun type => type.name)
        numNested := numNested
        isUnsafe := isUnsafe
        ctors := indType.ctors.map (fun ctor => ctor.name)
        isRec := AddInductive.isRec indTypes stats.indConsts
        isReflexive := AddInductive.isReflexive indTypes stats.indConsts })
    (fun generated =>
      generated.all = indTypes.toList.map (fun type => type.name))
    (by intro _a _b; rfl) hinfo
  have hlength : stats.nindices.toList.length = indTypes.toList.length := by
    simpa using hsize
  exact hall.trans (zipWith_left_projection
    (fun type : InductiveType => type.name) hlength).symm

/-- All headers emitted by one executable mutual-header batch carry the
same common-parameter count supplied to that batch. -/
theorem inductiveTypeInfos_uniformNumParams
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size) :
    ∀ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
      numNested isUnsafe lparams).toList,
      info.numParams = numParams := by
  intro info hinfo
  simp [AddInductive.inductiveTypeInfos, hsize] at hinfo ⊢
  exact List.property_of_mem_zipWith
    (fun (indType : InductiveType) (numIndices : Nat) =>
      show InductiveVal from {
        name := indType.name
        levelParams := lparams
        type := indType.type
        numParams := numParams
        numIndices := numIndices
        all := indTypes.toList.map (fun type => type.name)
        numNested := numNested
        isUnsafe := isUnsafe
        ctors := indType.ctors.map (fun ctor => ctor.name)
        isRec := AddInductive.isRec indTypes stats.indConsts
        isReflexive := AddInductive.isReflexive indTypes stats.indConsts })
    (fun generated => generated.numParams = numParams)
    (by intro _ _; rfl) hinfo

theorem inductiveTypeInfos_source_mem
    (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size)
    (howner : owner ∈ indTypes.toList) :
    ∃ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
        numNested isUnsafe lparams).toList,
      info.name = owner.name ∧
      info.ctors = owner.ctors.map (fun ctor => ctor.name) ∧
      info.all = indTypes.toList.map (fun type => type.name) := by
  rcases List.mem_iff_getElem.mp howner with ⟨i, hi, rfl⟩
  have hinfosSize :
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).size = indTypes.size := by
    simp [AddInductive.inductiveTypeInfos, hsize]
  let info := (AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe lparams)[i]'(by simpa [hinfosSize] using hi)
  refine ⟨info, ?_, ?_, ?_, ?_⟩
  · simpa [info] using Array.getElem_mem (xs :=
      AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams) (by simpa [hinfosSize] using hi)
  · simp [info, AddInductive.inductiveTypeInfos, hsize]
  · simp [info, AddInductive.inductiveTypeInfos, hsize]
  · simp [info, AddInductive.inductiveTypeInfos, hsize]

end VerifyInductive
end Lean4Lean
