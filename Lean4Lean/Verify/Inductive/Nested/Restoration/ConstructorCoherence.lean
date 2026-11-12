import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Nested.Lowering.Restore.ParameterOpening

/-! Closure of the installed mutual blocks, safety tags of the restored entries,
and coherence of the restored constructors' common parameters for a nested
run, all derived from the lowered run and the restoration folds.

The facts are stated over the rule-free `RestoredBlockBase`. The kernel family lookups
(`InductInfosFromDecl`) are a premise of `RestoredBlockBase.mutualInductivesClosed`, and the
installed abstract environment of `constructorTypingOfParameterDomains` is any extension of the
recursor stage. The installed-model facts are assembled in `RestoredBlock.kernelFacts` and
`installedFacts`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The kernel family lookups (`InductInfosFromDecl`) close the installed mutual
blocks once the restored source-family members are known to be present.  This
isolates the only
restoration-specific part of the closure argument from the generic lookup
reasoning. -/
theorem InductInfosFromDecl.mutualInductivesClosed
    {source target : Environment} {decl : VInductDecl}
    (H : InductInfosFromDecl source.constants target.constants decl)
    (hsourceWF : source.constants.WF) (htargetWF : target.constants.WF)
    (hsourceClosed : MutualInductivesClosed source)
    (hpreserves : ∀ {name found}, source.find? name = some found →
      target.find? name = some found)
    (hmembers : InductiveMemberInfos target
      (decl.types.map (fun type => type.name)))
    (hmemberParams : ∀ member info,
      member ∈ decl.types.map (fun type => type.name) →
      target.find? member = some (.inductInfo info) →
      info.numParams = decl.nparams)
    (hnames : (decl.types.map (fun type => type.name)).Nodup) :
    MutualInductivesClosed target := by
  intro familyName familyInfo hfamily
  have hfamilyMap : target.constants.find? familyName =
      some (.inductInfo familyInfo) := by
    rwa [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?] at hfamily
  rcases H familyName familyInfo hfamilyMap with hold | hnew
  · have holdEnv : source.find? familyName =
        some (.inductInfo familyInfo) := by
      change source.constants.find?' familyName =
        some (.inductInfo familyInfo)
      rw [hsourceWF.find?'_eq_find?]
      exact hold
    have Hclosed := hsourceClosed familyName familyInfo holdEnv
    exact ⟨Hclosed.members.mono hpreserves, Hclosed.target,
      Hclosed.names, by
        intro member info hmember hfind
        rcases Hclosed.members.find hmember with ⟨sourceInfo, hsourceInfo⟩
        have htargetInfo := hpreserves hsourceInfo
        rw [hfind] at htargetInfo
        have hinfo : info = sourceInfo :=
          ConstantInfo.inductInfo.inj (Option.some.inj htargetInfo)
        subst info
        exact Hclosed.parameters member sourceInfo hmember hsourceInfo⟩
  · rcases hnew with ⟨familyIdx, hfamilyName, ⟨A⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [A.all]
      exact hmembers
    · rw [A.all]
      exact List.mem_map.mpr ⟨decl.types[familyIdx]'A.familyIdx_lt,
        List.getElem_mem A.familyIdx_lt, (hfamilyName.trans A.name).symm⟩
    · rw [A.all]
      exact hnames
    · intro member info hmember hlookup
      rw [A.all] at hmember
      exact (hmemberParams member info hmember hlookup).trans A.numParams.symm

/-- Every source family restored by the outer fold is visible in the installed
kernel environment, in source order. -/
theorem FoldSteps.restoredSourceMemberInfos
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {ctorEnv loweredEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    {auxRec : NameMap Name} {remaining : List InductiveType}
    {stepSource targetEnv : Environment}
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining stepSource targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hsourceWF : stepSource.constants.WF) :
    InductiveMemberInfos targetEnv
        (remaining.map (fun type => type.name)) ∧
      (∀ member info, member ∈ remaining.map (fun type => type.name) →
        targetEnv.find? member = some (.inductInfo info) →
        info.numParams = sourceDecl.nparams) := by
  induction Htrace generalizing processed with
  | nil => exact ⟨.nil, by simp⟩
  | @cons head source middle tail target Hstep Htail ih =>
      let familyIdx := processed.length
      have hfamily : familyIdx < sourceTypes.length := by
        simp [familyIdx, hsplit]
      have hfamilyEq : sourceTypes[familyIdx] = head := by
        simp [familyIdx, hsplit]
      have hdecl : familyIdx < sourceDecl.types.length := by
        rw [← TrInductDeclCore.types_length Hsource]
        exact hfamily
      have Htype := TrInductDeclCore.typeAt Hsource familyIdx hfamily hdecl
      have Hstep' : RestoredInductiveStep result loweredEnv auxRec
          (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          source middle := by
        simpa only [hfamilyEq] using Hstep
      have Halign := Hstep'.inductInfoAlignmentAt Hlower Hc Hprod
        Hsource Hmetadata Hsources Harity Howners hempty familyIdx hfamily
        hsourceWF
      obtain ⟨headEntries, HheadFresh⟩ :=
        Hstep'.restored.freshExtension hsourceWF
      have hmiddleWF : middle.constants.WF :=
        HheadFresh.targetWF hsourceWF
      obtain ⟨tailEntries, HtailFresh⟩ :=
        Htail.inductiveFreshExtension hmiddleWF
      have hheadName : Hstep'.restored.header.newInfo.name = head.name := by
        calc
          Hstep'.restored.header.newInfo.name =
              sourceDecl.types[familyIdx].name := Halign.name
          _ = sourceTypes[familyIdx].name := Htype.header.name
          _ = head.name := congrArg InductiveType.name hfamilyEq
      have hheadMiddle : middle.find? head.name =
          some (.inductInfo Hstep'.restored.header.newInfo) := by
        rw [← hheadName, Lean.Kernel.Environment.find?,
          hmiddleWF.find?'_eq_find?]
        exact Halign.lookup
      have hheadTarget : target.find? head.name =
          some (.inductInfo Hstep'.restored.header.newInfo) :=
        HtailFresh.preservesSourceFind hmiddleWF hheadMiddle
      rcases ih
        (processed := processed ++ [head])
        (hsplit := by simpa [List.append_assoc] using hsplit)
        hmiddleWF with ⟨HtailMembers, HtailParams⟩
      refine ⟨.cons hheadTarget HtailMembers, ?_⟩
      intro member info hmember hmemberLookup
      simp only [List.map_cons, List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · subst member
        rw [hmemberLookup] at hheadTarget
        have hinfo : info = Hstep'.restored.header.newInfo :=
          ConstantInfo.inductInfo.inj (Option.some.inj hheadTarget)
        subst info
        exact Halign.numParams
      · exact HtailParams member info htail hmemberLookup

theorem sourceTypeNames
    (H : List.Forall₂ (TrInductiveType sourceEnv envTypes lparams)
      sourceTypes targetTypes) :
    sourceTypes.map (fun type => type.name) =
      targetTypes.map (fun type => type.name) := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [Hhead.header.name, ih]

/-! ## Parameter-domain coherence of restored constructors -/

/-- The semantic fact not contained in kernel or restoration metadata: the
independently translated source family and constructor expose
the requested number of leading binders, and those two binder contexts are
definitionally equal.  Residual bodies are intentionally unconstrained. -/
structure ConstructorParameterDomainsDefEq
    (venv : VEnv) (levelParams : List Name) (numParams : Nat)
    (familyTarget constructorTarget : VConstant) where
  familyDomains : List VExpr
  constructorDomains : List VExpr
  familyTail : VExpr
  constructorTail : VExpr
  familyTarget_defeq : venv.IsDefEqU levelParams.length [] familyTarget.type
    (VExpr.wrapForalls familyDomains familyTail)
  constructorTarget_eq : constructorTarget.type =
    VExpr.wrapForalls constructorDomains constructorTail
  familyLength : familyDomains.length = numParams
  constructorLength : constructorDomains.length = numParams
  parameterDomains : venv.IsDefEqCtx levelParams.length []
    familyDomains.reverse constructorDomains.reverse

/-- Parameter-domain coherence is persistent under abstract-environment
extension.  The level-parameter names themselves are irrelevant at this
boundary; only their cardinality indexes the definitional-equality judgment. -/
def ConstructorParameterDomainsDefEq.monoReindex
    (H : ConstructorParameterDomainsDefEq venv levelParams numParams
      familyTarget constructorTarget)
    (hle : venv ≤ targetEnv)
    (hlevels : levelParams.length = targetLevelParams.length)
    (hparams : numParams = targetNumParams) :
    ConstructorParameterDomainsDefEq targetEnv targetLevelParams
      targetNumParams familyTarget constructorTarget where
  familyDomains := H.familyDomains
  constructorDomains := H.constructorDomains
  familyTail := H.familyTail
  constructorTail := H.constructorTail
  familyTarget_defeq := by
    simpa only [hlevels] using H.familyTarget_defeq.mono hle
  constructorTarget_eq := H.constructorTarget_eq
  familyLength := H.familyLength.trans hparams
  constructorLength := H.constructorLength.trans hparams
  parameterDomains := by
    simpa only [hlevels] using H.parameterDomains.mono hle

/-- The pointwise semantic fact that remains after the restored source
translations have fixed every family and constructor target.  It is stated in
the source header environment, the earliest common environment in which both
translated parameter telescopes are available. -/
def NestedConstructorParameterDomainsDefEq
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockBase H sourceEnv decl lparams nparams
      isUnsafe safety) : Prop :=
  ∀ familyIdx (hfamily : familyIdx < decl.types.length)
    ctorIdx (hctor : ctorIdx < decl.types[familyIdx].ctors.length),
    Nonempty (ConstructorParameterDomainsDefEq C.install.venvCtors
      lparams nparams decl.types[familyIdx].toVConstVal.toVConstant
        decl.types[familyIdx].ctors[ctorIdx].toVConstant)

/-- Kernel alignment already contains the complete non-semantic
constructor metadata once the enclosing restored family alignment is fixed. -/
def ctorInfoAlignmentToCoherence
    (Hfamily : InductInfoAlignment prodEnv.constants decl familyIdx
      familyInfo)
    (Hctor : CtorInfoAlignment prodEnv.constants decl familyIdx ctorIdx
      familyInfo)
    (hprodWF : prodEnv.constants.WF) :
    CtorInfoCoherentAt prodEnv familyInfo.name familyInfo ctorIdx
      Hctor.familyInfo_ctorIdx_lt where
  info := Hctor.info
  lookup := by
    have hi := Hctor.familyInfo_ctorIdx_lt
    change prodEnv.constants.find?' (familyInfo.ctors[ctorIdx]'hi) =
      some (.ctorInfo Hctor.info)
    rw [hprodWF.find?'_eq_find?]
    exact Hctor.lookup
  induct := Hctor.induct
  cidx := Hctor.cidx
  numParams := Hctor.numParams.trans Hfamily.numParams.symm
  levelParams := Hctor.levelParamsExact
  isUnsafe := Hctor.isUnsafe.trans Hfamily.isUnsafe.symm

/-- Complete the coherence of one restored constructor from kernel metadata,
the restored abstract targets, and only their common-parameter
context conversion.  Choosing each target itself as its normal form makes
clear that no residual-body correspondence is being assumed here. -/
theorem CtorInfoAlignment.coherenceOfParameterDomains
    (Hfamily : InductInfoAlignment prodEnv.constants decl familyIdx
      familyInfo)
    (Hctor : CtorInfoAlignment prodEnv.constants decl familyIdx
      ctorIdx familyInfo)
    (hctorIdx : ctorIdx < familyInfo.ctors.length)
    (familyTarget constructorTarget : VConstant)
    (hfamilyLookup : venv.constants familyInfo.name = some familyTarget)
    (hconstructorLookup : venv.constants familyInfo.ctors[ctorIdx] =
      some constructorTarget)
    (hfamilyUvars : familyTarget.uvars = familyInfo.levelParams.length)
    (hconstructorUvars : constructorTarget.uvars =
      familyInfo.levelParams.length)
    (hfamilyWF : familyTarget.WF venv)
    (hconstructorWF : constructorTarget.WF venv)
    (henv : venv.WF)
    (hprodWF : prodEnv.constants.WF)
    (Hparams : ConstructorParameterDomainsDefEq venv
      familyInfo.levelParams familyInfo.numParams familyTarget
      constructorTarget) :
    Nonempty (ConstructorParameterAlignmentAt prodEnv venv
      familyInfo.name familyInfo ctorIdx Hctor.familyInfo_ctorIdx_lt) := by
  rcases hfamilyWF with ⟨familyLevel, HfamilyType⟩
  rcases hconstructorWF with ⟨constructorLevel, HconstructorType⟩
  exact ⟨{
    toCtorInfoCoherentAt :=
      ctorInfoAlignmentToCoherence Hfamily Hctor hprodWF
    familyTarget := familyTarget
    constructorTarget := constructorTarget
    familyLookup := hfamilyLookup
    constructorLookup := hconstructorLookup
    familyUvars := hfamilyUvars
    constructorUvars := hconstructorUvars
    familyNormalized :=
      VExpr.wrapForalls Hparams.familyDomains Hparams.familyTail
    constructorNormalized := constructorTarget.type
    familyDomains := Hparams.familyDomains
    constructorDomains := Hparams.constructorDomains
    familyTail := Hparams.familyTail
    constructorTail := Hparams.constructorTail
    familyType := .sort familyLevel
    constructorType := .sort constructorLevel
    familyDefEq := by
      have HfamilyType' : venv.HasType familyInfo.levelParams.length []
          familyTarget.type (.sort familyLevel) := by
        simpa only [hfamilyUvars] using HfamilyType
      have HfamilyDefEq := Hparams.familyTarget_defeq.of_l henv
        (by trivial) HfamilyType'
      exact HfamilyDefEq
    constructorDefEq := by
      change venv.IsDefEq constructorTarget.uvars [] constructorTarget.type
        constructorTarget.type (.sort constructorLevel) at HconstructorType
      simpa only [hconstructorUvars] using HconstructorType
    familyParams := by
      calc
        (VExpr.wrapForalls Hparams.familyDomains Hparams.familyTail).takeForalls
            familyInfo.numParams =
            (VExpr.wrapForalls Hparams.familyDomains
              Hparams.familyTail).takeForalls Hparams.familyDomains.length :=
          congrArg (fun n => (VExpr.wrapForalls Hparams.familyDomains
            Hparams.familyTail).takeForalls n) Hparams.familyLength.symm
        _ = some (Hparams.familyDomains, Hparams.familyTail) :=
          VExpr.takeForalls_wrapForalls _ _
    constructorParams := by
      rw [Hparams.constructorTarget_eq]
      calc
        (VExpr.wrapForalls Hparams.constructorDomains
            Hparams.constructorTail).takeForalls familyInfo.numParams =
            (VExpr.wrapForalls Hparams.constructorDomains
              Hparams.constructorTail).takeForalls
                Hparams.constructorDomains.length :=
          congrArg (fun n => (VExpr.wrapForalls Hparams.constructorDomains
            Hparams.constructorTail).takeForalls n)
              Hparams.constructorLength.symm
        _ = some (Hparams.constructorDomains, Hparams.constructorTail) :=
          VExpr.takeForalls_wrapForalls _ _
    parameterDomains := Hparams.parameterDomains }⟩

/-- Fold the pointwise restored parameter-context facts across all installed
inductive families.  Families already present in the source environment reuse
the source model.  Every newly restored family is identified by kernel
alignment; its remaining semantic fields come from the source translation
retained by the restored block certificate. -/
theorem RestoredBlockBase.constructorTypingOfParameterDomains
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {ves : VEnvs}
    (C : RestoredBlockBase H (ves.venv safety) decl lparams
      nparams isUnsafe safety)
    (wf : ves.WF sourceProdEnv)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      outEnv.constants decl)
    (Hparams : NestedConstructorParameterDomainsDefEq C)
    {installedVEnv : VEnv} (hinstalled : C.recursorVEnv ≤ installedVEnv) :
    ConstructorParameterAlignment safety outEnv installedVEnv := by
  have hsourceMapWF : sourceProdEnv.constants.WF :=
    (wf.tr (safety := safety)).map_wf
  obtain ⟨entries, Hfresh⟩ := H.freshExtension hsourceMapWF
  have houtMapWF : outEnv.constants.WF := Hfresh.targetWF hsourceMapWF
  have hctorsLE : C.install.venvCtors ≤ installedVEnv :=
    VEnv.addProjections_le.trans
      ((VEnv.addConstVals_le C.install.abstract_recursors).trans hinstalled)
  have htypesLE : C.install.venvTypes ≤ installedVEnv :=
    (VEnv.addConstVals_le C.constructorsAdded).trans hctorsLE
  have hsourceLE : ves.venv safety ≤ installedVEnv :=
    (VEnv.addConstVals_le C.typesAdded).trans htypesLE
  have Hsource : TrInductDeclCore (ves.venv safety) lparams nparams
      sourceTypes isUnsafe decl C.install.venvTypes
        C.install.venvCtors :=
    C.sourceTranslations.core C.typesSource C.uvars C.numParams C.unsafeEq
      C.typesAdded C.constructorsAdded
  intro familyName familyInfo hfamily hvisible ctorIdx hctorIdx
  have hfamilyMap : outEnv.constants.find? familyName =
      some (.inductInfo familyInfo) := by
    change outEnv.constants.find?' familyName = some (.inductInfo familyInfo)
      at hfamily
    rwa [houtMapWF.find?'_eq_find?] at hfamily
  rcases Horigins familyName familyInfo hfamilyMap with hold | hnew
  · rcases wf.constructorParameterAlignment familyName familyInfo (by
        change sourceProdEnv.constants.find?' familyName =
          some (.inductInfo familyInfo)
        rw [hsourceMapWF.find?'_eq_find?]
        exact hold) hvisible ctorIdx hctorIdx with ⟨Hctor⟩
    exact ⟨Hctor.rebaseKernel
      (Hfresh.preservesSourceFind hsourceMapWF Hctor.lookup) hsourceLE⟩
  · rcases hnew with ⟨familyIdx, rfl, ⟨Hfamily⟩⟩
    have hfamilyIdx := Hfamily.familyIdx_lt
    have hdeclCtor : ctorIdx <
        (decl.types[familyIdx]'hfamilyIdx).ctors.length := by
      rw [← Hfamily.constructors]
      exact hctorIdx
    rcases Hfamily.constructor ctorIdx hdeclCtor with ⟨Hctor⟩
    have hsourceFamily : familyIdx < sourceTypes.length := by
      rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
      exact Hfamily.familyIdx_lt
    have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
      familyIdx hsourceFamily Hfamily.familyIdx_lt
    have hsourceCtor : ctorIdx <
        (sourceTypes[familyIdx]'hsourceFamily).ctors.length := by
      rw [Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
      exact hdeclCtor
    have HsourceCtor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
      ctorIdx hsourceCtor hdeclCtor
    have hfamilyMember :
        (decl.types[familyIdx]'hfamilyIdx).toVConstVal ∈
        decl.typeConstants := by
      simp only [VInductDecl.typeConstants, List.mem_map]
      exact ⟨decl.types[familyIdx], List.getElem_mem hfamilyIdx, rfl⟩
    have hctorMember :
        (decl.types[familyIdx]'hfamilyIdx).ctors[ctorIdx]'hdeclCtor ∈
        decl.constructorConstants := by
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨decl.types[familyIdx], List.getElem_mem hfamilyIdx,
        List.getElem_mem hdeclCtor⟩
    have hfamilyLookup : C.install.venvCtors.constants familyInfo.name =
        some (decl.types[familyIdx]'hfamilyIdx).toVConstVal.toVConstant := by
      rw [Hfamily.name]
      exact (VEnv.addConstVals_le C.constructorsAdded).constants
        (VEnv.addConstVals_get C.typesAdded hfamilyMember)
    have hconstructorLookup :
        C.install.venvCtors.constants
            (familyInfo.ctors[ctorIdx]'hctorIdx) =
          some
            ((decl.types[familyIdx]'hfamilyIdx).ctors[ctorIdx]'hdeclCtor).toVConstant := by
      rw [Hctor.name]
      exact VEnv.addConstVals_get C.constructorsAdded hctorMember
    rcases Hparams familyIdx Hfamily.familyIdx_lt ctorIdx hdeclCtor with
      ⟨HparameterDomains⟩
    have HparameterDomains' := HparameterDomains.monoReindex VEnv.LE.rfl
      (by
        calc
          lparams.length = decl.uvars := C.uvars.symm
          _ = familyInfo.levelParams.length := Hfamily.levelParams.symm)
      (by
        calc
          nparams = decl.nparams := C.numParams.symm
          _ = familyInfo.numParams := Hfamily.numParams.symm)
    have hcanonicalWF : C.install.venvCtors.WF :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource
        (wf.tr (safety := safety)).wf
    exact ⟨(Classical.choice
      (Lean4Lean.VerifyInductive.CtorInfoAlignment.coherenceOfParameterDomains
      Hfamily Hctor hctorIdx
      (decl.types[familyIdx]'hfamilyIdx).toVConstVal.toVConstant
      ((decl.types[familyIdx]'hfamilyIdx).ctors[ctorIdx]'hdeclCtor).toVConstant
      hfamilyLookup hconstructorLookup
      (by
        calc
          (decl.types[familyIdx]'hfamilyIdx).toVConstVal.toVConstant.uvars =
              lparams.length := Htype.header.uvars
          _ = decl.uvars := C.uvars.symm
          _ = familyInfo.levelParams.length := Hfamily.levelParams.symm)
      (by
        calc
          ((decl.types[familyIdx]'hfamilyIdx).ctors[ctorIdx]'hdeclCtor).toVConstant.uvars =
              lparams.length := HsourceCtor.uvars
          _ = decl.uvars := C.uvars.symm
          _ = familyInfo.levelParams.length := Hfamily.levelParams.symm)
      (Htype.header.wf.mono
        ((VEnv.addConstVals_le C.typesAdded).trans
          (VEnv.addConstVals_le C.constructorsAdded)))
      (HsourceCtor.wf.mono (VEnv.addConstVals_le C.constructorsAdded))
      hcanonicalWF houtMapWF HparameterDomains')).mono hctorsLE⟩

end VerifyInductive
end Lean4Lean
