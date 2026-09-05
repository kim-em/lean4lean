import Lean4Lean.Verify.Inductive.PrimitiveAtomicInstallation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two sound installation histories that can reach the completed
constructor boundary.  Ordinary declarations preserve validity after every
constant; primitive Bool/Nat declarations instead regain it only after the
whole header/constructor batch. -/
inductive CompletedFormationInstallation (safety : DefinitionSafety)
    (sourceEnv : Environment) (sourceVEnv : VEnv)
    (headerEntries : List (ConstantInfo × VConstVal))
    (headerEnv : Environment) (headerVEnv : VEnv)
    (ctorEntries : List (ConstantInfo × VConstVal))
    (ctorEnv : Environment) (ctorVEnv : VEnv) : Prop
  | ordinary :
    AddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv
  | primitive :
    AtomicAddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AtomicAddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    PrimitiveBootstrapInstallation sourceVEnv ctorVEnv
      (headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd) ->
    CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv

def CompletedFormationInstallation.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : CompletedFormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    CompletedFormationInstallation safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv := by
  cases H with
  | ordinary Hheaders Hctors =>
      exact .ordinary (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
  | primitive Hheaders Hctors Hbootstrap =>
      exact .primitive (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
        Hbootstrap

theorem CompletedFormationInstallation.headerLE
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv <= headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.le
  | primitive Htypes _ _ => exact Htypes.le

theorem CompletedFormationInstallation.constructorLE
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv <= ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.le
  | primitive _ Hctors _ => exact Hctors.le

theorem CompletedFormationInstallation.headerAbstract
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv.addConstVals (headerEntries.map Prod.snd) = some headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.abstract
  | primitive Htypes _ _ => exact Htypes.abstract

theorem CompletedFormationInstallation.constructorAbstract
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv.addConstVals (ctorEntries.map Prod.snd) = some ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.abstract
  | primitive _ Hctors _ => exact Hctors.abstract

/-- The complete formation endpoint always carries the local checker
invariant. In the primitive case the header-only prefix is used only as a
`CheckingEnv`, never as `CheckingEnv.Valid`. -/
theorem CompletedFormationInstallation.checking
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : CheckingEnv safety sourceEnv sourceVEnv) :
    CheckingEnv safety ctorEnv ctorVEnv := by
  cases H with
  | ordinary Htypes Hctors =>
      exact (AtomicAddConstants.ofAddConstants Hctors).checking
        ((AtomicAddConstants.ofAddConstants Htypes).checking Hsource)
  | primitive Htypes Hctors _ =>
      exact Hctors.checking (Htypes.checking Hsource)

theorem CompletedFormationInstallation.quotInit_eq
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    ctorEnv.quotInit = sourceEnv.quotInit := by
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq
  | primitive Htypes Hctors _ =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq

/-- Replay a complete formation prefix in a larger abstract environment.
Primitive headers and constructors are replayed with only `CheckingEnv`; the
primitive invariant is not asserted at the invalid header-only intermediate
state. -/
theorem CompletedFormationInstallation.rebase
    (H : CompletedFormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hvalid : CheckingEnv.Valid safety sourceEnv largerSource)
    (hsafety : safety <= checkSafety)
    (hsource : sourceVEnv <= largerSource) :
    exists largerHeader largerCtors,
      Nonempty (CompletedFormationInstallation safety sourceEnv largerSource
        headerEntries headerEnv largerHeader ctorEntries ctorEnv largerCtors) /\
      headerVEnv <= largerHeader /\ ctorVEnv <= largerCtors := by
  cases H with
  | ordinary Htypes Hctors =>
      rcases Htypes.rebase Hvalid hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.valid Hvalid) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.ordinary Htypes' Hctors'⟩, hheader, hctors⟩
  | primitive Htypes Hctors _Hbootstrap =>
      rcases Htypes.rebase Hvalid.tr hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.checking Hvalid.tr) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      have Hbootstrap' : PrimitiveBootstrapInstallation largerSource
          largerCtors
          (headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd) :=
        ⟨VEnv.addConstVals_append Htypes'.abstract Hctors'.abstract⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.primitive Htypes' Hctors' Hbootstrap'⟩, hheader, hctors⟩

theorem CompletedFormationInstallation.headerMapWF
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF) : headerEnv.constants.WF := by
  cases H with
  | ordinary Htypes _ => exact Htypes.targetMapWF hwf
  | primitive Htypes _ _ => exact Htypes.targetMapWF hwf

theorem CompletedFormationInstallation.constructorMapWF
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF) : ctorEnv.constants.WF := by
  have hheader := H.headerMapWF hwf
  cases H with
  | ordinary _ Hctors => exact Hctors.targetMapWF hheader
  | primitive _ Hctors _ => exact Hctors.targetMapWF hheader

/-- Every old production lookup survives either sound completed formation
history. -/
theorem CompletedFormationInstallation.preservesSourceFind
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : sourceEnv.find? name = some found) :
    ctorEnv.find? name = some found := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.preservesSourceFind hwf hfind)
  | primitive Htypes Hctors _ =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.preservesSourceFind hwf hfind)

/-- A retained header entry is visible at the completed constructor endpoint
for both ordinary and atomic primitive histories. -/
theorem CompletedFormationInstallation.findHeaderEntry
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hentry : (info, value) ∈ headerEntries) :
    ctorEnv.find? info.name = some info := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)
  | primitive Htypes Hctors _ =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)

/-- A retained constructor entry is visible at the completed constructor
endpoint for both installation histories. -/
theorem CompletedFormationInstallation.findConstructorEntry
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hentry : (info, value) ∈ ctorEntries) :
    ctorEnv.find? info.name = some info := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary _ Hctors => exact Hctors.findEntry hheaderWF hentry
  | primitive _ Hctors _ => exact Hctors.findEntry hheaderWF hentry

theorem CompletedFormationInstallation.constructorEntrySafety
    (H : CompletedFormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hentry : (info, value) ∈ ctorEntries) : safety ≤ info.safety := by
  cases H with
  | ordinary _ Hctors => exact Hctors.entrySafety hentry
  | primitive _ Hctors _ => exact Hctors.entrySafety hentry

/-- Stable input boundary for recursor generation.  It contains only facts
available after every constructor is installed and the final checking context
is valid.  No field requires a valid header-only context. -/
structure CompletedConstructorPhases (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool) (depth : Nat)
    (sourceEnv : VEnv) (indTypes : Array InductiveType)
    (ctorEnv : Environment) where
  headerEnv : Environment
  headerVEnv : VEnv
  headerEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  headerValues : headerEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceMaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  context : ContextWF { c with env := ctorEnv }
  headerMLCtx : TypeChecker.MLCtx
  contextMLCtx : context.mlctx = headerMLCtx
  headers : HeaderCertificate sourceEnv decl
  params : List VExpr
  headerParams : headers.params = params
  parameterScope : VLCtx
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    headerVEnv c.lparams headerMLCtx.vlctx stats decl depth
  materializedParams : materialized.headers.params = params
  materializedParameterScope : materialized.parameterScope = parameterScope
  checked : CheckedConstructorCertificate sourceEnv decl headerVEnv
    params
  parameterPrefixes : CheckedRecursorParameterPrefixes stats indTypes
  constructorTails : CheckedRecursorConstructorTails headerVEnv c.lparams
    parameterScope stats decl indTypes
  ownerNormalForms : CheckedConstructorOwnerNormalForms stats indTypes
  headerSourceAligned : exists numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList headerEntries
  constructorSourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList constructorEntries
  constructorProduction : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    exists info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  constructorNonInductive : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    forall value : InductiveVal,
      entry.1 ≠ ConstantInfo.inductInfo value
  installation : CompletedFormationInstallation c.safety c.env sourceEnv
    headerEntries headerEnv headerVEnv constructorEntries ctorEnv context.venv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl headerVEnv context.venv
  productionInductiveOrigins :
    ProductionInductiveOrigins c.env.constants ctorEnv.constants decl
  constructorSemantics : forall {safety},
    InductiveConstructorsSemanticallyCoherent safety c.env sourceEnv ->
    InductiveConstructorsSemanticallyCoherent safety ctorEnv context.venv

/-- The constructor-complete abstract environment admits the exact projection
prefix of this declaration as a genuine staged well-formed environment. -/
theorem CompletedConstructorPhases.projectedWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    (R.context.venv.addProjections decl.projectionEntries).WF := by
  let block : VInductBlock := {
    types := decl.typeConstants
    ctors := decl.constructorConstants
    recursors := []
    rules := []
    projections := decl.projectionEntries }
  apply VEnv.WF.inductProjections
      (base := sourceEnv) (envTypes := R.headerVEnv)
      (decl := decl) (block := block)
  · rw [← R.sourceContextVEnv]
    exact R.sourceContext.checking.tr.wf
  · exact R.context.checking.tr.wf
  · exact Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  · exact Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars R.core
  · rfl
  · rfl
  · rfl
  · exact R.core.typesAdded
  · exact R.core.ctorsAdded

/-- Projection registration changes neither the production environment nor
its constant interpretation; only the independently certified abstract
projection table is added. -/
def CompletedConstructorPhases.projectedChecking
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    CheckingEnv.Valid c.safety ctorEnv
      (R.context.venv.addProjections decl.projectionEntries) :=
  R.context.checking.addProjections R.projectedWF

/-- The exact header/constructor installation trace preserves the persistent
constructor-owner invariant.  New constructor metadata obtains its owner from
the family-major constructor trace, and that owner's header is found in the
matching generated-header trace. -/
theorem CompletedConstructorPhases.constructorOwnersPresent
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hsource : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent ctorEnv := by
  rcases R.headerSourceAligned with ⟨numNested, Hheaders⟩
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, R.materialized.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have Hformation : AtomicAddConstants c.safety c.env sourceEnv
      (R.headerEntries ++ R.constructorEntries) ctorEnv R.context.venv := by
    cases R.installation with
    | ordinary Htypes Hctors =>
        exact (AtomicAddConstants.ofAddConstants Htypes).append
          (AtomicAddConstants.ofAddConstants Hctors)
    | primitive Htypes Hctors _ => exact Htypes.append Hctors
  apply Hformation.constructorOwnersPresent
    R.sourceContext.checking.tr.map_wf hsource
  intro entry hentry info hinfo
  rcases List.mem_append.mp hentry with hheader | hctor
  · rcases Hheaders.originInfo hheader with ⟨familyInfo, _, heq⟩
    rw [heq] at hinfo
    cases hinfo
  · rcases R.constructorSourceAligned.ownerOfEntry hctor with
      ⟨owner, howner, installedInfo, hentryInfo, hownerName⟩
    have hinfoEq : info = installedInfo := by
      rw [hentryInfo] at hinfo
      exact ConstantInfo.ctorInfo.inj hinfo.symm
    subst info
    rcases inductiveTypeInfos_owner stats nparams indTypes numNested isUnsafe
        c.lparams hindicesSize howner with ⟨ownerInfo, hownerInfo, hname⟩
    rcases Hheaders.findInfo hownerInfo with ⟨value, hentry⟩
    refine ⟨ownerInfo, ?_⟩
    rw [hownerName, ← hname]
    exact R.installation.findHeaderEntry
      R.sourceContext.checking.tr.map_wf hentry

/-- Transport the retained header materialization to the final valid
constructor environment only when recursor checking begins. -/
def CompletedConstructorPhases.materializedFinal
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      R.context.venv c.lparams R.context.mlctx.vlctx stats decl depth := by
  let M := R.materialized.mono R.installation.constructorLE
  exact {
    headers := M.headers
    commonLevel := M.commonLevel
    levels := M.levels
    levelParams := M.levelParams
    uvars := M.uvars
    consts := M.consts
    indices := M.indices
    params := by simpa only [R.contextMLCtx] using M.params
    paramFVars := M.paramFVars
    parameterScope := M.parameterScope
    normalizedSources := M.normalizedSources
    normalizedShapes := M.normalizedShapes
    ambientScope := M.ambientScope
    scopeDecomposition := by
      simpa only [R.contextMLCtx] using M.scopeDecomposition
    ambientLength := M.ambientLength
    cachedScope := M.cachedScope
    runtimeScope := by simpa only [R.contextMLCtx] using M.runtimeScope
    paramsContext := M.paramsContext
    narrowParams := M.narrowParams }

theorem CompletedConstructorPhases.materializedFinal_parameterScope
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.materializedFinal.parameterScope = R.parameterScope := by
  simp [CompletedConstructorPhases.materializedFinal,
    checkInductiveTypes.loopInd.MaterializedHeaderResult.mono,
    R.materializedParameterScope]

/-- Embed the ordinary formation result into the completed constructor
boundary while retaining its staged installation traces. -/
def ConstructorPhasesResult.completed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H ctorEnv) :
    CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceMaterialized := H.sourceMaterialized
  context := R.declared.context
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  parameterScope := H.materialized.parameterScope
  materialized := H.materialized
  materializedParams := H.headerParams
  materializedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorProduction := R.declared.production
  constructorNonInductive := R.declared.nonInductive
  installation := by
    rw [R.declared.contextVEnv]
    exact .ordinary H.installed R.declared.installed
  formation := R.formation
  core := by
    rw [R.declared.contextVEnv]
    exact R.core
  productionInductiveOrigins := R.productionInductiveOrigins
  constructorSemantics := fun Hsource => by
    rw [R.declared.contextVEnv]
    exact R.constructorSemantics Hsource

/-- Transport the materialized header cache into the completed primitive
constructor context. -/
def PrimitiveConstructorPhasesResult.materialized
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorPhasesResult H ctorEnv) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      R.declared.context.venv c.lparams R.declared.context.mlctx.vlctx
      stats decl depth := by
  have henv : H.context.venv <= R.declared.context.venv := by
    rw [R.declared.contextVEnv]
    exact R.declared.installed.le
  let M := H.materialized.mono henv
  simpa only [R.declared.contextMLCtx] using M

/-- The atomic primitive formation pipeline embeds into the same completed
recursor boundary. -/
def PrimitiveConstructorPhasesResult.completed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorPhasesResult H ctorEnv) :
    CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceMaterialized := H.sourceMaterialized
  context := R.declared.context
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  parameterScope := H.materialized.parameterScope
  materialized := H.materialized
  materializedParams := H.headerParams
  materializedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorProduction := R.declared.production
  constructorNonInductive := R.declared.nonInductive
  installation := by
    rw [R.declared.contextVEnv]
    exact .primitive H.installed R.declared.installed (by
      simpa [H.values, R.declared.values] using R.declared.bootstrap)
  formation := R.formation
  core := by
    rw [R.declared.contextVEnv]
    exact R.core
  productionInductiveOrigins := R.productionInductiveOrigins
  constructorSemantics := fun Hsource => by
    rw [R.declared.contextVEnv]
    exact R.constructorSemantics Hsource

end VerifyInductive
end Lean4Lean
