import Lean4Lean.Verify.Inductive.Recursor.Installation
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterRawShape

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Every abstract value in an ordinary lockstep installation has the same
non-primitive name as its production constant. -/
theorem AddConstants.valueNamesNonprimitive
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ name ∈ (entries.map Prod.snd).map VConstVal.name,
      ¬ Kernel.Environment.primitives.contains name := by
  induction H with
  | nil => simp
  | cons _hn hnprim htr _hwf _hadd _hdelta _Htail ih =>
    intro name hname
    simp only [List.map_cons, List.mem_cons] at hname
    rcases hname with hhead | htail
    · subst name
      simpa [htr.2] using hnprim
    · exact ih name htail

/-- A primitive lookup visible after an `AddConstants` fold predates the
fold, since every installed name is non-primitive. -/
theorem AddConstants.sourceContainsOfTargetContainsPrimitive
    (H : AddConstants safety env source entries outEnv target)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : target.contains name) : source.contains name := by
  rcases htarget with ⟨ci, hlookup⟩
  refine ⟨ci, ?_⟩
  rw [VEnv.addConstVals_constants_of_forall_ne H.abstract ?_] at hlookup
  · exact hlookup
  · intro value hvalue hname
    apply H.valueNamesNonprimitive value.name
      (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
    simpa [hname] using hprimitive

/-- Literal availability cannot be introduced by an ordinary non-primitive
constant fold: each name controlling literal support is reserved. -/
theorem AddConstants.sourceContainsLits
    (H : AddConstants safety env source entries outEnv target)
    (hlit : target.ContainsLits literal) : source.ContainsLits literal := by
  cases literal with
  | natVal n =>
      exact H.sourceContainsOfTargetContainsPrimitive (by native_decide) hlit
  | strVal s =>
      exact ⟨H.sourceContainsOfTargetContainsPrimitive (by native_decide)
          hlit.1,
        H.sourceContainsOfTargetContainsPrimitive (by native_decide) hlit.2⟩

/-- The environment-indexed literal condition is preserved by an ordinary
non-primitive constant installation. -/
theorem AddConstants.availableLiteralDisjoint
    (H : AddConstants safety prodEnv source entries outProd target)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint source indConsts) :
    checkPositivityStep.AvailableLiteralDisjoint target indConsts :=
  fun literal havailable => hlit literal (H.sourceContainsLits havailable)

theorem AddConstants.targetMapWF
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) : outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfresh : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    exact ih (hwf.insert ci.name ci hfresh)

theorem AddConstants.preservesSourceMapFind
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF)
    (hfind : env.constants.find? name = some found) :
    outEnv.constants.find? name = some found := by
  have hsource : env.find? name = some found := by
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind
  have htarget := H.preservesSourceFind hwf hsource
  rw [Lean.Kernel.Environment.find?,
    (H.targetMapWF hwf).find?'_eq_find?] at htarget
  exact htarget

theorem ProductionInductiveOrigins.addConstants
    {source middle target : Environment}
    (O : ProductionInductiveOrigins source.constants middle.constants decl)
    (H : AddConstants safety middle venv entries target outVEnv)
    (hwf : middle.constants.WF)
    (hnind : ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ ConstantInfo.inductInfo inductiveValue) :
    ProductionInductiveOrigins source.constants target.constants decl := by
  intro familyName familyInfo hfamily
  have htargetWF := H.targetMapWF hwf
  have hfamilyEnv : target.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?]
    exact hfamily
  rcases H.entryOrigin hwf hfamilyEnv with hold | hnew
  · have holdMap : middle.constants.find? familyName =
        some (.inductInfo familyInfo) := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hold
    rcases O familyName familyInfo holdMap with hsource | hcurrent
    · exact Or.inl hsource
    · rcases hcurrent with ⟨familyIdx, hname, ⟨A⟩⟩
      exact Or.inr ⟨familyIdx, hname, ⟨A.rebase
        (by simpa [← hname] using hfamily)
        (H.preservesSourceMapFind hwf)⟩⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    exact False.elim (hnind entry.1 entry.2 hentry familyInfo hinfo.symm)

/-- Non-circular result of mutual header declaration. It retains typed
headers, raw constructor correspondence, and the exact installed header
environment, but makes no constructor-WF claim. -/
structure DeclaredHeadersResult (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  production : ∃ numNested,
    entries.map Prod.fst =
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList.map (fun info => .inductInfo info)
  sourceAligned : ∃ numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList entries
  values : entries.map Prod.snd = decl.typeConstants
  context : ContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  translation : TrInductDeclHeaders sourceEnv c.lparams nparams
    indTypes.toList isUnsafe decl context.venv
  installed : AddConstants c.safety c.env sourceEnv entries outEnv context.venv
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceMaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : materialized.headers.params = headers.params
  parameterScopeEq : materialized.parameterScope =
    sourceMaterialized.parameterScope

/-- Header-only refinement of `declareInductiveTypes`. This is the executable
prefix used before any constructor has been checked. -/
theorem AddInductive.declareInductiveTypes.headersWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv
          indTypes outEnv, True := by
  rcases Hdecl with
    ⟨huvars, hnparams, hunsafe, htypesAdded, Htypes⟩
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Htranslated := AddInductive.inductiveTypeInfos.translated
    (numParams := numParams) (numNested := numNested)
    Htypes Hmaterialized.indices hvisible
  have Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal c.safety Hc.venv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF Hc.venv)
      infos.toList decl.typeConstants := by
    simpa [infos, VInductDecl.typeConstants] using Htranslated
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive)
    Hc.checking Hentries VEnv.LE.rfl htypesAdded (by
      simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    have hvalues :
        (List.zip
          (infos.toList.map (fun info => ConstantInfo.inductInfo info))
          decl.typeConstants).map Prod.snd = decl.typeConstants := by
      have hlength : infos.toList.length = decl.typeConstants.length :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries
      apply List.map_snd_zip
      simpa [hlength]
    refine ⟨{
      entries := List.zip
        (infos.toList.map (fun info => .inductInfo info)) decl.typeConstants
      production := by
        refine ⟨numNested, ?_⟩
        have hfst : (List.zip
            (infos.toList.map (fun info => ConstantInfo.inductInfo info))
            decl.typeConstants).map Prod.fst =
            infos.toList.map (fun info => ConstantInfo.inductInfo info) := by
          apply List.map_fst_zip
          have hlength :=
            Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries
          simpa using Nat.le_of_eq hlength
        simpa [infos] using hfst
      sourceAligned := ⟨numNested, by
        apply InductiveHeaderEntries.ofZip
        simpa using
          Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries⟩
      values := hvalues
      context := Hc.withEnv (Hinstalled.valid Hc.checking) Hinstalled.le
      headers := Hmaterialized.headers
      translation := ?_
      installed := Hinstalled
      sourceContext := Hc
      sourceContextVEnv := rfl
      sourceMaterialized := Hmaterialized
      materialized := Hmaterialized.mono Hinstalled.le
      headerParams := rfl
      parameterScopeEq := rfl }, trivial⟩
    exact {
      uvars := huvars
      nparams := hnparams
      isUnsafe := hunsafe
      typesAdded := htypesAdded
      types := Htypes }

/-- Verified boundary after installing all mutual type constants and before
checking any constructor. The executable and abstract environments are
aligned, while the original source-to-constructor translation already points
at this exact abstract header environment. -/
structure DeclaredTypesResult (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  context : ContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  typesInstalled : sourceEnv.addConstVals decl.typeConstants = some context.venv
  sourceTypes : List.Forall₂
    (TrInductiveType sourceEnv context.venv c.lparams)
    indTypes.toList decl.types
  installed : AddConstants c.safety c.env sourceEnv entries outEnv context.venv
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : materialized.headers.params = headers.params

def DeclaredHeadersResult.formation
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (Hchecked : CheckedConstructorsResult sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams
      H.materialized.parameterScope) :
    FormationCertificate sourceEnv decl where
  headers := H.headers
  envTypes := H.context.venv
  typesInstalled := H.translation.typesAdded
  constructorParameters := Hchecked.parameterShapes
    H.context.checking.tr.wf H.translation.types
    (H.materialized.runtimeScope.scopeWF H.context.checking.tr.wf)
    (checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      H.materialized).params_size
    H.materialized.uvars.symm (by
      rw [← H.headerParams]
      exact H.materialized.paramsContext)
  constructors := Hchecked.checked.formation

/-- Constructor checking consumes only the raw constructor translations
retained by header installation and returns both formation and pointwise
constructor typing.  In particular this boundary does not assume the source
constructor constants are already well-formed. -/
theorem AddInductive.checkConstructors.checkedWF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        CheckedConstructorsResult sourceEnv decl H.context.venv
          H.headers.params stats indTypes c.lparams
          H.materialized.parameterScope := by
  have Hloops := checkConstructors.loopTypes.refinesMaterialized
    H.context H.translation.types H.translation.typesAdded H.materialized
    H.headerParams hconsume hlit hproj hunsafe H.materialized.universeBound
  rw [AddInductive.checkConstructors]
  change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
    AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
      { c with env := outEnv }).WF _
  change (((liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } >>= fun _ =>
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
        { c with env := outEnv }).WF _)
  rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } = .ok outEnv from rfl]
  exact Hloops

/-- The same executable constructor check also retains the canonical owner
normal form for every constructor.  This proof is kept as an independent
projection so the abstract formation certificate does not depend on the
later recursor implementation. -/
theorem AddInductive.checkConstructors.ownerNormalFormsWF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        CheckedConstructorOwnerNormalForms stats indTypes := by
  let Hsuffix := H.materialized.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      H.materialized
  have Hloops := checkConstructors.loopTypes.ownerNormalFormsWF
    (Q := fun _ => CheckedConstructorOwnerNormalForms stats indTypes)
    (isUnsafe := isUnsafe)
    H.context H.translation.types
    (ConstructorOwnerNormalFormRows.empty stats indTypes)
    Hsuffix Hstats hconsume hlit hproj
    (fun Hrows => Hrows.complete)
  rw [AddInductive.checkConstructors]
  change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
    AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
      { c with env := outEnv }).WF _
  change (((liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } >>= fun _ =>
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
        { c with env := outEnv }).WF _)
  rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } = .ok outEnv from rfl]
  exact Hloops

theorem AddInductive.checkConstructors.headersWF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        Nonempty (FormationCertificate sourceEnv decl) :=
  (AddInductive.checkConstructors.checkedWF H hconsume hlit hproj
    hunsafe).mono fun _ Hchecked => ⟨H.formation Hchecked⟩

/-- Verified boundary after the concrete constructor-info fold.  It retains
the exact abstract constructor environment and the now-typed pointwise source
translation needed to join the header and constructor phases. -/
structure DeclaredConstructorsResult
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (outEnv : Environment) where
  venvCtors : VEnv
  entries : List (ConstantInfo × VConstVal)
  values : entries.map Prod.snd = decl.constructorConstants
  installed : AddConstants c.safety headerEnv H.context.venv entries
    outEnv venvCtors
  sourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList entries
  production : ∀ entry ∈ entries,
    ∃ info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  nonInductive : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
    ∀ (value : InductiveVal),
    entry.1 ≠ ConstantInfo.inductInfo value
  translation : TrInductDeclConstructors H.context.venv c.lparams
    indTypes.toList decl venvCtors
  context : ContextWF { c with env := outEnv }
  contextVEnv : context.venv = venvCtors
  contextMLCtx : context.mlctx = H.context.mlctx

theorem AddInductive.declareConstructors.WF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (Hchecked : CheckedConstructorCertificate sourceEnv decl H.context.venv
      H.headers.params)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    (AddInductive.declareConstructors stats indTypes isUnsafe
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : DeclaredConstructorsResult H outEnv, True := by
  let mkInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
  have Htranslated := Hchecked.translated H.translation
  have Hfold := AddConstants.ofConstructorTypes
    (allowPrimitive := c.allowPrimitive) mkInfo H.context.checking
    Htranslated VEnv.LE.rfl
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by
      intro owner i ctor
      simpa [mkInfo, AddInductive.constructorInfo] using hvisible)
    hnprim
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  change (indTypes.toList.foldlM (init := headerEnv) fun
      (env : Environment) (owner : InductiveType) => do
    let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
    pure env).WF _
  exact Hfold.mono fun outEnv Hout => by
    rcases Hout with
      ⟨venvCtors, entries, hvalues, Hinstalled, Haligned, hproduction,
        hnind⟩
    have hctorsAdded : H.context.venv.addConstVals decl.constructorConstants =
        some venvCtors := by
      simp only [VInductDecl.constructorConstants]
      rw [← hvalues]
      exact Hinstalled.abstract
    let Htranslation : TrInductDeclConstructors H.context.venv c.lparams
        indTypes.toList decl venvCtors := {
      ctorsAdded := hctorsAdded
      types := Htranslated }
    exact ⟨{
      venvCtors := venvCtors
      entries := entries
      values := by simpa [VInductDecl.constructorConstants] using hvalues
      installed := Hinstalled
      sourceAligned := by simpa [mkInfo] using Haligned
      production := hproduction
      nonInductive := hnind
      translation := Htranslation
      context := H.context.withEnv
        (Hinstalled.valid H.context.checking) Hinstalled.le
      contextVEnv := rfl
      contextMLCtx := rfl }, trivial⟩

structure ConstructorPhasesResult
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (outEnv : Environment) where
  checked : CheckedConstructorCertificate sourceEnv decl H.context.venv
    H.headers.params
  parameterPrefixes : CheckedRecursorParameterPrefixes stats indTypes
  constructorTails : CheckedRecursorConstructorTails H.context.venv c.lparams
    H.materialized.parameterScope stats decl indTypes
  ownerNormalForms : CheckedConstructorOwnerNormalForms stats indTypes
  declared : DeclaredConstructorsResult H outEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl H.context.venv declared.venvCtors

/-- The materialized header cache transported through both header and
constructor installation, in the exact context where recursor generation
starts. -/
def ConstructorPhasesResult.materialized
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      R.declared.context.venv c.lparams R.declared.context.mlctx.vlctx
      stats decl depth := by
  have henv : H.context.venv ≤ R.declared.context.venv := by
    rw [R.declared.contextVEnv]
    exact R.declared.installed.le
  let M := H.materialized.mono henv
  exact {
    headers := M.headers
    commonLevel := M.commonLevel
    levels := M.levels
    levelParams := M.levelParams
    uvars := M.uvars
    consts := M.consts
    indices := M.indices
    params := by
      simpa only [R.declared.contextMLCtx] using M.params
    paramFVars := M.paramFVars
    parameterScope := M.parameterScope
    normalizedSources := M.normalizedSources
    ambientScope := M.ambientScope
    scopeDecomposition := by
      simpa only [R.declared.contextMLCtx] using M.scopeDecomposition
    ambientLength := M.ambientLength
    cachedScope := M.cachedScope
    runtimeScope := by
      simpa only [R.declared.contextMLCtx] using M.runtimeScope
    paramsContext := M.paramsContext
    narrowParams := M.narrowParams }

/-- Select one newly installed production constructor by its source family
and owner-local index, and assemble its persistent semantic common-parameter
coherence witness.  This is the positional bridge between the executable
header/constructor folds and the independent formation specification. -/
theorem ConstructorPhasesResult.installedConstructorSemanticCoherenceAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ familyInfo : InductiveVal,
      ∃ hi : ctorIdx < familyInfo.ctors.length,
        familyInfo.name = indTypes[familyIdx].name ∧
        familyInfo.ctors = indTypes[familyIdx].ctors.map (fun ctor => ctor.name) ∧
        outEnv.find? familyInfo.name = some (.inductInfo familyInfo) ∧
        Nonempty (InductiveConstructorSemanticCoherenceAt
          outEnv R.declared.venvCtors familyInfo.name familyInfo ctorIdx hi) := by
  rcases H.sourceAligned with ⟨numNested, Haligned⟩
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, H.materialized.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have hinfosSize : infos.size = indTypes.size := by
    simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hinfoIdx : familyIdx < infos.size := by simpa [hinfosSize] using hfamily
  let familyInfo := infos[familyIdx]
  have hfamilyInfoMem : familyInfo ∈ infos.toList := by
    apply Array.mem_toList_iff.mpr
    simpa [familyInfo] using Array.getElem_mem hinfoIdx
  have hfamilyName : familyInfo.name = indTypes[familyIdx].name := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hfamilyCtors : familyInfo.ctors =
      indTypes[familyIdx].ctors.map (fun ctor => ctor.name) := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hi : ctorIdx < familyInfo.ctors.length := by
    simpa [hfamilyCtors] using hctor
  rcases Haligned.findInfo hfamilyInfoMem with ⟨familyValue, hfamilyEntry⟩
  have hfamilyHeader :
      headerEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    H.installed.findEntry H.sourceContext.checking.tr.map_wf hfamilyEntry
  have hfamilyLookup :
      outEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    R.declared.installed.preservesSourceFind H.context.checking.tr.map_wf
      hfamilyHeader
  let sourceFamily := indTypes[familyIdx]
  let sourceCtor := sourceFamily.ctors[ctorIdx]
  let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
    sourceFamily ctorIdx sourceCtor
  rcases R.declared.sourceAligned.findAt
      (owner := sourceFamily) (List.getElem_mem hfamily)
      ctorIdx hctor with ⟨ctorValue, hctorEntry⟩
  have hctorLookupExact :
      outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
    R.declared.installed.findEntry H.context.checking.tr.map_wf hctorEntry
  have hctorLookup :
      outEnv.find? familyInfo.ctors[ctorIdx] = some (.ctorInfo ctorInfo) := by
    simpa [ctorInfo, sourceCtor, sourceFamily, hfamilyCtors,
      AddInductive.constructorInfo] using hctorLookupExact
  have htargetFamily : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    familyIdx (by simpa using hfamily) htargetFamily
  have htargetCtor : ctorIdx < decl.types[familyIdx].ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    simpa [sourceFamily] using hctor
  have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx (by simpa [sourceFamily] using hctor) htargetCtor
  have hfamilyTargetLookup : R.declared.venvCtors.constants familyInfo.name =
      some decl.types[familyIdx].toVConstant := by
    have hlookup : H.context.venv.constants decl.types[familyIdx].name =
        some decl.types[familyIdx].toVConstant := by
      apply VEnv.addConstVals_get R.core.typesAdded
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem htargetFamily, rfl⟩
    simpa [hfamilyName, Htype.header.name] using
      (VEnv.addConstVals_le R.core.ctorsAdded).constants hlookup
  have hctorTargetLookup : R.declared.venvCtors.constants
      familyInfo.ctors[ctorIdx] =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
    have hlookup := VEnv.addConstVals_get R.core.ctorsAdded
      (ci := decl.types[familyIdx].ctors[ctorIdx]) (by
        simp only [VInductDecl.constructorConstants]
        apply List.mem_flatMap.mpr
        exact ⟨decl.types[familyIdx], List.getElem_mem htargetFamily,
          List.getElem_mem htargetCtor⟩)
    simpa [hfamilyCtors, sourceFamily, Hctor.name] using hlookup
  have hfinalWF : R.declared.venvCtors.WF := by
    rw [← R.declared.contextVEnv]
    exact R.declared.context.checking.tr.wf
  have hparamsSize : stats.params.size = decl.nparams := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      H.materialized.params
    simpa [VInductDecl.paramVars] using hlength
  let C : InductiveConstructorCoherenceAt outEnv familyInfo.name familyInfo
      ctorIdx hi := {
    info := ctorInfo
    lookup := hctorLookup
    induct := by
      simp [ctorInfo, sourceFamily, AddInductive.constructorInfo, hfamilyName]
    cidx := by simp [ctorInfo, AddInductive.constructorInfo]
    numParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo, hindicesSize, hparamsSize, R.core.nparams]
    levelParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo, hindicesSize]
    isUnsafe := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo, hindicesSize] }
  refine ⟨familyInfo, hi, hfamilyName, hfamilyCtors, hfamilyLookup, ?_⟩
  apply InductiveConstructorSemanticCoherenceAt.ofShapes C hfinalWF
    decl.types[familyIdx] decl.types[familyIdx].ctors[ctorIdx]
    hfamilyTargetLookup hctorTargetLookup
  · exact Htype.header.uvars.trans R.core.uvars.symm
  · exact Hctor.uvars.trans R.core.uvars.symm
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      hindicesSize, R.core.uvars]
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      hindicesSize, R.core.nparams]
  · exact H.headers.typeShapes _ (List.getElem_mem htargetFamily)
  · exact R.checked.formation.ctorShape
      (List.getElem_mem htargetFamily) (List.getElem_mem htargetCtor)
  · exact H.installed.le.trans R.declared.installed.le
  · exact R.declared.installed.le

/-- The executable header and constructor folds identify every newly visible
production inductive family with one exact source declaration position. -/
theorem ConstructorPhasesResult.productionInductiveOrigins
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv) :
    ProductionInductiveOrigins c.env.constants outEnv.constants decl := by
  intro familyName familyInfo hfamily
  have hsourceWF := H.sourceContext.checking.tr.map_wf
  have hheaderWF := H.context.checking.tr.map_wf
  have houtWF := R.declared.installed.targetMapWF hheaderWF
  have hfamilyEnv : outEnv.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
    exact hfamily
  rcases R.declared.installed.entryOrigin hheaderWF hfamilyEnv with
      hheader | hctorOrigin
  · rcases H.installed.entryOrigin hsourceWF hheader with hold | hnew
    · left
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hold
    · right
      rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.materialized.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              R.core).symm
          _ = indTypes.size := by simp
      have hparamsSize : stats.params.size = decl.nparams := by
        have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          H.materialized.params
        simpa [VInductDecl.paramVars] using hlength
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have htargetIdx : familyIdx < decl.types.length := by
        rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
        simpa using hfamilyIdx
      have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
        familyIdx (by simpa using hfamilyIdx) htargetIdx
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hfamilyNameEq : familyName = familyInfo.name := by
        have hentryFamilyName : entry.1.name = familyInfo.name := by
          have heq := congrArg ConstantInfo.name hentryValue
          dsimp only [ConstantInfo.name] at heq
          exact heq.symm
        exact hentryName.trans hentryFamilyName
      refine ⟨familyIdx, hfamilyNameEq, ⟨{
        familyIdx_lt := htargetIdx
        name := ?_
        lookup := by simpa [← hfamilyNameEq] using hfamily
        all := ?_
        levelParams := ?_
        numParams := ?_
        numIndices := ?_
        constructors := ?_
        isUnsafe := ?_
        constructor := ?_ }⟩⟩
      · calc
          familyInfo.name = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].name := Htype.header.name.symm
      · calc
          familyInfo.all = indTypes.toList.map (fun type => type.name) := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types.map (fun type => type.name) := by
            apply List.ext_getElem
            · simpa using
                Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
            · intro i hsource htarget
              simp only [List.getElem_map]
              exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
                i (by simpa using hsource) (by simpa using htarget)).header.name.symm
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.uvars]
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.nparams]
      · have hindex : stats.nindices[familyIdx]? =
            some decl.types[familyIdx].numIndices := by
          rw [← Array.getElem?_toList, H.materialized.indices]
          simp [htargetIdx]
        have hstats : familyIdx < stats.nindices.size := by
          simpa [hindicesSize] using hfamilyIdx
        have hindexExact : stats.nindices[familyIdx] =
            decl.types[familyIdx].numIndices := by
          rw [Array.getElem?_eq_getElem hstats] at hindex
          exact Option.some.inj hindex
        calc
          familyInfo.numIndices = stats.nindices[familyIdx] := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].numIndices := hindexExact
      · simpa [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos] using
          Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.isUnsafe]
      · intro ctorIdx htargetCtor
        have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
          have hbound := htargetCtor
          rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype] at hbound
          simpa using hbound
        have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
          ctorIdx hsourceCtor htargetCtor
        rcases R.installedConstructorSemanticCoherenceAt familyIdx hfamilyIdx
            ctorIdx hsourceCtor with
          ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
            hinstalledLookup, ⟨C⟩⟩
        have hsourceName : familyName = indTypes[familyIdx].name := by
          calc
            familyName = familyInfo.name := hfamilyNameEq
            _ = indTypes[familyIdx].name := by
              simp [hfamilyInfoExact, infos,
                AddInductive.inductiveTypeInfos]
        have hsameLookup : outEnv.find? familyName =
            some (.inductInfo installedInfo) := by
          simpa [hinstalledName, hsourceName] using hinstalledLookup
        have hinstalledEq : installedInfo = familyInfo := by
          rw [hfamilyEnv] at hsameLookup
          cases Option.some.inj hsameLookup
          rfl
        subst installedInfo
        have hctorLookup : outEnv.constants.find? familyInfo.ctors[ctorIdx] =
            some (.ctorInfo C.info) := by
          have hlookup := C.lookup
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          exact hlookup
        let sourceFamily := indTypes[familyIdx]
        let sourceCtor := sourceFamily.ctors[ctorIdx]
        let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
          sourceFamily ctorIdx sourceCtor
        rcases R.declared.sourceAligned.findAt
            (owner := sourceFamily) (List.getElem_mem hfamilyIdx)
            ctorIdx (by simpa [sourceFamily] using hsourceCtor) with
          ⟨ctorValue, hctorEntry⟩
        have hctorLookupExact :
            outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
          R.declared.installed.findEntry H.context.checking.tr.map_wf hctorEntry
        have hctorNameExact :
            familyInfo.ctors[ctorIdx] = ctorInfo.name := by
          simp [ctorInfo, sourceCtor, sourceFamily, hinstalledCtors,
            AddInductive.constructorInfo]
        have hctorLookupExact' :
            outEnv.constants.find? familyInfo.ctors[ctorIdx] =
              some (.ctorInfo ctorInfo) := by
          have hlookup := hctorLookupExact
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          simpa [hctorNameExact] using hlookup
        have hctorInfoExact : C.info = ctorInfo := by
          have heq : (ConstantInfo.ctorInfo C.info) = .ctorInfo ctorInfo := by
            exact Option.some.inj (hctorLookup.symm.trans hctorLookupExact')
          exact ConstantInfo.ctorInfo.inj heq
        exact ⟨{
          familyIdx_lt := htargetIdx
          ctorIdx_lt := htargetCtor
          familyInfo_ctorIdx_lt := hi
          info := C.info
          name := by
            calc
              familyInfo.ctors[ctorIdx] =
                  indTypes[familyIdx].ctors[ctorIdx].name := by
                simp [hinstalledCtors]
              _ = decl.types[familyIdx].ctors[ctorIdx].name :=
                Hctor.name.symm
          lookup := hctorLookup
          induct := by simpa [hfamilyNameEq] using C.induct
          cidx := C.cidx
          numParams := by
            calc
              C.info.numParams = familyInfo.numParams := C.numParams
              _ = decl.nparams := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.nparams]
          numFields := by
            rw [hctorInfoExact]
            calc
              ctorInfo.numFields =
                  AddInductive.constructorArity sourceCtor.type -
                    stats.params.size :=
                AddInductive.constructorInfo_numFields stats c.lparams
                  isUnsafe sourceFamily ctorIdx sourceCtor
              _ = AddInductive.constructorArity ctorInfo.type -
                    decl.nparams := by
                rw [hparamsSize]
                rfl
          levelParamsExact := C.levelParams
          levelParams := by
            calc
              C.info.levelParams.length = familyInfo.levelParams.length :=
                congrArg List.length C.levelParams
              _ = decl.uvars := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.uvars]
          isUnsafe := by
            calc
              C.info.isUnsafe = familyInfo.isUnsafe := C.isUnsafe
              _ = decl.isUnsafe := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.isUnsafe] }⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (R.declared.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- Header and constructor installation preserves the persistent invariant
for old families and supplies it positionally for every newly declared
family.  No name-based matching is used to construct the new witness; names
only identify the unique production lookup after installation. -/
theorem ConstructorPhasesResult.constructorSemantics
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      safety c.env sourceEnv) :
    InductiveConstructorsSemanticallyCoherent
      safety outEnv R.declared.venvCtors := by
  intro familyName familyInfo hfamily hvisible ctorIdx hctor
  rcases R.declared.installed.entryOrigin H.context.checking.tr.map_wf
      hfamily with hheader | hctorOrigin
  · rcases H.installed.entryOrigin H.sourceContext.checking.tr.map_wf
        hheader with hold | hnew
    · rcases Hsource familyName familyInfo hold hvisible ctorIdx hctor with ⟨C⟩
      have hctorHeader := H.installed.preservesSourceFind
        H.sourceContext.checking.tr.map_wf C.lookup
      have hctorFinal := R.declared.installed.preservesSourceFind
        H.context.checking.tr.map_wf hctorHeader
      exact ⟨C.rebaseProduction hctorFinal
        (H.installed.le.trans R.declared.installed.le)⟩
    · rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.materialized.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              R.core).symm
          _ = indTypes.size := by simp
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
        simpa [hfamilyInfoExact, infos, AddInductive.inductiveTypeInfos]
          using hctor
      rcases R.installedConstructorSemanticCoherenceAt familyIdx hfamilyIdx
          ctorIdx hsourceCtor with
        ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
          hinstalledLookup, ⟨C⟩⟩
      have hentryFamilyName : entry.1.name = familyInfo.name := by
        have heq := congrArg ConstantInfo.name hentryValue
        dsimp only [ConstantInfo.name] at heq
        exact heq.symm
      have hsourceName : familyName = indTypes[familyIdx].name := by
        calc
          familyName = entry.1.name := hentryName
          _ = familyInfo.name := hentryFamilyName
          _ = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
      have hfamilyNameEq : familyName = familyInfo.name := by
        exact hentryName.trans hentryFamilyName
      have hsameLookup : outEnv.find? familyName =
          some (.inductInfo installedInfo) := by
        simpa [hinstalledName, hsourceName] using hinstalledLookup
      have hinstalledEq : installedInfo = familyInfo := by
        rw [hfamily] at hsameLookup
        cases Option.some.inj hsameLookup
        rfl
      subst installedInfo
      rw [hfamilyNameEq]
      exact ⟨by simpa only [Subsingleton.elim hi hctor] using C⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (R.declared.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- Select the exact checked common-parameter tail for a production
constructor.  This is the concrete half of the constructor/recursor bridge;
the abstract formation half remains available through `R.checked`. -/
def ConstructorPhasesResult.checkedRecursorParameterPrefixAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ tail, RecursorParamPrefix stats 0
      indTypes[familyIdx].ctors[ctorIdx].type tail :=
  R.parameterPrefixes.replay familyIdx hfamily ctorIdx hctor

/-- Select the exact translated constructor tail and the independent
positivity/formation certificate produced by constructor checking. -/
def ConstructorPhasesResult.checkedRecursorConstructorTailAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    CheckedConstructorTailReplayAt H.context.venv c.lparams
      H.materialized.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] :=
  R.constructorTails.replay familyIdx hfamily ctorIdx hctor

/-- The checked constructor replay supplies a typed application of the
installed constructor to all common parameters in the independently retained
recursor parameter scope. -/
theorem ConstructorPhasesResult.checkedConstructorPrefixSeedAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    let Hbase := R.declared.context
    let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
    let Hmaterialized := R.materialized
    let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
    ∃ ctorVal tail tailTarget introTarget,
      ctorVal ∈ (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily)).ctors ∧
      ctorVal.name = indTypes[familyIdx].ctors[ctorIdx].name ∧
      RecursorParamPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls tail tailTarget ∧
      Rbase.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx tailTarget ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      introTarget = VExpr.mkApps
        (.const indTypes[familyIdx].ctors[ctorIdx].name
          (recursorDeclarationAbstractLevels c.lparams Helim))
        (recursorCanonicalVars stats.params.size) ∧
      Rbase.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx introTarget tailTarget ∧
      Nonempty
        (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Rbase.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams)
          (recursorConstructorTelescopeTarget ctorVal Helim)
          Hsuffix.parameterDecls tailTarget stats.params.size 0) := by
  let Hbase := R.declared.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.materialized
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  have hheaderLE : H.context.venv ≤ Hbase.venv := by
    change H.context.venv ≤ R.declared.context.venv
    rw [R.declared.contextVEnv]
    exact R.declared.installed.le
  have Hreplay := R.checkedRecursorConstructorTailAt
    familyIdx hfamily ctorIdx hctor
  have Hreplay' : CheckedConstructorTailReplayAt H.context.venv c.lparams
      Hmaterialized.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] := by
    have hscope : Hmaterialized.parameterScope =
        H.materialized.parameterScope := by
      simp [Hmaterialized, ConstructorPhasesResult.materialized,
        checkInductiveTypes.loopInd.MaterializedHeaderResult.mono]
    rw [hscope]
    exact Hreplay
  have Hrebased := Hreplay'.toRecursorContext
    Hmaterialized hheaderLE Helim
  change ∃ ctorVal tail tailTarget introTarget, _
  rcases Hrebased with
    ⟨ctorVal, tail, tailTarget, hctorMem, hctorName, hctorUvars,
      Hprefix, Htail, HtailType, ⟨Hsynthesis⟩⟩
  have hfamilyDecl : familyIdx < decl.types.length := by
    rw [← R.constructorTails.size_eq]
    exact hfamily
  have hctorConstantMem : ctorVal ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[familyIdx], List.getElem_mem hfamilyDecl, hctorMem⟩
  have hctorWFHeader : ctorVal.toVConstant.WF H.context.venv :=
    by
      simpa [VConstant.WF, hctorUvars, H.materialized.uvars] using
        R.checked.types ctorVal hctorConstantMem
  have hctorWF : ctorVal.toVConstant.WF Rbase.venv := by
    simpa [Rbase, Hbase] using hctorWFHeader.mono hheaderLE
  have hctorLookup : Rbase.venv.constants ctorVal.name =
      some ctorVal.toVConstant := by
    have hlookup : Hbase.venv.constants ctorVal.name =
        some ctorVal.toVConstant := by
      change R.declared.context.venv.constants ctorVal.name =
        some ctorVal.toVConstant
      rw [R.declared.contextVEnv]
      apply VEnv.addConstVals_get R.declared.translation.ctorsAdded
      exact hctorConstantMem
    simpa [Rbase] using hlookup
  let levels := recursorDeclarationAbstractLevels c.lparams Helim
  have hlevelsWF : ∀ level ∈ levels,
      level.WF (AddInductive.getRecLevelParams
        elimLevel c.lparams).length :=
    recursorDeclarationAbstractLevels_wf Helim
  have hlevelsLength : levels.length = ctorVal.uvars := by
    rw [recursorDeclarationAbstractLevels_length Helim, hctorUvars]
  have hsourceLevelsLength : stats.levels.length = ctorVal.uvars := by
    calc
      stats.levels.length = decl.uvars := Hmaterialized.levels
      _ = c.lparams.length := Hmaterialized.uvars.symm
      _ = ctorVal.uvars := hctorUvars.symm
  have htargetType : ctorVal.type.instL levels =
      (recursorConstructorTelescopeTarget ctorVal Helim).type :=
    VConstVal.type_instL_recursorDeclarationAbstractLevels
      hctorWF hctorUvars Helim
  have HintroType := Hsynthesis.canonicalApplication Rbase.checking.tr.wf
    hctorLookup hlevelsWF hlevelsLength htargetType
  have Hhead : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (.const ctorVal.name stats.levels) (.const ctorVal.name levels) := by
    exact TrExprS.const hctorLookup
      (Hmaterialized.recursorLevelTranslation hlparams Helim)
      hsourceLevelsLength
  have hcanonical :
      checkInductiveTypes.loopType.cachedParamVars stats.params.size 0 =
        recursorCanonicalVars Hsynthesis.params.length := by
    rw [checkInductiveTypes.loopType.cachedParamVars_zero_eq_recursorCanonicalVars,
      Hsynthesis.parameterCount]
  have Hargs : List.Forall₂
      (TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls)
      stats.params.toList
      (recursorCanonicalVars Hsynthesis.params.length) := by
    rw [← hcanonical]
    exact Hsuffix.narrowParams
  have Hintro : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (Expr.mkAppList (.const ctorVal.name stats.levels)
        stats.params.toList)
      (VExpr.mkApps (.const ctorVal.name levels)
        (recursorCanonicalVars Hsynthesis.params.length)) :=
    checkPositivityStep.TrExprS.mkAppList Rbase.checking.tr.wf.ordered
      Hsynthesis.scopeWF.toCtx Hhead Hargs ⟨tailTarget, HintroType⟩
  refine ⟨ctorVal, tail, tailTarget,
    VExpr.mkApps (.const ctorVal.name levels)
      (recursorCanonicalVars Hsynthesis.params.length),
    hctorMem, hctorName, Hprefix, Htail, HtailType, ?_, ?_, HintroType,
    ⟨Hsynthesis⟩⟩
  · simpa [Expr.mkAppN_eq_mkAppList, hctorName, Rbase, Hbase,
      Hmaterialized, Hsuffix] using Hintro
  · simp [levels, hctorName, Hsynthesis.parameterCount]

/-- Reinterpret a checked constructor seed in any later recursor context
whose parameter suffix is the one retained by the first pass. -/
theorem ConstructorPhasesResult.checkedConstructorRuntimeSeedAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    {current : AddInductive.Context}
    (Rcurrent : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henvCurrent : Rcurrent.venv = R.declared.context.venv)
    {runtimeDepth : Nat}
    (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
      runtimeDepth)
    (hparameterDecls : HsuffixCurrent.parameterDecls =
      (R.materialized.parameterSuffix.toRecursorContext
        Helim).parameterDecls)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ tail tailTarget introTarget,
      RecursorParamPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      Nonempty (CheckedConstructorOwnerNormalForm stats familyIdx tail) ∧
      tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx tail tailTarget ∧
      Rcurrent.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      Rcurrent.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget := by
  let Hbase := R.declared.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let HsuffixBase := R.materialized.parameterSuffix.toRecursorContext Helim
  rcases R.checkedConstructorPrefixSeedAt Helim hlparams familyIdx hfamily
      ctorIdx hctor with
    ⟨_ctorVal, tail, tailNarrow, introNarrow, _hmem, _hname,
      Hprefix, Htail, HtailType, Hintro, _HintroShape,
      HintroType, _Hsynthesis⟩
  rcases R.ownerNormalForms.replay familyIdx hfamily ctorIdx hctor with
    ⟨normalTail, HnormalPrefix, Hnormal⟩
  have htailEq : normalTail = tail :=
    HnormalPrefix.tail_eq Hprefix
  subst normalTail
  have HtailCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls tail tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Htail
  have HtailTypeCurrent : Rcurrent.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HtailType
  have HtailParams : tail.FVarsIn
      (· ∈ ExprArrayFVarIds stats.params) := by
    exact HtailCurrent.fvarsIn.mono fun fv hfv => by
      rw [HsuffixCurrent.parameterDecls_fvars] at hfv
      simpa using hfv
  have HintroCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls
      (mkAppN
        (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
        stats.params) introNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Hintro
  have HintroTypeCurrent : Rcurrent.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx introNarrow tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HintroType
  rcases HsuffixCurrent.runtimeScope.transportTypedTerm
      Rcurrent.checking.tr.wf HintroCurrent HtailCurrent
      HintroTypeCurrent HtailTypeCurrent with
    ⟨introTarget, tailTarget, HintroRuntime, HtailRuntime,
      HintroTypeRuntime, HtailTypeRuntime⟩
  exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailParams,
    HtailRuntime, HtailTypeRuntime, HintroRuntime, HintroTypeRuntime⟩

/-- Select one mutual-family header for recursor replay after transporting
both its source translation and the materialized header certificate through
header and constructor installation. -/
def ConstructorPhasesResult.checkedRecursorHeaderAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (hlparams : c.lparams.Nodup) :
    mkRecInfos.loopArgs1.CheckedRecursorHeaderAt R.declared.context stats
      decl depth indTypes[familyIdx] familyIdx := by
  have htarget : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    familyIdx (by simpa using hfamily) htarget
  have hsourceLE : sourceEnv ≤ R.declared.venvCtors :=
    H.installed.le.trans R.declared.installed.le
  have Hsource := Htype.header.mono hsourceLE
  refine {
    target := decl.types[familyIdx]
    targetAt := by simp [htarget]
    materialized := ?_
    sourceTranslation := ?_
    targetLookup := ?_
    lparamsNodup := hlparams }
  · exact R.materialized
  · rw [R.declared.contextVEnv]
    simpa using Hsource
  · have hheaderLookup : H.context.venv.constants
        decl.types[familyIdx].name =
        some decl.types[familyIdx].toVConstant := by
      apply VEnv.addConstVals_get H.installed.abstract
      rw [H.values]
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem htarget, rfl⟩
    rw [R.declared.contextVEnv]
    exact R.declared.installed.le.constants hheaderLookup

/-- Enter the independently verified first mutual recursor pass from the
constructor-phase result.  The continuation receives the complete structural
state together with recursor-universe translations of every accumulated
index, major, and motive origin type. -/
theorem ConstructorPhasesResult.loopInd1SemanticWF
    {alpha : Type} {Q : alpha → Prop}
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (Hk : ∀ {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams))
      (henvOut : Rout.venv = R.declared.context.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut : HsuffixOut.parameterDecls =
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth)
      (Hbindings : RecInfoBindings cOut recInfos)
      (Horigins : RecInfoTypeOrigins cOut recInfos),
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes →
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes →
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes →
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel →
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoOuterOrder Rout Hparams Hbindings →
      RecInfoArities stats recInfos →
      RecInfoMinorsEmpty recInfos →
      RecInfoBlueprintCounts recInfos →
      BindingContextLE { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut →
      recInfos.size = indTypes.size →
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] k
      { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  let Hbase := R.declared.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.materialized
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  let HstatsOrdinary :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader Hmaterialized
  let Hstats := HstatsOrdinary.toRecursorContext Helim
  let Hheaders : ∀ i (hi : i < indTypes.size),
      mkRecInfos.loopArgs1.CheckedRecursorHeaderAt Hbase stats decl depth
        indTypes[i] i := fun i hi =>
    R.checkedRecursorHeaderAt i hi hlparams
  have HparamsCtx : ∀ i (hi : i < indTypes.size),
      VEnv.IsDefEqCtx Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        ((Hheaders i hi).recursorParams Helim).reverse
        Hsuffix.parameterDecls.toCtx := by
    intro i hi
    have hmaterialized : (Hheaders i hi).materialized = Hmaterialized := by
      rfl
    change VEnv.IsDefEqCtx Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      ((Hheaders i hi).recursorParams Helim).reverse
      (Hmaterialized.parameterSuffix.toRecursorContext
        Helim).parameterDecls.toCtx
    rw [← hmaterialized]
    exact (Hheaders i hi).recursorParamsContext Helim
  let HparamsHeader : BoundFVarArray { c with env := headerEnv }
      stats.params := H.materialized.parameterSuffix.paramsBound
  let Hparams : BoundFVarArray { c with
      env := outEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } stats.params :=
    HparamsHeader.monoFVars (by intro fv; exact id)
  have hparamsNodup : Hparams.fvars.Nodup := by
    change HparamsHeader.fvars.Nodup
    change (ExprArrayFVarIds stats.params).Nodup
    exact H.materialized.parameterSuffix.paramsBound_nodup
  refine mkRecInfos.loopInd1.resultSemantics Hbase stats indTypes elimLevel
    Helim Hheaders hconsume 0 #[] k Rbase (by simp [Rbase, Hbase])
    Hsuffix HparamsCtx
    Hstats (RecInfoBindings.empty _) (RecInfoTypeOrigins.empty _)
    (RecursorTranslatedOriginTypes.empty Rbase)
    (RecInfoMajorTypeShapes.empty stats)
    (RecursorTranslatedOriginTypes.empty Rbase)
    (RecInfoMotiveTypeShapes.empty _ elimLevel)
    (RecInfoMotiveTelescopes.empty Rbase stats decl
      Hsuffix.parameterDecls.toCtx elimLevel)
    (RecursorTranslatedOriginTypeRows.empty Rbase) Hparams
    (RecInfoBindings.empty_noAlias _ Hparams hparamsNodup)
    (RecInfoOuterOrder.empty Hsuffix Hparams)
    (BindingContextLE.rebaseTypeCheckerLParams
      (BindingContextLE.refl { c with env := outEnv })
      c.typeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams))
    rfl (RecInfoArities.empty stats)
    RecInfoMinorsEmpty.empty RecInfoBlueprintCounts.empty ?_
  intro cOut outDepth recInfos Rout henvOut HsuffixOut hparameterDeclsOut
    HstatsOut
    Hbindings Horigins HmajorTypes HmajorShapes HmotiveTypes HmotiveShapes
    Htelescopes HindexRows HparamsOut HnoAlias Horder Harities Hempty
    Hblueprints Hroot hsize
  have Hroot' : BindingContextLE { c with
      env := outEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } cOut := by
    simpa using Hroot.rebaseTypeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams)
      cOut.typeCheckerLParams
  apply Hk recInfos Rout henvOut HsuffixOut hparameterDeclsOut HstatsOut
    Hbindings Horigins
    HmajorTypes HmajorShapes HmotiveTypes HmotiveShapes (by
      simpa [hparameterDeclsOut] using Htelescopes) HindexRows HparamsOut
    HnoAlias Horder Harities Hempty Hblueprints Hroot'
  simpa using hsize

/-- The verified header cache supplies the exact retained parameter binders
needed by recursor-info generation, while the constructor phases supply its
independent declaration/cardinality input. -/
theorem ConstructorPhasesResult.mkRecInfosWF
    {alpha : Type} {Q : alpha → Prop}
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      R.declared.context.venv stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (Hk : ∀ {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.declared.context.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls =
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls →
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (Hbindings : RecInfoBindings cOut recInfos) →
      (Horigins : RecInfoTypeOrigins cOut recInfos) →
      RecInfoRuleBlueprintOrigins stats recInfos Horigins →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins →
      RecInfoMinorSourceAlignment stats indTypes Horigins →
      RecInfoMinorSemanticAlignment Rout Horigins
        HsuffixOut.parameterDecls →
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes →
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes →
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes →
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel →
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoOuterOrder Rout Hparams Hbindings →
      RecInfoArities stats recInfos →
      (∀ i, i < recInfos.size →
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) →
      RecursorCardinalityCertificate stats recInfos decl →
      BindingContextLE { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut →
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k
      { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  unfold AddInductive.mkRecInfos
  refine R.loopInd1SemanticWF elimLevel Helim hlparams hconsume
    (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) ?_
  intro cFrames frameDepth recInfos Rframes henvFrames HsuffixFrames
    hparameterDeclsFrames HstatsFrames HbindingsFrames HoriginsFrames
    HmajorTypesFrames HmajorShapesFrames HmotiveTypesFrames
    HmotiveShapesFrames HtelescopesFrames HindexRowsFrames HparamsFrames
    HnoAliasFrames HorderFrames HaritiesFrames HemptyFrames
    HblueprintCountsFrames HrootFrames hsizeFrames
  have hrecordsFrames : recInfos.size = stats.indConsts.size := by
    calc
      recInfos.size = indTypes.size := hsizeFrames
      _ = indTypes.toList.length := by simp
      _ = decl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = stats.indConsts.size := HstatsFrames.types_size.symm
  refine mkRecInfos.loopInd2.resultSemantics (root := { c with
      env := outEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams })
    (Q := Q) stats indTypes 0 recInfos k Rframes HsuffixFrames
    HstatsFrames hconsume
      (by simpa only [henvFrames] using hlit)
    (checkInductiveTypes.loopType.MLCtxOnlyLams.noIndConsts
      Rframes.onlyLams) hproj
    HbindingsFrames HoriginsFrames
    (RecInfoRuleBlueprintOrigins.ofEmpty HoriginsFrames HemptyFrames
      HblueprintCountsFrames)
    (RecInfoRuleBlueprintSemanticOrigins.ofEmpty Rframes decl HoriginsFrames
      HemptyFrames HblueprintCountsFrames elimLevel)
    (RecInfoMinorSourceAlignment.ofEmpty HoriginsFrames HemptyFrames)
    (RecInfoMinorSemanticAlignment.ofEmpty
      (parameterDecls := HsuffixFrames.parameterDecls)
      Rframes HoriginsFrames HemptyFrames)
    HmajorTypesFrames HmajorShapesFrames
    HmotiveTypesFrames HmotiveShapesFrames HtelescopesFrames
    HindexRowsFrames HparamsFrames HnoAliasFrames HorderFrames HrootFrames
    hsizeFrames
    hrecordsFrames HaritiesFrames ?_ ?_ ?_ ?_
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
      hparameterDeclsCurrent familyIdx hfamily ctor hctor
    rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
    rcases R.checkedConstructorRuntimeSeedAt elimLevel Helim hlparams
        Rcurrent (henvCurrent.trans henvFrames) HsuffixCurrent
        (hparameterDeclsCurrent.trans hparameterDeclsFrames) familyIdx
        hfamily ctorIdx hctorIdx with
      ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
        Htail, HtailType, Hintro, HintroType⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars, Htail,
      HtailType, Hintro, HintroType⟩
  · intro cOut outDepth out Rout henvOut HsuffixOut hparameterDeclsOut
      HstatsOut hctxOut HbindingsOut HoriginsOut HblueprintsOut
      HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut houtSize houtCounts
      HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
      HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
      HaritiesOut HrootOut
    exact Hk out Rout (henvOut.trans henvFrames) HsuffixOut
      (hparameterDeclsOut.trans hparameterDeclsFrames) HstatsOut
      hctxOut HbindingsOut HoriginsOut HblueprintsOut HblueprintSemanticsOut HminorSourcesOut
      HminorSemanticsOut
      HmajorTypesOut HmajorShapesOut
      HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
      HparamsOut HnoAliasOut HorderOut HaritiesOut houtCounts
      (RecursorCardinalityCertificate.ofResult R.core H.materialized
        houtSize houtCounts HaritiesOut)
      HrootOut

/-- Exact `run` prefix immediately after constructor installation.  The
eliminator-level search is semantically relevant only through the level it
returns; `mkRecInfosWF` validates every successful choice uniformly. -/
theorem ConstructorPhasesResult.getElimLevelMkRecInfosWF
    {alpha : Type} {Q : alpha → Prop}
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      R.declared.context.venv stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (k : Level → Bool → Array AddInductive.RecInfo → AddInductive.M alpha)
    (Hk : ∀ elimLevel,
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) →
      ∀ kTarget,
      ∀ {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.declared.context.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls =
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls →
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (Hbindings : RecInfoBindings cOut recInfos) →
      (Horigins : RecInfoTypeOrigins cOut recInfos) →
      RecInfoRuleBlueprintOrigins stats recInfos Horigins →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins →
      RecInfoMinorSourceAlignment stats indTypes Horigins →
      RecInfoMinorSemanticAlignment Rout Horigins
        HsuffixOut.parameterDecls →
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes →
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes →
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes →
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl
        (R.materialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel →
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoOuterOrder Rout Hparams Hbindings →
      RecInfoArities stats recInfos →
      (∀ i, i < recInfos.size →
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) →
      RecursorCardinalityCertificate stats recInfos decl →
      BindingContextLE { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut →
      (k elimLevel kTarget recInfos cOut).WF Q) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel
          (k elimLevel kTarget)) { c with env := outEnv }).WF Q := by
  have Helim := AddInductive.getElimLevel.WF stats indTypes
    { c with env := outEnv }
  exact Helim.bind fun elimLevel hElim => by
    simp only [AddInductive.withTypeCheckerLParams, withReader,
      MonadWithReaderOf.withReader]
    exact (show (AddInductive.isKTarget stats indTypes
      { c with
        env := outEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF
        fun _ => True from fun _ _ => trivial).bind fun kTarget _ =>
      R.mkRecInfosWF elimLevel hElim hlparams hconsume hlit hproj
        (k elimLevel kTarget) (Hk elimLevel hElim kTarget)

/-- The executable constructor check and declaration folds jointly establish
the independent formation judgment and the complete pointwise source/core
translation. -/
theorem AddInductive.constructorPhases.WF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : ConstructorPhasesResult H outEnv, True := by
  have Hcheck := AddInductive.checkConstructors.checkedWF H hconsume
    hlit hproj hunsafe
  have Howners := AddInductive.checkConstructors.ownerNormalFormsWF H
    hconsume hlit hproj
  have HcheckBoth :
      (AddInductive.checkConstructors indTypes stats isUnsafe
        { c with env := headerEnv }).WF fun _ =>
          CheckedConstructorsResult sourceEnv decl H.context.venv
              H.headers.params stats indTypes c.lparams
              H.materialized.parameterScope ∧
            CheckedConstructorOwnerNormalForms stats indTypes := by
    intro out hout
    exact ⟨Hcheck out hout, Howners out hout⟩
  exact HcheckBoth.bind fun _ HcheckedBoth =>
    let Hchecked := HcheckedBoth.1
    let HownerNormalForms := HcheckedBoth.2
    (AddInductive.declareConstructors.WF H Hchecked.checked hvisible hnprim).mono
      fun outEnv Hdeclared => by
        rcases Hdeclared with ⟨Hdeclared, _⟩
        exact ⟨{
          checked := Hchecked.checked
          parameterPrefixes := Hchecked.parameterPrefixes
          constructorTails := Hchecked.constructorTails
          ownerNormalForms := HownerNormalForms
          declared := Hdeclared
          formation := H.formation Hchecked
          core := Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases
            H.translation Hdeclared.translation }, trivial⟩

/-- Header installation, constructor checking, and constructor installation
in the exact production order.  The result is the first executable prefix
that exposes both `FormationCertificate` and `TrInductDeclCore` without
assuming either one. -/
theorem AddInductive.formationCore.headersWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hc.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ headerEnv : Environment,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ _ : ConstructorPhasesResult Hheaders outEnv, True := by
  have Htypes := AddInductive.declareInductiveTypes.headersWF Hc Hdecl
    Hmaterialized hvisible hnprimTypes
  exact Htypes.bind fun headerEnv Hresult => by
    rcases Hresult with ⟨Hheaders, _⟩
    have Hphases := AddInductive.constructorPhases.WF Hheaders
      hconsume (Hheaders.installed.availableLiteralDisjoint hlit) hproj
      hunsafe hvisible hnprimCtors
    exact Hphases.mono fun outEnv Hresult => by
      rcases Hresult with ⟨Hphases, _⟩
      exact ⟨headerEnv, Hheaders, Hphases, trivial⟩

/-- Non-circular formation prefix: header installation starts from the raw
phase translation and constructor checking itself supplies the formation
certificate. -/
theorem AddInductive.formationPrefix.headersWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hc.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun outEnv =>
        AddInductive.withEnv outEnv
          (AddInductive.checkConstructors indTypes stats isUnsafe)) c).WF
      fun _ => Nonempty (FormationCertificate Hc.venv decl) := by
  have Htypes := AddInductive.declareInductiveTypes.headersWF Hc Hdecl
    Hmaterialized hvisible hnprim
  exact Htypes.bind fun outEnv hresult => by
    rcases hresult with ⟨Hstaged, _⟩
    have Hconstructors := AddInductive.checkConstructors.headersWF Hstaged
      hconsume (Hstaged.installed.availableLiteralDisjoint hlit) hproj hunsafe
    exact Hconstructors

/-- End-to-end refinement of `declareInductiveTypes`: a successful executable
fold installs precisely the independently specified mutual headers and
transports the materialized header certificate into that environment. -/
theorem AddInductive.declareInductiveTypes.WF
    {envTypes envCtors : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclCore Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : DeclaredTypesResult c stats decl depth Hc.venv
          indTypes outEnv, True := by
  rcases Hdecl with
    ⟨huvars, hnparams, hunsafe, htypesAdded, hctorsAdded, Htypes⟩
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Htranslated := AddInductive.inductiveTypeInfos.translated
    (numParams := numParams) (numNested := numNested)
    (Lean4Lean.List.Forall₂.imp
      (fun _ _ h =>
        Lean4Lean.VerifyInductive.TrInductiveType.headers h) Htypes)
    Hmaterialized.indices hvisible
  have Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal c.safety Hc.venv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF Hc.venv)
      infos.toList decl.typeConstants := by
    simpa [infos, VInductDecl.typeConstants] using Htranslated
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive)
    Hc.checking Hentries VEnv.LE.rfl htypesAdded (by
      simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    refine ⟨{
      entries := List.zip
        (infos.toList.map (fun info => .inductInfo info)) decl.typeConstants
      context := Hc.withEnv (Hinstalled.valid Hc.checking) Hinstalled.le
      headers := Hmaterialized.headers
      typesInstalled := htypesAdded
      sourceTypes := Htypes
      installed := Hinstalled
      materialized := Hmaterialized.mono Hinstalled.le
      headerParams := rfl }, trivial⟩

def DeclaredTypesResult.formation
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (Hchecked : CheckedConstructorsResult sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams
      H.materialized.parameterScope) :
    FormationCertificate sourceEnv decl where
  headers := H.headers
  envTypes := H.context.venv
  typesInstalled := H.typesInstalled
  constructorParameters := Hchecked.parameterShapes
    H.context.checking.tr.wf
    (Lean4Lean.List.Forall₂.imp
      (fun _ _ h => Lean4Lean.VerifyInductive.TrInductiveType.headers h)
      H.sourceTypes)
    (H.materialized.runtimeScope.scopeWF H.context.checking.tr.wf)
    (checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      H.materialized).params_size
    H.materialized.uvars.symm (by
      rw [← H.headerParams]
      exact H.materialized.paramsContext)
  constructors := Hchecked.checked.formation

theorem AddInductive.checkConstructors.WF
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        Nonempty (FormationCertificate sourceEnv decl) := by
  have Hheaders : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv H.context.venv c.lparams)
      indTypes.toList decl.types :=
    Lean4Lean.List.Forall₂.imp
      (fun _ _ h => Lean4Lean.VerifyInductive.TrInductiveType.headers h)
      H.sourceTypes
  have Hloops := checkConstructors.loopTypes.refinesMaterialized
    H.context Hheaders H.typesInstalled H.materialized H.headerParams
    hconsume hlit hproj hunsafe H.materialized.universeBound
  rw [AddInductive.checkConstructors]
  change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
    AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
      { c with env := outEnv }).WF _
  change (((liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } >>= fun _ =>
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
        { c with env := outEnv }).WF _)
  rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } = .ok outEnv from rfl]
  exact Hloops.mono fun _ Hchecked => ⟨H.formation Hchecked⟩

/-- The exact executable prefix used by `AddInductive.run`, through mutual
header installation and constructor checking, refines `FormationWF`. -/
theorem AddInductive.formationPrefix.WF
    {envTypes envCtors : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclCore Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hc.venv stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun outEnv =>
        AddInductive.withEnv outEnv
          (AddInductive.checkConstructors indTypes stats isUnsafe)) c).WF
      fun _ => Nonempty (FormationCertificate Hc.venv decl) := by
  exact AddInductive.formationPrefix.headersWF Hc
    (Lean4Lean.VerifyInductive.TrInductDeclCore.headers Hdecl)
    Hmaterialized hvisible hnprim hconsume hlit hproj hunsafe

/-- Three-stage installation certificate matching the executable order:
mutual headers, constructors, then recursors. Reduction equations are not
included here because their validity depends on the independent iota schema. -/
structure StagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  typesAdded : AddConstants safety env venv types envTypes venvTypes
  ctorsAdded : AddConstants safety envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors outEnv outVEnv

def StagedBlock.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : StagedBlock checkSafety env venv types ctors recursors
      outEnv outVEnv) :
    StagedBlock safety env venv types ctors recursors outEnv outVEnv where
  envTypes := H.envTypes
  venvTypes := H.venvTypes
  envCtors := H.envCtors
  venvCtors := H.venvCtors
  typesAdded := H.typesAdded.sf_mono hsafety
  ctorsAdded := H.ctorsAdded.sf_mono hsafety
  recursorsAdded := H.recursorsAdded.sf_mono hsafety

/-- Reinterpret a replayed three-stage installation using the translations
of its original stronger-safety certificate. -/
def StagedBlock.reindex
    (H : StagedBlock checkSafety prodEnv base types ctors recursors
      outEnv outBase)
    (Hlarger : StagedBlock targetSafety prodEnv largerBase types ctors
      recursors outEnv largerOut)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    StagedBlock safety prodEnv largerBase types ctors recursors
      outEnv largerOut := by
  have henvTypes : H.envTypes = Hlarger.envTypes :=
    H.typesAdded.prod_eq Hlarger.typesAdded
  let Htypes : AddConstants checkSafety prodEnv base types
      Hlarger.envTypes H.venvTypes := henvTypes ▸ H.typesAdded
  let HctorsBase : AddConstants checkSafety Hlarger.envTypes H.venvTypes ctors
      H.envCtors H.venvCtors := henvTypes ▸ H.ctorsAdded
  have henvCtors : H.envCtors = Hlarger.envCtors :=
    HctorsBase.prod_eq Hlarger.ctorsAdded
  let Hctors : AddConstants checkSafety Hlarger.envTypes H.venvTypes ctors
      Hlarger.envCtors H.venvCtors := henvCtors ▸ HctorsBase
  let Hrecursors : AddConstants checkSafety Hlarger.envCtors H.venvCtors
      recursors outEnv outBase := henvCtors ▸ H.recursorsAdded
  have htypes : H.venvTypes ≤ Hlarger.venvTypes :=
    VEnv.addConstVals_mono hbase H.typesAdded.abstract
      Hlarger.typesAdded.abstract
  have hctors : H.venvCtors ≤ Hlarger.venvCtors :=
    VEnv.addConstVals_mono htypes H.ctorsAdded.abstract
      Hlarger.ctorsAdded.abstract
  exact {
    envTypes := Hlarger.envTypes
    venvTypes := Hlarger.venvTypes
    envCtors := Hlarger.envCtors
    venvCtors := Hlarger.venvCtors
    typesAdded := Htypes.reindex Hlarger.typesAdded hsafety hbase
    ctorsAdded := Hctors.reindex Hlarger.ctorsAdded hsafety htypes
    recursorsAdded := Hrecursors.reindex Hlarger.recursorsAdded
      hsafety hctors }

@[simp] theorem StagedBlock.reindex_venvTypes
    (H : StagedBlock checkSafety prodEnv base types ctors recursors
      outEnv outBase)
    (Hlarger : StagedBlock targetSafety prodEnv largerBase types ctors
      recursors outEnv largerOut)
    (hsafety : safety ≤ checkSafety) (hbase : base ≤ largerBase) :
    (H.reindex Hlarger hsafety hbase).venvTypes = Hlarger.venvTypes := by
  rfl

@[simp] theorem StagedBlock.reindex_venvCtors
    (H : StagedBlock checkSafety prodEnv base types ctors recursors
      outEnv outBase)
    (Hlarger : StagedBlock targetSafety prodEnv largerBase types ctors
      recursors outEnv largerOut)
    (hsafety : safety ≤ checkSafety) (hbase : base ≤ largerBase) :
    (H.reindex Hlarger hsafety hbase).venvCtors = Hlarger.venvCtors := by
  rfl

theorem StagedBlock.valid
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid (H.ctorsAdded.valid (H.typesAdded.valid hvalid))

theorem StagedBlock.abstract_types
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    venv.addConstVals (types.map Prod.snd) = some H.venvTypes :=
  H.typesAdded.abstract

theorem StagedBlock.abstract_ctors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvTypes.addConstVals (ctors.map Prod.snd) = some H.venvCtors :=
  H.ctorsAdded.abstract

theorem StagedBlock.abstract_recursors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvCtors.addConstVals (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- Collapse the executable header/constructor/recursor staging into the
single lockstep installation trace needed by facts that concern the complete
lowered production environment.  The staged form remains canonical for
typing, because each family of constants has a different abstract source
environment. -/
theorem StagedBlock.combined
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    AddConstants safety env venv (types ++ ctors ++ recursors)
      outEnv outVEnv :=
  by
    simpa [List.append_assoc] using
      H.typesAdded.append (H.ctorsAdded.append H.recursorsAdded)

theorem StagedBlock.aligned
    (H : StagedBlock checkSafety env venv types ctors recursors
      outEnv outVEnv)
    (Halign : Aligned checkSafety env.constants venv) :
    Aligned checkSafety outEnv.constants outVEnv :=
  H.recursorsAdded.aligned
    (H.ctorsAdded.aligned (H.typesAdded.aligned Halign))

theorem StagedBlock.trEnvIgnore
    (H : StagedBlock checkSafety prodEnv venv types ctors recursors
      outEnv outVEnv)
    (htypes : ∀ entry ∈ types, ¬ observerSafety ≤ entry.1.safety)
    (hctors : ∀ entry ∈ ctors, ¬ observerSafety ≤ entry.1.safety)
    (hrecursors : ∀ entry ∈ recursors,
      ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv :=
  H.recursorsAdded.trEnvIgnore hrecursors
    (H.ctorsAdded.trEnvIgnore hctors
      (H.typesAdded.trEnvIgnore htypes htr))

theorem StagedBlock.quotInit_eq
    (H : StagedBlock safety prodEnv venv types ctors recursors
      outEnv outVEnv) :
    outEnv.quotInit = prodEnv.quotInit :=
  H.recursorsAdded.quotInit_eq.trans
    (H.ctorsAdded.quotInit_eq.trans H.typesAdded.quotInit_eq)

theorem StagedBlock.deltaConservative
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (Halign : Aligned safety env.constants venv) :
    ∀ {name ci}, outEnv.constants.find? name = some ci →
      ci.deltaValue?.isSome → env.constants.find? name = some ci := by
  have HalignTypes := H.typesAdded.aligned Halign
  have HalignCtors := H.ctorsAdded.aligned HalignTypes
  intro name ci hfind hdelta
  exact H.typesAdded.deltaConservative Halign
    (H.ctorsAdded.deltaConservative HalignTypes
      (H.recursorsAdded.deltaConservative HalignCtors hfind hdelta)
      hdelta)
    hdelta

/-- The complete semantic certificate for the block assembled by the three
executable installation stages. `AddConstants` records the per-step checking
environment; the three `*WF` fields deliberately record the stronger
stage-wide facts required by the independent `VInductBlock.WF` specification.
This distinction matters for mutual declarations: typing a later header only
after installing an earlier sibling would not establish formation of the
mutual block. -/
structure BlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  staged : StagedBlock safety env venv types ctors recursors outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF staged.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF staged.venvCtors
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def BlockCertificate.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : BlockCertificate checkSafety env venv types ctors recursors
      rules outEnv outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  staged := H.staged.sf_mono hsafety
  typesWF := H.typesWF
  ctorsWF := H.ctorsWF
  recursorsWF := H.recursorsWF
  rulesWF := H.rulesWF

/-- A replayed block inherits every observer-safety interpretation carried
by its original certificate. -/
def BlockCertificate.reindex
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hlarger : BlockCertificate targetSafety prodEnv largerBase types ctors
      recursors rules outEnv largerOut)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    BlockCertificate safety prodEnv largerBase types ctors recursors
      rules outEnv largerOut := by
  have htypes : H.staged.venvTypes ≤ Hlarger.staged.venvTypes :=
    VEnv.addConstVals_mono hbase H.staged.typesAdded.abstract
      Hlarger.staged.typesAdded.abstract
  have hctors : H.staged.venvCtors ≤ Hlarger.staged.venvCtors :=
    VEnv.addConstVals_mono htypes H.staged.ctorsAdded.abstract
      Hlarger.staged.ctorsAdded.abstract
  have hout : outBase ≤ largerOut :=
    VEnv.addConstVals_mono hctors H.staged.recursorsAdded.abstract
      Hlarger.staged.recursorsAdded.abstract
  exact {
    staged := H.staged.reindex Hlarger.staged hsafety hbase
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := by
      intro ci hci
      change ci.toVConstant.WF Hlarger.staged.venvTypes
      exact (H.ctorsWF ci hci).mono htypes
    recursorsWF := by
      intro ci hci
      change ci.toVConstant.WF Hlarger.staged.venvCtors
      exact (H.recursorsWF ci hci).mono hctors
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hout }

/-- Generated recursor traversal discharges the recursor-typing field of the
semantic block certificate in the exact pre-recursor environment recorded by
the staging invariant. -/
def GeneratedRecursors.toBlockCertificate
    (staged : StagedBlock safety env venv types ctors recursors
      outEnv outVEnv)
    (H : GeneratedRecursors safety staged.venvCtors lparams elimLevel c stats
      indTypes recInfos recursors)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (htypes : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv)
    (hctors : ∀ ci ∈ ctors.map Prod.snd,
      ci.toVConstant.WF staged.venvTypes)
    (hrules : ∀ df ∈ rules, df.WF outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  staged := staged
  typesWF := htypes
  ctorsWF := hctors
  recursorsWF := H.recursorsWF Hc Hbindings Hparams
  rulesWF := hrules

def BlockCertificate.block
    (_H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules

/-- A completed executable staging certificate directly discharges the
independent semantic well-formedness judgment. -/
theorem BlockCertificate.wf
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.staged.venvTypes, H.staged.venvCtors, outVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors, H.typesWF, H.ctorsWF, H.recursorsWF,
    H.rulesWF⟩

/-- The abstract installation result is fixed by the executable staging
certificate; reduction rules are installed only after every recursor. -/
theorem BlockCertificate.install
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some (outVEnv.addDefEqRules rules) := by
  simp [BlockCertificate.block, VInductBlock.install,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors]

theorem BlockCertificate.names
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    List.Nodup
      ((H.block.types ++ H.block.ctors ++ H.block.recursors).map (·.name)) := by
  have hall : venv.addConstVals
      (types.map Prod.snd ++ ctors.map Prod.snd ++ recursors.map Prod.snd) =
      some outVEnv :=
    VEnv.addConstVals_append
      (VEnv.addConstVals_append H.staged.abstract_types
        H.staged.abstract_ctors)
      H.staged.abstract_recursors
  simpa [BlockCertificate.block, List.map_append] using
    VEnv.addConstVals_names_nodup hall

theorem BlockCertificate.hasPrimitives
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hprimitives : venv.HasPrimitives) :
    (outVEnv.addDefEqRules rules).HasPrimitives :=
  hasPrimitives_addDefEqs (H.staged.recursorsAdded.hasPrimitives
    (H.staged.ctorsAdded.hasPrimitives
      (H.staged.typesAdded.hasPrimitives Hprimitives))) rules

/-- Replay all three executable installation stages in a larger abstract
environment, retaining a complete block certificate rather than only its
abstract endpoint.  The production environments and generated entries stay
fixed; only their safety-indexed abstract interpretation changes. -/
theorem BlockCertificate.rebaseCertificate
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    ∃ largerOutBase,
      Nonempty (BlockCertificate safety prodEnv largerBase types ctors
        recursors rules outEnv largerOutBase) ∧
      outBase ≤ largerOutBase := by
  rcases H.staged.typesAdded.rebase Hvalid hsafety hbase with
    ⟨largerTypes, Htypes, htypesLE⟩
  have HvalidTypes := Htypes.valid Hvalid
  rcases H.staged.ctorsAdded.rebase HvalidTypes hsafety htypesLE with
    ⟨largerCtors, Hctors, hctorsLE⟩
  have HvalidCtors := Hctors.valid HvalidTypes
  rcases H.staged.recursorsAdded.rebase HvalidCtors hsafety hctorsLE with
    ⟨largerOutBase, Hrecursors, hrecursorsLE⟩
  refine ⟨largerOutBase, ⟨?_⟩, hrecursorsLE⟩
  exact {
    staged := {
      envTypes := H.staged.envTypes
      venvTypes := largerTypes
      envCtors := H.staged.envCtors
      venvCtors := largerCtors
      typesAdded := Htypes
      ctorsAdded := Hctors
      recursorsAdded := Hrecursors }
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := fun ci hci => (H.ctorsWF ci hci).mono htypesLE
    recursorsWF := fun ci hci => (H.recursorsWF ci hci).mono hctorsLE
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hrecursorsLE }

/-- Replay a certified block in a larger abstract environment.  This is the
core transport used by safe declarations across the unsafe/partial/safe
models: it reconstructs all three installation stages, their stage-relative
typing proofs, and monotonicity of the final rule-extended environment. -/
theorem BlockCertificate.rebase
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    ∃ largerOut,
      H.block.WF largerBase ∧
      H.block.install largerBase = some largerOut ∧
      outBase.addDefEqRules rules ≤ largerOut := by
  rcases H.rebaseCertificate Hvalid hsafety hbase with
    ⟨largerOutBase, ⟨Hlarger⟩, houtBase⟩
  exact ⟨largerOutBase.addDefEqRules rules, Hlarger.wf, Hlarger.install,
    VEnv.addDefEqRules_mono houtBase⟩

/-- Re-establish source and formation well-formedness in a larger safety
model using the freshly replayed block installation.  Freshness-sensitive
`addConstVals` facts come from `Hblock`; all semantic typing and positivity facts
are transported monotonically from the original declaration judgment. -/
theorem VInductDecl.WF.rebaseOfBlock
    {decl : VInductDecl} {block : VInductBlock}
    {base largerBase : VEnv}
    (H : decl.WF base)
    (hbase : base ≤ largerBase)
    (Hblock : block.WF largerBase)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants) :
    decl.WF largerBase := by
  rcases Hblock with
    ⟨largerTypes, largerCtors, largerRecursors, hlargerTypes,
      hlargerCtors, hlargerRecursors, _htypesWF, _hctorsWF, _hrecsWF,
      _hrulesWF⟩
  have hlargerTypes' :
      largerBase.addConstVals decl.typeConstants = some largerTypes := by
    simpa [htypes] using hlargerTypes
  have hlargerCtors' :
      largerTypes.addConstVals decl.constructorConstants = some largerCtors := by
    simpa [hctors] using hlargerCtors
  rcases H.1 with
    ⟨hnonempty, hnames, htypeUvars, hctorUvars, sourceTypes,
      sourceCtors, hsourceTypes, hsourceCtors, hsourceTypesWF,
      hsourceCtorsWF⟩
  have hsourceTypesLE : sourceTypes ≤ largerTypes :=
    VEnv.addConstVals_mono hbase hsourceTypes hlargerTypes'
  have Hsource : decl.SourceWF largerBase :=
    ⟨hnonempty, hnames, htypeUvars, hctorUvars, largerTypes, largerCtors,
      hlargerTypes', hlargerCtors',
      fun type htype => (hsourceTypesWF type htype).mono hbase,
      fun ctor hctor => (hsourceCtorsWF ctor hctor).mono hsourceTypesLE⟩
  cases H.2 with
  | ordinary Hordinary =>
    rcases Hordinary with
      ⟨params, resultLevel, formationTypes, hformationTypes, htypeShapes,
        hctorShapes⟩
    have hformationTypesLE : formationTypes ≤ largerTypes :=
      VEnv.addConstVals_mono hbase hformationTypes hlargerTypes'
    have Hformation : decl.FormationWF largerBase :=
      ⟨params, resultLevel, largerTypes, hlargerTypes',
        fun type htype =>
          ⟨(htypeShapes type htype).1,
            (htypeShapes type htype).2.mono hbase⟩,
        fun type htype ctor hctor =>
          let Hctor := hctorShapes type htype ctor hctor
          ⟨Hctor.1.mono hformationTypesLE,
            Hctor.2.mono hformationTypesLE⟩⟩
    exact ⟨Hsource, .ordinary Hformation⟩
  | nested Hnested hformationBase =>
    exact ⟨Hsource, .nested Hnested (hformationBase.trans hbase)⟩

/-- Replay a complete inductive refinement in a larger safety-indexed model.
The fresh block supplies the source-installation facts that plain weakening
cannot preserve, while source well-formedness and compilation semantics are
transported from the original model. -/
theorem BlockCertificate.rebaseAddInduct
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block) :
    ∃ largerOutBase,
      Nonempty (BlockCertificate safety prodEnv largerBase types ctors
        recursors rules outEnv largerOutBase) ∧
      VEnv.AddInduct largerBase decl (largerOutBase.addDefEqRules rules) ∧
      outBase.addDefEqRules rules ≤ largerOutBase.addDefEqRules rules := by
  rcases H.rebaseCertificate Hvalid hsafety hbase with
    ⟨largerOutBase, ⟨Hlarger⟩, houtBase⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    hcompile.mono hbase Hlarger.wf
  exact ⟨largerOutBase, ⟨Hlarger⟩,
    .intro hdeclLarger hcompileLarger Hlarger.wf Hlarger.install,
    VEnv.addDefEqRules_mono houtBase⟩

/-- Exact production-only fact needed to keep a newly installed unsafe block
hidden from the unchanged partial and safe abstract models. -/
def InstalledInductiveHeadersUnsafe
    (sourceEnv outEnv : Environment) : Prop :=
  ∀ familyName familyInfo,
    outEnv.find? familyName = some (.inductInfo familyInfo) →
    sourceEnv.find? familyName = none →
    familyInfo.isUnsafe = true

/-- A batch whose production entries are all tagged unsafe supplies the
exact hidden-header certificate required by the safety-indexed extension. -/
theorem BlockCertificate.installedInductiveHeadersUnsafe
    (H : BlockCertificate .unsafe prodEnv unsafeBase types ctors recursors
      rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe) :
    InstalledInductiveHeadersUnsafe prodEnv outEnv := by
  intro familyName familyInfo hfamily hfresh
  rcases H.staged.combined.entryOrigin hwf hfamily with hold | hnew
  · rw [hfresh] at hold
    contradiction
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafety : (ConstantInfo.inductInfo familyInfo).safety =
        DefinitionSafety.unsafe := by
      rw [hinfo]
      exact hunsafe entry hentry
    cases h : familyInfo.isUnsafe
    · have heq : DefinitionSafety.safe = DefinitionSafety.unsafe := by
        simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial, h] using hsafety
      contradiction
    · rfl

/-- Constructor semantics for an unchanged observer of an unsafe block.
Every visible old family is transported through the production installation;
a genuinely new family is unsafe and hence cannot be visible to a partial or
safe observer. -/
theorem BlockCertificate.hiddenUnsafeConstructorSemantics
    (H : BlockCertificate .unsafe prodEnv unsafeBase types ctors recursors
      rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      observer prodEnv observerBase)
    (hobserver : observer ≠ .unsafe)
    (Hhidden : InstalledInductiveHeadersUnsafe prodEnv outEnv) :
    InductiveConstructorsSemanticallyCoherent observer outEnv observerBase := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := H.staged.combined
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.rebaseProduction
      (Hinstall.preservesSourceFind hwf C.lookup) VEnv.LE.rfl⟩
  · rcases hnew with ⟨_entry, _hentry, _hname, _hinfo⟩
    cases hold : prodEnv.find? familyName with
    | some oldInfo =>
      have hpreserved := Hinstall.preservesSourceFind hwf hold
      rw [hfamily] at hpreserved
      cases hpreserved
      rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
      exact ⟨C.rebaseProduction
        (Hinstall.preservesSourceFind hwf C.lookup) VEnv.LE.rfl⟩
    | none =>
      have hunsafe := Hhidden familyName familyInfo hfamily hold
      have hobserverUnsafe : observer ≤ DefinitionSafety.unsafe := by
        simpa [hunsafe] using hvisible
      have heq : observer = DefinitionSafety.unsafe :=
        DefinitionSafety.le_antisymm hobserverUnsafe
          DefinitionSafety.unsafe_le
      exact False.elim (hobserver heq)

/-- Lift one unsafe block installation to the three safety-indexed abstract
environments.  Partial and safe translation traces normally come from
ignoring the newly installed unsafe production constants; every other field
is derived from the block certificate and the source `VEnvs.WF`. -/
theorem BlockCertificate.extendUnsafe
    {ves : VEnvs}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WF prodEnv)
    (htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (outVEnv.addDefEqRules rules))
    (htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial))
    (htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe))
    (hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (outVEnv.addDefEqRules rules))
    (hinductiveProvenance : ∀ safety,
      InstalledInductiveProvenance safety outEnv.constants
        (match safety with
        | .unsafe => outVEnv.addDefEqRules rules
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe))
    (hheadersUnsafe : InstalledInductiveHeadersUnsafe prodEnv outEnv) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply Lean4Lean.VEnvs.WF.extendUnsafe wf (outVEnv.addDefEqRules rules)
    htrUnsafe htrPartial htrSafe
  · exact H.hasPrimitives wf.hasPrimitives
  · exact hsafePrimitives
  · exact wf.typeAnnotationWrappers.rebase
      (H.staged.combined.preservesSourceFind
        (wf.tr (safety := .unsafe)).map_wf)
  · exact hclosed
  · exact hconstructorOwners
  · intro safety
    cases safety with
    | «unsafe» => exact hconstructorSemantics
    | «partial» =>
      exact H.hiddenUnsafeConstructorSemantics
        (wf.tr (safety := .unsafe)).map_wf
        (wf.constructorSemantics (safety := .partial)) (by decide)
        hheadersUnsafe
    | safe =>
      exact H.hiddenUnsafeConstructorSemantics
        (wf.tr (safety := .unsafe)).map_wf
        (wf.constructorSemantics (safety := .safe)) (by decide)
        hheadersUnsafe
  · exact hinductiveProvenance
  · exact VInductBlock.install_le H.install

/-- Semantic endpoint of the executable block certificates. Once source
typing/formation and the independent compilation relation are supplied, the
staged executable installation constructs the abstract inductive extension. -/
theorem BlockCertificate.addInductAbstract
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hdecl : decl.WF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) :=
  .intro Hdecl Hcompile H.wf H.install

theorem BlockCertificate.addInductOfFormation
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : decl.SourceWF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) :=
  H.addInductAbstract (Hformation.declWF Hsource) Hcompile

/-- Ordinary compilation, source formation, and staged source translation
assemble directly into the abstract environment extension. -/
theorem BlockCertificate.addInductOfOrdinaryCompilation
    (H : BlockCertificate safety env venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : OrdinaryCompilationCertificate venv decl H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductOfFormation Hformation
    (Lean4Lean.TrInductDecl.sourceWF Htranslated)
    Hcompile.compilesTo

/-- Nested restoration has the same source boundary: the core translation
retains the pre-lowering constructor typing and staged freshness facts. -/
theorem BlockCertificate.addInductOfNestedCompilation
    (H : BlockCertificate safety env venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : NestedCompilationCertificate venv decl H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductOfFormation Hformation
    (Lean4Lean.TrInductDecl.sourceWF Htranslated)
    Hcompile.compilesTo

/-- Sound nested-formation endpoint.  Unlike the compatibility theorem above,
this consumes the independent source-to-expanded formation derivation rather
than asking the restored source declaration to satisfy the ordinary
constructor-shape judgment. -/
theorem BlockCertificate.addInductOfNestedFormation
    (H : BlockCertificate safety env venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : decl.NestedFormationWF venv)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : NestedCompilationCertificate venv decl H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.addInductAbstract
    ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
      .nested Hformation VEnv.LE.rfl⟩
    Hcompile.compilesTo

/-- Final assembly point for the implementation-refinement boundary. Once
the executable traversals have supplied source formation, compilation shape,
staged typing, and production-map conservation, no further semantic facts are
hidden in `AddInduct`. -/
theorem BlockCertificate.addInduct
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsourceAligned : Aligned checkSafety prodEnv.constants venv) :
    AddInduct checkSafety prodEnv.constants venv decl outEnv.constants
      (outVEnv.addDefEqRules rules) := by
  apply AddInduct.intro H.block hdecl hcompile H.wf H.install
  · exact horigins
  · intro name ci hfind
    have hfindEnv : prodEnv.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?,
        hsourceAligned.map_wf.find?'_eq_find?]
      exact hfind
    have hout := H.staged.combined.preservesSourceFind
      hsourceAligned.map_wf hfindEnv
    have houtWF := H.staged.combined.targetMapWF hsourceAligned.map_wf
    rw [Lean.Kernel.Environment.find?,
      houtWF.find?'_eq_find?] at hout
    exact hout
  · intro Haligned
    exact aligned_addDefEqs (H.staged.aligned Haligned) rules
  · exact H.staged.deltaConservative hsourceAligned

/-- For a safe declaration, the staging trace directly supplies the concrete
safe-observer alignment required by `AddInduct`. -/
theorem BlockCertificate.addInductSafe
    (H : BlockCertificate .safe prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsourceAligned : Aligned .safe prodEnv.constants venv) :
    AddInduct .safe prodEnv.constants venv decl outEnv.constants
      (outVEnv.addDefEqRules rules) := by
  exact H.addInduct hdecl hcompile horigins hsourceAligned

/-- Replay a safe certified block into any safety-indexed source model and
construct the concrete `AddInduct` relation at that model's observer safety. -/
theorem BlockCertificate.rebaseAddInductSafe
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid targetSafety prodEnv largerBase)
    (hbase : base ≤ largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl) :
    ∃ largerOutBase,
      Nonempty (BlockCertificate targetSafety prodEnv largerBase types ctors
        recursors rules outEnv largerOutBase) ∧
      AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
        (largerOutBase.addDefEqRules rules) ∧
      outBase.addDefEqRules rules ≤ largerOutBase.addDefEqRules rules := by
  rcases H.rebaseCertificate Hvalid DefinitionSafety.le_safe hbase with
    ⟨largerOutBase, ⟨Hlarger⟩, houtBase⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    hcompile.mono hbase Hlarger.wf
  have hadd : AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
      (largerOutBase.addDefEqRules rules) := by
    exact Hlarger.addInduct hdeclLarger hcompileLarger horigins
      Hvalid.tr.aligned
  exact ⟨largerOutBase, ⟨Hlarger⟩, hadd,
    VEnv.addDefEqRules_mono houtBase⟩

/-- Reconstruct constructor semantics for one replay of a safe block.  Old
families are transported from the corresponding source safety model.  A new
family is necessarily safe because the original batch was checked at
`.safe`, so its already-completed output witness transports along the replay
monotonicity proof. -/
theorem BlockCertificate.replaySafeConstructorSemantics
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hreplay : BlockCertificate observer prodEnv observerBase types ctors
      recursors rules outEnv replayBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      observer prodEnv observerBase)
    (Hcompleted : InductiveConstructorsSemanticallyCoherent .safe outEnv
      (outBase.addDefEqRules rules))
    (hreplay : outBase.addDefEqRules rules ≤
      replayBase.addDefEqRules rules) :
    InductiveConstructorsSemanticallyCoherent observer outEnv
      (replayBase.addDefEqRules rules) := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := Hreplay.staged.combined
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    have hlookup := Hinstall.preservesSourceFind hwf C.lookup
    have hle : observerBase ≤ replayBase.addDefEqRules rules :=
      Hinstall.le.trans VEnv.addDefEqRules_le
    exact ⟨C.rebaseProduction hlookup hle⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafe : .safe ≤ (ConstantInfo.inductInfo familyInfo).safety := by
      rw [hinfo]
      exact H.staged.combined.entrySafety hentry
    have hsafe' : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hsafe
    have hfamilySafe : familyInfo.isUnsafe = false := by
      cases h : familyInfo.isUnsafe
      · rfl
      · have hsafeUnsafe : DefinitionSafety.safe ≤
            DefinitionSafety.unsafe := by simpa [h] using hsafe'
        have heq : DefinitionSafety.safe = DefinitionSafety.unsafe :=
          DefinitionSafety.le_antisymm hsafeUnsafe DefinitionSafety.unsafe_le
        contradiction
    have hsafeVisible : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simp [hfamilySafe, DefinitionSafety.le_rfl]
    rcases Hcompleted familyName familyInfo hfamily hsafeVisible i hi with ⟨C⟩
    exact ⟨C.mono hreplay⟩

/-- A safe executable block extends all three abstract safety models.  Each
model is replayed independently, while monotonicity of the resulting family
is recovered from the shared abstract block installation. -/
theorem BlockCertificate.extendSafeExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      outBase.addDefEqRules rules ≤ ves'.venv .safe := by
  have valid (safety : DefinitionSafety) :
      CheckingEnv.Valid safety prodEnv (ves.venv safety) :=
    (wf.tr (safety := safety)).toCheckingValid
      (wf.hasPrimitives (safety := safety)) wf.safePrimitives
      wf.typeAnnotationWrappers
  rcases H.rebaseAddInductSafe (valid .unsafe)
      (wf.mono DefinitionSafety.unsafe_le) hdecl hcompile horigins with
    ⟨unsafeBase, ⟨Hunsafe⟩, HunsafeAdd, hunsafeLE⟩
  rcases H.rebaseAddInductSafe (valid .partial)
      (wf.mono DefinitionSafety.le_safe) hdecl hcompile horigins with
    ⟨partialBase, ⟨Hpartial⟩, HpartialAdd, hpartialLE⟩
  rcases H.rebaseAddInductSafe (valid .safe) VEnv.LE.rfl
      hdecl hcompile horigins with
    ⟨safeBase, ⟨Hsafe⟩, HsafeAdd, hsafeLE⟩
  let pre : DefinitionSafety → VEnv
    | .unsafe => unsafeBase
    | .partial => partialBase
    | .safe => safeBase
  let next (safety : DefinitionSafety) := (pre safety).addDefEqRules rules
  let cert : ∀ safety,
      BlockCertificate safety prodEnv (ves.venv safety) types ctors
        recursors rules outEnv (pre safety)
    | .unsafe => Hunsafe
    | .partial => Hpartial
    | .safe => Hsafe
  let adds : ∀ safety,
      AddInduct safety prodEnv.constants (ves.venv safety) decl outEnv.constants
        (next safety)
    | .unsafe => HunsafeAdd
    | .partial => HpartialAdd
    | .safe => HsafeAdd
  let outputLE : ∀ safety,
      outBase.addDefEqRules rules ≤ (pre safety).addDefEqRules rules
    | .unsafe => hunsafeLE
    | .partial => hpartialLE
    | .safe => hsafeLE
  have hprimitives : ∀ safety, (next safety).HasPrimitives := by
    intro safety
    exact (cert safety).hasPrimitives
      (wf.hasPrimitives (safety := safety))
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] :=
    (Hsafe.staged.valid (valid .safe)).safePrimitives
  have hsemantics : ∀ safety,
      InductiveConstructorsSemanticallyCoherent safety outEnv
        (next safety) := by
    intro safety
    exact H.replaySafeConstructorSemantics (cert safety)
      (wf.tr (safety := safety)).map_wf
      (wf.constructorSemantics (safety := safety)) hconstructorSemantics
      (outputLE safety)
  have hmono : ∀ {safety safety'}, safety ≤ safety' →
      next safety' ≤ next safety := by
    intro safety safety' hle
    exact VInductBlock.install_mono (wf.mono hle)
      (cert safety').install (cert safety).install
  rcases wf.extendInductExact decl next adds H.staged.quotInit_eq
      hprimitives hsafePrimitives hclosed hconstructorOwners hsemantics hmono with
    ⟨ves', wf', hsourceLE, hexact⟩
  refine ⟨ves', wf', hsourceLE, ?_⟩
  rw [hexact .safe]
  exact outputLE .safe

/-- Environment-preservation projection of `extendSafeExact`. -/
theorem BlockCertificate.extendSafe
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases H.extendSafeExact wf hdecl hcompile horigins hclosed
      hconstructorOwners hconstructorSemantics with
    ⟨ves', wf', hle, _hsafe⟩
  exact ⟨ves', wf', hle⟩

/-- Install a certified inductive block directly into the concrete
environment-refinement judgment.  This is the abstract/executable seam used
by the inductive branch of declaration verification. -/
theorem BlockCertificate.trEnv'
    {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsource : TrEnv' checkSafety prodEnv.constants quotInit venv) :
    TrEnv' checkSafety outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) :=
  .induct hdecl
    (H.addInduct hdecl hcompile horigins hsource.aligned) hsource

theorem BlockCertificate.trEnvSafe
    {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsource : TrEnv' .safe prodEnv.constants quotInit venv) :
    TrEnv' .safe outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) :=
  .induct hdecl
    (H.addInductSafe hdecl hcompile horigins hsource.aligned) hsource

/-- Unsafe inductives extend only the unsafe abstract model; partial and safe
models replay the concrete additions through `TrEnv'.ignore`. -/
theorem BlockCertificate.extendUnsafeOfHidden
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .unsafe))
    (hcompile : decl.CompilesTo (ves.venv .unsafe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (outVEnv.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have validUnsafe : CheckingEnv.Valid .unsafe prodEnv
      (ves.venv .unsafe) :=
    (wf.tr (safety := .unsafe)).toCheckingValid
      (wf.hasPrimitives (safety := .unsafe)) wf.safePrimitives
      wf.typeAnnotationWrappers
  have hiddenPartial : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.partial ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have hiddenSafe : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.safe ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (outVEnv.addDefEqRules rules) := by
    rw [H.staged.quotInit_eq]
    exact H.trEnv' hdecl hcompile horigins
      (wf.tr (safety := .unsafe))
  have htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial) := by
    rw [H.staged.quotInit_eq]
    apply H.staged.trEnvIgnore
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · exact wf.tr (safety := .partial)
  have htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe) := by
    rw [H.staged.quotInit_eq]
    apply H.staged.trEnvIgnore
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · exact wf.tr (safety := .safe)
  have hheadersUnsafe := H.installedInductiveHeadersUnsafe
    (wf.tr (safety := .unsafe)).map_wf hunsafe
  have haddUnsafe : AddInduct .unsafe prodEnv.constants
      (ves.venv .unsafe) decl outEnv.constants
      (outVEnv.addDefEqRules rules) :=
    H.addInduct hdecl hcompile horigins
      (wf.tr (safety := .unsafe)).aligned
  have houtMapWF := H.staged.combined.targetMapWF
    (wf.tr (safety := .unsafe)).map_wf
  have hiddenProvenance (observer : DefinitionSafety)
      (hobserver : observer ≠ .unsafe) :
      InstalledInductiveProvenance observer outEnv.constants
        (ves.venv observer) := by
    apply VerifyInductive.InstalledInductiveProvenance.rebaseHidden
      (wf.inductiveProvenance (safety := observer))
      haddUnsafe.preservesSourceFind
    intro familyName familyInfo hfamily hfresh
    have hfamilyEnv : outEnv.find? familyName =
        some (.inductInfo familyInfo) := by
      rw [Lean.Kernel.Environment.find?, houtMapWF.find?'_eq_find?]
      exact hfamily
    have hfreshEnv : prodEnv.find? familyName = none := by
      rw [Lean.Kernel.Environment.find?,
        (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
      exact hfresh
    have hunsafeFamily := hheadersUnsafe familyName familyInfo
      hfamilyEnv hfreshEnv
    have hobserverNotLE : ¬ observer ≤ DefinitionSafety.unsafe := by
      intro hle
      exact hobserver (DefinitionSafety.le_antisymm hle
        DefinitionSafety.unsafe_le)
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, hunsafeFamily] using hobserverNotLE
  have hinductiveProvenance : ∀ safety,
      InstalledInductiveProvenance safety outEnv.constants
        (match safety with
        | .unsafe => outVEnv.addDefEqRules rules
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe)
    | .unsafe => InstalledInductiveProvenance.addInduct
        (wf.inductiveProvenance (safety := .unsafe)) haddUnsafe
    | .partial => hiddenProvenance .partial (by decide)
    | .safe => hiddenProvenance .safe (by decide)
  exact H.extendUnsafe wf htrUnsafe htrPartial htrSafe
    (H.staged.valid validUnsafe).safePrimitives hclosed hconstructorOwners
    hconstructorSemantics hinductiveProvenance hheadersUnsafe

theorem BlockCertificate.trEnvOfOrdinaryCompilation
    (H : BlockCertificate checkSafety prodEnv venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : OrdinaryCompilationCertificate venv decl H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (htr : TrEnv' checkSafety prodEnv.constants quotInit venv) :
    TrEnv' checkSafety outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact H.trEnv' (Hformation.declWF Htranslated.sourceWF)
    Hcompile.compilesTo horigins htr

theorem BlockCertificate.trEnvOfNestedCompilation
    (H : BlockCertificate checkSafety prodEnv venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : NestedCompilationCertificate venv decl H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (htr : TrEnv' checkSafety prodEnv.constants quotInit venv) :
    TrEnv' checkSafety outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNestedCompilation
      Hsource hnonempty Hcompile
  exact H.trEnv' (Hformation.declWF Htranslated.sourceWF)
    Hcompile.compilesTo horigins htr

/-- Concrete-environment endpoint using the independent nested formation
derivation.  This is the refinement path for declarations whose restored
constructors deliberately do not have the ordinary lowered `CtorShape`. -/
theorem BlockCertificate.trEnvOfNestedFormation
    (H : BlockCertificate checkSafety prodEnv venv blockTypes blockCtors
      blockRecursors rules outEnv outVEnv)
    (Hformation : decl.NestedFormationWF venv)
    (Hsource : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl
      sourceEnvTypes sourceEnvCtors)
    (hnonempty : sourceTypes ≠ [])
    (Hcompile : NestedCompilationCertificate venv decl H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (htr : TrEnv' checkSafety prodEnv.constants quotInit venv) :
    TrEnv' checkSafety outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) := by
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNestedCompilation
      Hsource hnonempty Hcompile
  exact H.trEnv'
    ⟨Htranslated.sourceWF, .nested Hformation VEnv.LE.rfl⟩
    Hcompile.compilesTo horigins htr


end VerifyInductive
end Lean4Lean
