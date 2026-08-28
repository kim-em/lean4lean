import Lean4Lean.Verify.Inductive.PrimitiveConstructorEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Internal completed primitive prefix before its persistent production
origin/coherence fields are packaged for the common recursor boundary. -/
structure PrimitiveConstructorCorePhasesResult
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (outEnv : Environment) where
  checked : CheckedConstructorCertificate sourceEnv decl H.context.venv
    H.headers.params
  parameterPrefixes : CheckedRecursorParameterPrefixes stats indTypes
  constructorTails : CheckedRecursorConstructorTails H.context.venv c.lparams
    H.materialized.parameterScope stats decl indTypes
  ownerNormalForms : CheckedConstructorOwnerNormalForms stats indTypes
  declared : PrimitiveDeclaredConstructorsResult H outEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl H.context.venv declared.venvCtors

/-- Select one constructor installed by the completed primitive atomic batch
and recover its exact abstract semantic witness.  This is the primitive
counterpart of the ordinary two-fold positional bridge; it uses only the
staged header map WF and never asserts a valid header-only context. -/
theorem PrimitiveConstructorCorePhasesResult.installedConstructorSemanticCoherenceAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCorePhasesResult H outEnv)
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
    R.declared.installed.preservesSourceFind H.context.checking.map_wf
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
    R.declared.installed.findEntry H.context.checking.map_wf hctorEntry
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

/-- The two atomic primitive installation stages identify every newly visible
production inductive family with its exact source declaration position. -/
theorem PrimitiveConstructorCorePhasesResult.productionInductiveOrigins
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCorePhasesResult H outEnv) :
    ProductionInductiveOrigins c.env.constants outEnv.constants decl := by
  intro familyName familyInfo hfamily
  have hsourceWF := H.sourceContext.checking.tr.map_wf
  have hheaderWF := H.context.checking.map_wf
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
          R.declared.installed.findEntry H.context.checking.map_wf hctorEntry
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

/-- Atomic primitive header and constructor installation preserves semantic
coherence for old families and establishes it positionally for the newly
installed canonical family. -/
theorem PrimitiveConstructorCorePhasesResult.constructorSemantics
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCorePhasesResult H outEnv)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      safety c.env sourceEnv) :
    InductiveConstructorsSemanticallyCoherent
      safety outEnv R.declared.venvCtors := by
  intro familyName familyInfo hfamily hvisible ctorIdx hctor
  rcases R.declared.installed.entryOrigin H.context.checking.map_wf
      hfamily with hheader | hctorOrigin
  · rcases H.installed.entryOrigin H.sourceContext.checking.tr.map_wf
        hheader with hold | hnew
    · rcases Hsource familyName familyInfo hold hvisible ctorIdx hctor with ⟨C⟩
      have hctorHeader := H.installed.preservesSourceFind
        H.sourceContext.checking.tr.map_wf C.lookup
      have hctorFinal := R.declared.installed.preservesSourceFind
        H.context.checking.map_wf hctorHeader
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

/-- Package the internally accumulated finite evidence as the public
primitive constructor-phase result consumed by the common recursor adapter. -/
def PrimitiveConstructorCorePhasesResult.complete
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCorePhasesResult H outEnv) :
    PrimitiveConstructorPhasesResult H outEnv where
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  declared := R.declared
  formation := R.formation
  core := R.core
  productionInductiveOrigins := R.productionInductiveOrigins
  constructorSemantics := R.constructorSemantics

/-- The successful executable check is followed by the exact atomic
constructor fold.  Validity is regained only at the fold's completed Bool/Nat
endpoint. -/
theorem AddInductive.primitiveConstructorCorePhases.WF
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : PrimitiveConstructorCorePhasesResult H outEnv, True := by
  exact (AddInductive.checkConstructors.primitiveCoreWF H Hshape).bind
    fun _ Hchecked =>
      (AddInductive.declareConstructors.primitiveWF H Hshape
        Hchecked.1.checked hvisible).mono fun outEnv Hdeclared => by
          rcases Hdeclared with ⟨Hdeclared, _⟩
          let Hformation : FormationCertificate sourceEnv decl := {
            headers := H.headers
            envTypes := H.context.venv
            typesInstalled := H.translation.typesAdded
            constructorParameters := Hchecked.1.parameterShapes
              H.context.checking.wf H.translation.types
              (H.materialized.runtimeScope.scopeWF H.context.checking.wf)
              (checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
                H.materialized).params_size
              H.materialized.uvars.symm (by
                rw [← H.headerParams]
                exact H.materialized.paramsContext)
            constructors := Hchecked.1.checked.formation }
          exact ⟨{
            checked := Hchecked.1.checked
            parameterPrefixes := Hchecked.1.parameterPrefixes
            constructorTails := Hchecked.1.constructorTails
            ownerNormalForms := Hchecked.2
            declared := Hdeclared
            formation := Hformation
            core := Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases
              H.translation Hdeclared.translation }, trivial⟩

/-- The complete executable primitive constructor prefix, including the
persistent production-origin and constructor-semantic invariants. -/
theorem AddInductive.primitiveConstructorPhases.WF
    (H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : PrimitiveConstructorPhasesResult H outEnv, True := by
  exact (AddInductive.primitiveConstructorCorePhases.WF H Hshape hvisible).mono
    fun _ Hcore => by
      rcases Hcore with ⟨R, _⟩
      exact ⟨R.complete, trivial⟩

end VerifyInductive
end Lean4Lean
