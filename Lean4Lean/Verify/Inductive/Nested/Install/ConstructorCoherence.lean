import Lean4Lean.Verify.Inductive.Nested.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Nested.Restoration.ParameterOpening

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Production origins close the final mutual blocks once the exact restored
source-family members are known to be present.  This isolates the only
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
    exact ⟨Hclosed.members.mapEnvironment hpreserves, Hclosed.target,
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

/-- Every original source family restored by the exact outer fold is visible
in its final production environment, in source order. -/
private theorem StateForMTrace.restoredSourceMemberInfos
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    {auxRec : NameMap Name} {remaining : List InductiveType}
    {stepSource targetEnv : Environment}
    (Htrace : StateForMTrace
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
      have Halign := Hstep'.productionFamilyAlignmentAt Hlower Hc Hprod
        Hsource Hmetadata Hsources Harity Howners hempty familyIdx hfamily
        hsourceWF
      obtain ⟨headEntries, HheadFresh⟩ :=
        Hstep'.restored.freshTrace hsourceWF
      have hmiddleWF : middle.constants.WF :=
        HheadFresh.targetWF hsourceWF
      obtain ⟨tailEntries, HtailFresh⟩ :=
        Htail.inductiveFreshTrace hmiddleWF
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

private theorem sourceTypeNames
    (H : List.Forall₂ (TrInductiveType sourceEnv envTypes lparams)
      sourceTypes targetTypes) :
    sourceTypes.map (fun type => type.name) =
      targetTypes.map (fun type => type.name) := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [Hhead.header.name, ih]

/-- The exact closed lowering, installed ordinary producer, and restoration
trace discharge the final mutual-block closure premise. -/
theorem NestedFinalAssemblyCertificate.mutualInductivesClosed
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hsourceClosed : MutualInductivesClosed sourceProdEnv) :
    MutualInductivesClosed outEnv := by
  have Hsource : TrInductDeclCore sourceEnv c.lparams nparams sourceTypes
      isUnsafe decl C.canonical.venvTypes C.canonical.venvCtors := by
    simpa only [hlparams] using C.sourceSemantics.core C.typesSource C.uvars
      C.numParams C.unsafeEq C.typesAdded C.constructorsAdded
  have Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  obtain ⟨HprimaryMembers, HprimaryParams⟩ :=
    Hrestored.inductives.restoredSourceMemberInfos Hlower Hc Hprod Hsource
      Hmetadata Hsources Harity Howners hempty [] (by simp) hsourceWF
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshTrace hsourceWF
  obtain ⟨auxEntries, HauxFresh⟩ :=
    Hrestored.auxiliaries.recursorFreshTrace
      (HprimaryFresh.targetWF hsourceWF)
  have HmembersSource : InductiveMemberInfos outEnv
      (sourceTypes.map (fun type => type.name)) :=
    HprimaryMembers.mapEnvironment
      (HauxFresh.preservesSourceFind (HprimaryFresh.targetWF hsourceWF))
  have Hmembers : InductiveMemberInfos outEnv
      (decl.types.map (fun type => type.name)) := by
    rw [← sourceTypeNames Hsource.types]
    exact HmembersSource
  have HmemberParams : ∀ member info,
      member ∈ decl.types.map (fun type => type.name) →
      outEnv.find? member = some (.inductInfo info) →
      info.numParams = decl.nparams := by
    intro member info hmember hlookup
    have hmemberSource : member ∈
        sourceTypes.map (fun type => type.name) := by
      rwa [sourceTypeNames Hsource.types]
    rcases HprimaryMembers.find hmemberSource with
      ⟨primaryInfo, hprimaryLookup⟩
    have houtLookup := HauxFresh.preservesSourceFind
      (HprimaryFresh.targetWF hsourceWF) hprimaryLookup
    rw [hlookup] at houtLookup
    have hinfo : info = primaryInfo :=
      ConstantInfo.inductInfo.inj (Option.some.inj houtLookup)
    subst info
    exact HprimaryParams member primaryInfo hmemberSource hprimaryLookup
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using VEnv.addConstVals_names_nodup C.typesAdded
  have Hfresh := HprimaryFresh.append HauxFresh
  have Horigins := C.productionInductiveOrigins Hlower Hc Hprod Hmetadata
    Hsources Harity Howners hempty henv hlparams hnames
  apply InductInfosFromDecl.mutualInductivesClosed Horigins
    (by simpa only [henv] using hsourceWF)
    (by simpa only [henv] using Hfresh.targetWF hsourceWF)
    hsourceClosed
  · intro name found hfind
    have hfind' : c.env.find? name = some found := by
      simpa only [henv] using hfind
    exact Hfresh.preservesSourceFind hsourceWF hfind'
  · exact Hmembers
  · exact HmemberParams
  · exact htypeNames

/-- The positionally aligned constructor restoration trace retains enough
installed-production metadata to show that every restored constructor is
exactly unsafe, not merely visible to the unsafe checker. -/
private theorem LoweredRestoredConstructors.unsafeFreshTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Htrace : LoweredRestoredConstructors result mappingEnv loweredEnv
      params nparams c.safety c.lparams sources state targets finalState
      sourceProdEnv targetProdEnv)
    (owner : InductiveType) (howner : owner ∈ indTypes.toList)
    (htargets : ∀ target ∈ targets, target ∈ owner.ctors)
    (hunsafe : isUnsafe = true)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  induction Htrace with
  | nil => exact ⟨[], .nil, by simp⟩
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      targets finalState targetProdEnv Hmapping Hstep _hsafety _hlevels
      _hname _htype Htail ih =>
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hmetadata := Hstep.metadataOfInstalled Hprod howner
        (htargets target (by simp)) rfl
      have hciUnsafe : ci.safety = .unsafe := by
        simp [ci, ConstantInfo.safety, ConstantInfo.isUnsafe,
          Hstep.restored.restoration.isUnsafe, hmetadata.2.2.2, hunsafe]
      have hfresh : sourceProdEnv.find? ci.name = none :=
        find?_none_of_contains_false hwf Hstep.restored.fresh
      have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hnextWF : middleProdEnv.constants.WF := by
        rw [hmiddle]
        exact constantsWF_add_checked hwf hfresh
      have htargetsTail : ∀ tail ∈ targets, tail ∈ owner.ctors := by
        intro tail htail
        exact htargets tail (by simp [htail])
      rcases ih htargetsTail hnextWF with ⟨entries, Hentries, hentries⟩
      have Hentries' : FreshConstantTrace (sourceProdEnv.add ci) entries
          targetProdEnv := by
        rw [← hmiddle]
        exact Hentries
      refine ⟨ci :: entries, .cons hfresh Hentries', ?_⟩
      intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | htail
      · exact hciUnsafe
      · exact hentries entry htail

/-- A recursor restoration whose source name belongs to the exact generated
batch restores an exactly unsafe entry when that batch was produced in the
unsafe checking context. -/
private theorem RestoredRecursorStep.unsafeFreshTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (hgenerated : oldRecName ∈
      (Hprod.entries.map Prod.snd).map (·.name))
    (hsafety : c.safety = .unsafe)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  rcases List.mem_map.mp hgenerated with ⟨value, hvalue, hvalueName⟩
  rcases Hprod.installed.existsEntryOfValue hvalue with ⟨info, hentry⟩
  have hlookup := Hprod.findRecursorOfMem hentry
  have hentryName := Hprod.installed.entryNames hentry
  have holdInfo : info = .recInfo Hstep.oldInfo := by
    have hlookup' : loweredEnv.find? info.name =
        some (.recInfo Hstep.oldInfo) := by
      rw [hentryName, hvalueName]
      exact Hstep.lookup
    exact Option.some.inj (hlookup.symm.trans hlookup')
  rcases List.mem_iff_getElem.mp hentry with ⟨i, hi, hentryEq⟩
  have hi' : i < Hprod.entries.length := by simpa using hi
  let E := Hprod.generated.entry i hi'
  have hsource : Hprod.entries[i].1 = .recInfo E.info := E.source_eq
  have hinfo : Hstep.oldInfo = E.info := by
    have : info = .recInfo E.info :=
      (congrArg Prod.fst hentryEq).symm.trans hsource
    rw [holdInfo] at this
    exact ConstantInfo.recInfo.inj this
  have hlocalSafety : Hprod.localContext.safety = .unsafe :=
    Hprod.localExtends.safety_eq.trans hsafety
  have holdUnsafe : Hstep.oldInfo.isUnsafe = true := by
    rw [hinfo, E.isUnsafe, hlocalSafety]
    decide
  let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
  have hciUnsafe : ci.safety = .unsafe := by
    simp [ci, ConstantInfo.safety, ConstantInfo.isUnsafe,
      Hstep.restored.restoration.isUnsafe, holdUnsafe]
  have hfresh : sourceProdEnv.find? ci.name = none :=
    find?_none_of_contains_false hwf Hstep.restored.fresh
  have htarget : targetProdEnv = sourceProdEnv.add ci :=
    congrArg Prod.snd Hstep.restored.output
  rw [htarget]
  exact ⟨[ci], .cons hfresh .nil, by simpa using hciUnsafe⟩

/-- One exact primary-family restoration emits only unsafe entries when the
source declaration and generated recursor batch are unsafe. -/
private theorem RestoredInductiveStep.unsafeFreshTraceAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      sourceProdEnv targetProdEnv)
    (hunsafe : isUnsafe = true) (hsafety : c.safety = .unsafe)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  rcases Hlower.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultFamily, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hresultArray : familyIdx < result.types.toArray.size := by
    simpa using hresultFamily
  have htargetArrayEq : result.types.toArray[familyIdx] = target := by
    simpa using htargetEq
  have htargetMem : target ∈ result.types.toArray.toList := by
    rw [← htargetArrayEq]
    simpa using Array.getElem_mem hresultArray
  have Halign := Hstep.productionFamilyAlignmentAt Hlower Hc Hprod Hsource
    Hmetadata Hsources Harity Howners hempty familyIdx hfamily hwf
  let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
  have hheaderBool : Hstep.restored.header.newInfo.isUnsafe = true :=
    Halign.isUnsafe.trans (Hsource.isUnsafe.trans hunsafe)
  have hheaderUnsafe : header.safety = .unsafe := by
    simp [header, ConstantInfo.safety, ConstantInfo.isUnsafe,
      hheaderBool]
  have hheaderFresh : sourceProdEnv.find? header.name = none :=
    find?_none_of_contains_false hwf Hstep.restored.header.fresh
  have hheaderEnv : Hstep.restored.headerEnv = sourceProdEnv.add header :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderWF : Hstep.restored.headerEnv.constants.WF := by
    rw [hheaderEnv]
    exact constantsWF_add_checked hwf hheaderFresh
  rcases Hlower.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨_fvars, _state, target', _loweredState, _hparams, _hnodup, _hsize,
      htarget', _hctorNames, _Hmappings, _HrawTrace, HctorTrace⟩
  have htarget'Eq : target' = target := by
    have := htarget'.symm.trans htarget
    exact Option.some.inj this
  subst target'
  rcases HctorTrace.unsafeFreshTrace Hprod target htargetMem
      (fun ctor hctor => hctor) hunsafe hheaderWF with
    ⟨ctorEntries, HctorEntries, hctorUnsafe⟩
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorEntries.targetWF hheaderWF
  have hrecords : Hprod.recInfos.size = result.types.toArray.size := by
    rw [Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simp
  have hgenerated := Hprod.generated.recursorName_mem hrecords familyIdx
    hresultArray
  have hbang : result.types.toArray[familyIdx]! = target := by
    rw [Array.getElem!_eq_getD,
      ← Array.getElem_eq_getD (h := hresultArray) default,
      htargetArrayEq]
  have hprimaryGenerated : Lean.mkRecName sourceTypes[familyIdx].name ∈
      (Hprod.entries.map Prod.snd).map (·.name) := by
    have htargetGenerated : Lean.mkRecName target.name ∈
        (Hprod.entries.map Prod.snd).map (·.name) := by
      simpa [hbang] using hgenerated
    rw [Hmapping.name] at htargetGenerated
    exact htargetGenerated
  rcases Hstep.restored.recursor.unsafeFreshTrace Hprod hprimaryGenerated
      hsafety hconstructorWF with
    ⟨recEntries, HrecEntries, hrecUnsafe⟩
  have HctorRec := HctorEntries.append HrecEntries
  have Htail : FreshConstantTrace (sourceProdEnv.add header)
      (ctorEntries ++ recEntries) targetProdEnv := by
    rw [← hheaderEnv]
    exact HctorRec
  refine ⟨header :: ctorEntries ++ recEntries,
    .cons hheaderFresh Htail, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with rfl | htail
  · exact hheaderUnsafe
  · rcases List.mem_append.mp htail with hctor | hrec
    · exact hctorUnsafe entry hctor
    · exact hrecUnsafe entry hrec

/-- The exact outer primary-family fold emits only unsafe entries. -/
private theorem StateForMTrace.unsafeInductiveFreshTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining sourceProdEnv targetProdEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hunsafe : isUnsafe = true) (hsafety : c.safety = .unsafe)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  induction Htrace generalizing processed with
  | nil => exact ⟨[], .nil, by simp⟩
  | @cons head source middle tail target Hstep Htail ih =>
      let familyIdx := processed.length
      have hfamily : familyIdx < sourceTypes.length := by
        simp [familyIdx, hsplit]
      have hfamilyEq : sourceTypes[familyIdx] = head := by
        simp [familyIdx, hsplit]
      have Hstep' : RestoredInductiveStep result loweredEnv auxRec
          (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          source middle := by
        simpa only [hfamilyEq] using Hstep
      rcases Hstep'.unsafeFreshTraceAt Hlower Hc Hprod Hsource Hmetadata
          Hsources Harity Howners hempty familyIdx hfamily hunsafe hsafety hwf
          with
        ⟨headEntries, Hhead, hheadUnsafe⟩
      have hmiddleWF : middle.constants.WF := Hhead.targetWF hwf
      rcases ih (processed := processed ++ [head])
          (by simpa [List.append_assoc] using hsplit) hmiddleWF with
        ⟨tailEntries, HtailEntries, htailUnsafe⟩
      refine ⟨headEntries ++ tailEntries,
        Hhead.append HtailEntries, ?_⟩
      intro entry hentry
      rcases List.mem_append.mp hentry with hhead | htail
      · exact hheadUnsafe entry hhead
      · exact htailUnsafe entry htail

/-- A recursor-only restoration fold emits only unsafe entries when each
source name is identified with the exact generated batch. -/
private theorem StateForMTrace.unsafeRecursorFreshTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv)
    (hgenerated : ∀ name ∈ names,
      name ∈ (Hprod.entries.map Prod.snd).map (·.name))
    (hsafety : c.safety = .unsafe)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  induction Htrace with
  | nil => exact ⟨[], .nil, by simp⟩
  | @cons head source middle tail target Hstep Htail ih =>
      rcases Hstep.unsafeFreshTrace Hprod
          (hgenerated head (by simp)) hsafety hwf with
        ⟨headEntries, Hhead, hheadUnsafe⟩
      have hmiddleWF : middle.constants.WF := Hhead.targetWF hwf
      have hgeneratedTail : ∀ name ∈ tail,
          name ∈ (Hprod.entries.map Prod.snd).map (·.name) := by
        intro name hname
        exact hgenerated name (by simp [hname])
      rcases ih hgeneratedTail hmiddleWF with
        ⟨tailEntries, HtailEntries, htailUnsafe⟩
      refine ⟨headEntries ++ tailEntries,
        Hhead.append HtailEntries, ?_⟩
      intro entry hentry
      rcases List.mem_append.mp hentry with hhead | htail
      · exact hheadUnsafe entry hhead
      · exact htailUnsafe entry htail

/-- The complete exact production restoration trace is uniformly unsafe.
This is the canonical trace later transported to any extension-equivalent
fresh trace by `NestedFinalAssemblyCertificate.productionOrder`. -/
theorem RestoredNestedDeclarationsResult.unsafeFreshTraceOfProduction
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams true
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams (main :: rest)
      true sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks (main :: rest))
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1
      ((), targetProdEnv))
    (hsafety : c.safety = .unsafe)
    (hwf : sourceProdEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceProdEnv entries targetProdEnv ∧
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  rcases H.inductives.unsafeInductiveFreshTrace Hlower Hc Hprod Hsource
      Hmetadata Hsources Harity Howners hempty [] (by simp) rfl hsafety hwf with
    ⟨primaryEntries, Hprimary, hprimaryUnsafe⟩
  have hprimaryWF := Hprimary.targetWF hwf
  have hauxGenerated : ∀ name ∈
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1,
      name ∈ (Hprod.entries.map Prod.snd).map (·.name) := by
    intro name hname
    exact Hlower.auxRecNameGeneratedAtFresh Hc Hprod hempty hname
  rcases H.auxiliaries.unsafeRecursorFreshTrace Hprod hauxGenerated
      hsafety hprimaryWF with
    ⟨auxEntries, Haux, hauxUnsafe⟩
  refine ⟨primaryEntries ++ auxEntries, Hprimary.append Haux, ?_⟩
  intro entry hentry
  rcases List.mem_append.mp hentry with hprimary | haux
  · exact hprimaryUnsafe entry hprimary
  · exact hauxUnsafe entry haux

/-- Exact restoration plus the certificate's production-order permutation
discharges unsafe safety for every fresh trace of the same final extension. -/
theorem NestedFinalAssemblyCertificate.entriesUnsafe
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    (C : NestedFinalAssemblyCertificate H sourceEnv sourceDecl lparams
      nparams true .unsafe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams true depth
      sourceEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hauxRec : auxRec =
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
    (hauxNames : auxRecNames =
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1)
    (hsafety : c.safety = .unsafe) :
    ∀ entries (_Hentries : FreshConstantTrace sourceProdEnv entries outEnv),
      ∀ entry ∈ entries, entry.safety = .unsafe := by
  have Hsource : TrInductDeclCore sourceEnv c.lparams nparams sourceTypes
      true sourceDecl C.canonical.venvTypes C.canonical.venvCtors := by
    simpa only [hlparams] using C.sourceSemantics.core C.typesSource C.uvars
      C.numParams C.unsafeEq C.typesAdded C.constructorsAdded
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  cases sourceTypes with
  | nil => exact False.elim (C.sourceNonempty rfl)
  | cons main rest =>
      have Hrestored : RestoredNestedDeclarationsResult result loweredEnv
          c.env (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
          ((main :: rest).map (fun type => type.name)) (main :: rest)
          (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1
          ((), outEnv) := by
        simpa only [henv, hnames, hauxRec, hauxNames] using H
      rcases Hrestored.unsafeFreshTraceOfProduction Hlower Hc Hprod Hsource
          Hmetadata Hsources Harity Howners hempty hsafety hsourceWF with
        ⟨exactEntries, Hexact, hexactUnsafe⟩
      intro entries Hentries entry hentry
      have Hentries' : FreshConstantTrace c.env entries outEnv := by
        simpa only [henv] using Hentries
      have hactualCanonical := C.productionOrder entries Hentries
      have hexactCanonical := C.productionOrder exactEntries (by
        simpa only [henv] using Hexact)
      have hactualExact : entries ~ exactEntries :=
        hactualCanonical.trans hexactCanonical.symm
      exact hexactUnsafe entry (hactualExact.mem_iff.mp hentry)

/-- Safe final assembly with both production origins and final mutual closure
derived from the exact producer/restoration evidence. -/
theorem NestedFinalAssemblyCertificate.safeInductiveFinalResultOfProductionClosed
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name}
    (C : NestedFinalAssemblyCertificate H (ves.venv .safe) decl lparams
      nparams false .safe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams false depth
      (ves.venv .safe) result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WFCore sourceProdEnv) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety))
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hconstructorSemantics :
      CtorParamsAgree .safe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .safe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = false ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      false) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  have hclosed := C.mutualInductivesClosed Hlower Hc Hprod Hmetadata Hsources
    Harity Howners hempty henv hlparams hnames wf.inductivesClosed
  exact C.safeInductiveFinalResultOfProduction wf hcorner Hlower Hc Hprod
    Hmetadata Hsources Harity hempty henv hlparams hnames hclosed
      hconstructorSemantics htypesH hctorOrigin

/-- Unsafe final assembly with origins, final mutual closure, and uniform
restoration-entry safety all derived from the exact producer/restoration
evidence.  Constructor semantic coherence is the only remaining final-model
premise. -/
theorem NestedFinalAssemblyCertificate.unsafeInductiveFinalResultOfProductionClosed
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name}
    (C : NestedFinalAssemblyCertificate H (ves.venv .unsafe) decl lparams
      nparams true .unsafe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams true depth
      (ves.venv .unsafe) result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WFCore sourceProdEnv) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety))
    (Hlower : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hauxRec : auxRec =
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
    (hauxNames : auxRecNames =
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1)
    (hsafety : c.safety = .unsafe)
    (hconstructorSemantics :
      CtorParamsAgree .unsafe outEnv
        (C.finalBaseVEnv.addDefEqRules
          (C.primaryRules ++ C.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .unsafe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = true ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      true) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  have hentries := C.entriesUnsafe Hlower Hc Hprod Hmetadata Hsources Harity
    Howners hempty henv hlparams hnames hauxRec hauxNames hsafety
  have hclosed := C.mutualInductivesClosed Hlower Hc Hprod Hmetadata Hsources
    Harity Howners hempty henv hlparams hnames wf.inductivesClosed
  exact C.unsafeInductiveFinalResultOfProduction wf hcorner Hlower Hc Hprod
    Hmetadata Hsources Harity hempty henv hlparams hnames hentries hclosed
      hconstructorSemantics htypesH hctorOrigin

/-- Consume a rich exact safe nested run directly.  All dependent ordinary
production indices are recovered from the alignments retained by the run. -/
private theorem NestedInstalledProduction.reindex
    (P : NestedInstalledProduction loweredEnv)
    {c' : AddInductive.Context} {nparams' : Nat} {isUnsafe' : Bool}
    {initialEnv' : VEnv} {indTypes' : Array InductiveType}
    (hc : P.c = c') (hnparams : P.nparams = nparams')
    (hunsafe : P.isUnsafe = isUnsafe')
    (henv : P.initialEnv = initialEnv')
    (htypes : P.indTypes = indTypes') :
    ∃ Hheaders : HeaderEnvironment c' P.stats P.loweredDecl nparams'
        isUnsafe' P.depth initialEnv' indTypes' P.headerEnv,
      ∃ Hconstructors : OrdinaryConstructorCheck Hheaders P.ctorEnv,
        Nonempty (RecursorCheck Hconstructors.toConstructorCheck loweredEnv) := by
  subst c'
  subst nparams'
  subst isUnsafe'
  subst initialEnv'
  subst indTypes'
  exact ⟨P.headers, P.constructors, ⟨P.production⟩⟩

theorem NestedExactFinalRunResult.safeInductiveFinalResult
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes
      (ves.venv .safe) decl lparams nparams false .safe outEnv)
    (wf : ves.WFCore sourceProdEnv) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety))
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hmetadata : SourcePrefixOfLowered decl E.production.loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (hconstructorSemantics :
      CtorParamsAgree .safe outEnv
      (E.assembly.finalBaseVEnv.addDefEqRules
          (E.assembly.primaryRules ++ E.assembly.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .safe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = false ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      false) := by
  have hisUnsafe : E.production.isUnsafe = false := by
    rw [E.production_isUnsafe, E.productionContext_safety]
    decide
  obtain ⟨Hheaders, Hconstructors, ⟨Hproduction⟩⟩ :=
    E.production.reindex E.production_c E.production_nparams hisUnsafe
      E.production_initialEnv E.production_indTypes
  have Harity : decl.ConstructorArityPrefix E.production.loweredDecl := by
    have h := E.assembly.constructorArityPrefix
    rw [E.production_eq] at h
    exact h
  exact E.assembly.safeInductiveFinalResultOfProductionClosed wf hcorner Hlower
    E.productionContextWF Hproduction Hmetadata Hsources Harity hempty
    E.productionContext_env E.productionContext_lparams rfl
      hconstructorSemantics htypesH hctorOrigin

/-- Consume a rich exact unsafe nested run directly.  Closure and every
unsafe restoration-entry tag are reconstructed from its exact production
and restoration traces. -/
theorem NestedExactFinalRunResult.unsafeInductiveFinalResult
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes
      (ves.venv .unsafe) decl lparams nparams true .unsafe outEnv)
    (wf : ves.WFCore sourceProdEnv) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety))
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hmetadata : SourcePrefixOfLowered decl E.production.loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (hconstructorSemantics :
      CtorParamsAgree .unsafe outEnv
      (E.assembly.finalBaseVEnv.addDefEqRules
          (E.assembly.primaryRules ++ E.assembly.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .unsafe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = true ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      true) := by
  have hisUnsafe : E.production.isUnsafe = true := by
    rw [E.production_isUnsafe, E.productionContext_safety]
    decide
  obtain ⟨Hheaders, Hconstructors, ⟨Hproduction⟩⟩ :=
    E.production.reindex E.production_c E.production_nparams hisUnsafe
      E.production_initialEnv E.production_indTypes
  have Harity : decl.ConstructorArityPrefix E.production.loweredDecl := by
    have h := E.assembly.constructorArityPrefix
    rw [E.production_eq] at h
    exact h
  exact E.assembly.unsafeInductiveFinalResultOfProductionClosed wf hcorner Hlower
    E.productionContextWF Hproduction Hmetadata Hsources Harity hempty
    E.productionContext_env E.productionContext_lparams rfl rfl rfl
      E.productionContext_safety hconstructorSemantics htypesH hctorOrigin

/-! ## Narrow semantic residue for restored constructors -/

/-- The exact semantic datum not contained in production/restoration
metadata: the independently translated source family and constructor expose
the requested number of leading binders, and those two binder contexts are
definitionally equal.  Residual bodies are intentionally unconstrained. -/
structure RestoredConstructorParameterDomains
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
def RestoredConstructorParameterDomains.monoReindex
    (H : RestoredConstructorParameterDomains venv levelParams numParams
      familyTarget constructorTarget)
    (hle : venv ≤ targetEnv)
    (hlevels : levelParams.length = targetLevelParams.length)
    (hparams : numParams = targetNumParams) :
    RestoredConstructorParameterDomains targetEnv targetLevelParams
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

/-- The pointwise semantic payload that remains after the exact restored
source trace has fixed every family and constructor target.  It is stated in
the canonical post-header environment, the earliest common environment in
which both translated parameter telescopes are available. -/
def NestedRestoredConstructorParameterDomains
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) : Prop :=
  ∀ familyIdx (hfamily : familyIdx < decl.types.length)
    ctorIdx (hctor : ctorIdx < decl.types[familyIdx].ctors.length),
    Nonempty (RestoredConstructorParameterDomains C.canonical.venvCtors
      lparams nparams decl.types[familyIdx].toVConstVal.toVConstant
        decl.types[familyIdx].ctors[ctorIdx].toVConstant)

/-- Exact production alignment already contains the complete non-semantic
constructor metadata once the enclosing restored family alignment is fixed. -/
def productionConstructorAlignmentToCoherence
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

/-- Complete one restored constructor semantic witness from exact production
metadata, exact restored abstract targets, and only their common-parameter
context conversion.  Choosing each target itself as its normal form makes
clear that no residual-body correspondence is being assumed here. -/
theorem CtorInfoAlignment.semanticCoherenceOfParameterDomains
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
    (Hparams : RestoredConstructorParameterDomains venv
      familyInfo.levelParams familyInfo.numParams familyTarget
      constructorTarget) :
    Nonempty (CtorParamsAgreeAt prodEnv venv
      familyInfo.name familyInfo ctorIdx Hctor.familyInfo_ctorIdx_lt) := by
  rcases hfamilyWF with ⟨familyLevel, HfamilyType⟩
  rcases hconstructorWF with ⟨constructorLevel, HconstructorType⟩
  exact ⟨{
    toCtorInfoCoherentAt :=
      productionConstructorAlignmentToCoherence Hfamily Hctor hprodWF
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

/-- Fold the pointwise restored parameter-context evidence across all final
inductive families.  Families already present in the source environment reuse
the source model.  Every newly restored family is identified by exact
production alignment; its remaining semantic fields come from the canonical
source translation retained by the assembly certificate. -/
theorem NestedFinalAssemblyCertificate.constructorSemanticsOfParameterDomains
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {ves : VEnvs}
    (C : NestedFinalAssemblyCertificate H (ves.venv safety) decl lparams
      nparams isUnsafe safety)
    (wf : ves.WFCore sourceProdEnv)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      outEnv.constants decl)
    (Hparams : NestedRestoredConstructorParameterDomains C) :
    CtorParamsAgree safety outEnv
      (C.finalBaseVEnv.addDefEqRules
        (C.primaryRules ++ C.auxiliaryRules)) := by
  let installedVEnv := C.finalBaseVEnv.addDefEqRules
    (C.primaryRules ++ C.auxiliaryRules)
  have hsourceMapWF : sourceProdEnv.constants.WF :=
    (wf.tr (safety := safety)).map_wf
  obtain ⟨entries, Hfresh⟩ := H.freshTrace hsourceMapWF
  have houtMapWF : outEnv.constants.WF := Hfresh.targetWF hsourceMapWF
  have hctorsLE : C.canonical.venvCtors ≤ installedVEnv :=
    VEnv.addEliminators_addProjections_le.trans
      ((VEnv.addConstVals_le C.canonical.abstract_recursors).trans
        VEnv.addDefEqRules_le)
  have htypesLE : C.canonical.venvTypes ≤ installedVEnv :=
    (VEnv.addConstVals_le C.constructorsAdded).trans hctorsLE
  have hsourceLE : ves.venv safety ≤ installedVEnv :=
    (VEnv.addConstVals_le C.typesAdded).trans htypesLE
  have Hsource : TrInductDeclCore (ves.venv safety) lparams nparams
      sourceTypes isUnsafe decl C.canonical.venvTypes
        C.canonical.venvCtors :=
    C.sourceSemantics.core C.typesSource C.uvars C.numParams C.unsafeEq
      C.typesAdded C.constructorsAdded
  intro familyName familyInfo hfamily hvisible ctorIdx hctorIdx
  have hfamilyMap : outEnv.constants.find? familyName =
      some (.inductInfo familyInfo) := by
    change outEnv.constants.find?' familyName = some (.inductInfo familyInfo)
      at hfamily
    rwa [houtMapWF.find?'_eq_find?] at hfamily
  rcases Horigins familyName familyInfo hfamilyMap with hold | hnew
  · rcases wf.ctorParamsAgree familyName familyInfo (by
        change sourceProdEnv.constants.find?' familyName =
          some (.inductInfo familyInfo)
        rw [hsourceMapWF.find?'_eq_find?]
        exact hold) hvisible ctorIdx hctorIdx with ⟨Hctor⟩
    exact ⟨Hctor.rebaseProduction
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
    have hfamilyLookup : C.canonical.venvCtors.constants familyInfo.name =
        some (decl.types[familyIdx]'hfamilyIdx).toVConstVal.toVConstant := by
      rw [Hfamily.name]
      exact (VEnv.addConstVals_le C.constructorsAdded).constants
        (VEnv.addConstVals_get C.typesAdded hfamilyMember)
    have hconstructorLookup :
        C.canonical.venvCtors.constants
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
    have hcanonicalWF : C.canonical.venvCtors.WF :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource
        (wf.tr (safety := safety)).wf
    exact ⟨(Classical.choice
      (Lean4Lean.VerifyInductive.CtorInfoAlignment.semanticCoherenceOfParameterDomains
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

/-- Exact safe-run adapter for the pointwise parameter-domain fold.  The
closed lowering trace is used only to recover production origins for this
exact restoration; all constructor semantics then come from the fold above. -/
theorem NestedExactFinalRunResult.safeConstructorSemanticsOfParameterDomains
    {ves : VEnvs}
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes
      (ves.venv .safe) decl lparams nparams false .safe outEnv)
    (wf : ves.WFCore sourceProdEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hmetadata : SourcePrefixOfLowered decl E.production.loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent E.productionContext.env)
    (hempty : initialState.nestedAux = #[])
    (Hparams : NestedRestoredConstructorParameterDomains E.assembly) :
    CtorParamsAgree .safe outEnv
      (E.assembly.finalBaseVEnv.addDefEqRules
        (E.assembly.primaryRules ++ E.assembly.auxiliaryRules)) := by
  have hisUnsafe : E.production.isUnsafe = false := by
    rw [E.production_isUnsafe, E.productionContext_safety]
    decide
  obtain ⟨Hheaders, Hconstructors, ⟨Hproduction⟩⟩ :=
    E.production.reindex E.production_c E.production_nparams hisUnsafe
      E.production_initialEnv E.production_indTypes
  have Harity : decl.ConstructorArityPrefix E.production.loweredDecl := by
    have h := E.assembly.constructorArityPrefix
    rw [E.production_eq] at h
    exact h
  have Horigins := E.assembly.productionInductiveOrigins Hlower
    E.productionContextWF Hproduction Hmetadata Hsources Harity Howners hempty
      E.productionContext_env E.productionContext_lparams rfl
  exact E.assembly.constructorSemanticsOfParameterDomains wf Horigins Hparams

/-- Unsafe counterpart of `safeConstructorSemanticsOfParameterDomains`.
Unsafe restoration tags are irrelevant here: constructor coherence depends
only on exact production origins and the canonical abstract source trace. -/
theorem NestedExactFinalRunResult.unsafeConstructorSemanticsOfParameterDomains
    {ves : VEnvs}
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes
      (ves.venv .unsafe) decl lparams nparams true .unsafe outEnv)
    (wf : ves.WFCore sourceProdEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hmetadata : SourcePrefixOfLowered decl E.production.loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent E.productionContext.env)
    (hempty : initialState.nestedAux = #[])
    (Hparams : NestedRestoredConstructorParameterDomains E.assembly) :
    CtorParamsAgree .unsafe outEnv
      (E.assembly.finalBaseVEnv.addDefEqRules
        (E.assembly.primaryRules ++ E.assembly.auxiliaryRules)) := by
  have hisUnsafe : E.production.isUnsafe = true := by
    rw [E.production_isUnsafe, E.productionContext_safety]
    decide
  obtain ⟨Hheaders, Hconstructors, ⟨Hproduction⟩⟩ :=
    E.production.reindex E.production_c E.production_nparams hisUnsafe
      E.production_initialEnv E.production_indTypes
  have Harity : decl.ConstructorArityPrefix E.production.loweredDecl := by
    have h := E.assembly.constructorArityPrefix
    rw [E.production_eq] at h
    exact h
  have Horigins := E.assembly.productionInductiveOrigins Hlower
    E.productionContextWF Hproduction Hmetadata Hsources Harity Howners hempty
      E.productionContext_env E.productionContext_lparams rfl
  exact E.assembly.constructorSemanticsOfParameterDomains wf Horigins Hparams

end VerifyInductive
end Lean4Lean
