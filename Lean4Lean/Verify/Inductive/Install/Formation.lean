import Lean4Lean.Verify.Inductive.Install.Headers
import Lean4Lean.Verify.Inductive.Install.LiteralNames
import Lean4Lean.Verify.Inductive.Install.Metadata

/-! Skeleton-free formation: the header installation, the constructor check and
the constructor installation, composed for the declaration that these
executable traversals themselves synthesize, together with closure of the
installed mutual block. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Header installation, the constructor checker, and constructor
installation composed from the declaration synthesized by those same
executable traversals.  Unlike `formationCore.headersWF`, neither the
declaration nor its header translation is a caller input. -/
theorem AddInductive.formationCoreWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c.lparams.Nodup)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) c.env)
    (hpresent : ListedConstructorsPresent c.env) :
    ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ decl headerEnv,
        ∃ Hheaders : HeaderEnvironment c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ _ : OrdinaryConstructorCheck Hheaders outEnv, True := by
  have HheadersAndLoop :=
    AddInductive.declareInductiveTypes.constructorsWF
      Hsemantic hlevels hlevelParams hindicesSize hindices hconsts hparams
      hcommonParams Hcache Hsuffix Hambient hcommon hnotzero hvisible hnprimTypes
      hconsume hlparams hpresent
  have Hcombined :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun outEnv =>
        ∃ decl headerEnv,
          ∃ Hheaders : HeaderEnvironment c stats decl nparams
            isUnsafe depth Hc.venv indTypes headerEnv,
          ∃ _ : OrdinaryConstructorCheck Hheaders outEnv, True :=
    HheadersAndLoop.bind fun headerEnv ⟨hheaderWF, Hloop⟩ => by
    change ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
        { c with env := headerEnv }).WF _
    intro outEnvFinal houtFinal
    -- The constructor names are checked fresh only when the constructors are declared, after
    -- their types are checked; that check succeeding is what makes the header environment,
    -- in which the types are checked, list no present constant.
    have hfresh : ConstructorNamesAbsent indTypes headerEnv := by
      change (AddInductive.checkConstructors indTypes stats isUnsafe
        { c with env := headerEnv } >>= fun _ =>
          AddInductive.declareConstructors stats indTypes isUnsafe
            { c with env := headerEnv }) = .ok outEnvFinal at houtFinal
      cases hcheck : AddInductive.checkConstructors indTypes stats isUnsafe
          { c with env := headerEnv } with
      | error e => rw [hcheck] at houtFinal; cases houtFinal
      | ok u =>
        rw [hcheck] at houtFinal
        exact AddInductive.declareConstructors.namesAbsent
          (c := { c with env := headerEnv }) hheaderWF outEnvFinal houtFinal
    have Hloop := Hloop hfresh
    have Hcheck :
        (AddInductive.checkConstructors indTypes stats isUnsafe
          { c with env := headerEnv }).WF fun _ =>
            ∃ decl,
            ∃ Hheaders : HeaderEnvironment c stats decl nparams
              isUnsafe depth Hc.venv indTypes headerEnv,
              CheckedConstructors Hc.venv decl Hheaders.context.venv
                  Hheaders.headers.params stats indTypes c.lparams
                  Hheaders.statsWF.parameterScope /\
                ConstructorOwnerNormalForms stats indTypes ∧
                SourceCtorsCertified Hheaders.context.venv c.lparams indTypes.toList := by
      intro checkedOut hfull
      have hcheckedOut : AddInductive.checkConstructors.loopTypes indTypes stats
          isUnsafe 0 { headerCheckContext c stats with env := headerEnv } = .ok checkedOut :=
        hfull
      rcases Hloop checkedOut hcheckedOut with ⟨decl, ⟨Hheaders⟩⟩
      have hlitInstalled := Hheaders.checkedAvailableLiteralDisjoint
      have Hchecked := AddInductive.checkConstructors.checkedWF Hheaders
        hconsume hlitInstalled
        (fun h => Hheaders.translation.isUnsafe.trans h) hlparams
        checkedOut hfull
      have Howners :=
        AddInductive.checkConstructors.ownerNormalFormsWF Hheaders
          hconsume hlitInstalled
          checkedOut hfull
      have Htele := AddInductive.checkConstructors.telescopesWF Hheaders
        (Hheaders.installed.envGhostFree Hc.checking.tr.map_wf henv
          (Hheaders.entriesNoRecursor))
        checkedOut hfull
      exact ⟨decl, Hheaders, Hchecked, Howners, Htele⟩
    have Hphases :
        ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
          AddInductive.declareConstructors stats indTypes isUnsafe)
            { c with env := headerEnv }).WF fun outEnv =>
              ∃ decl,
              ∃ Hheaders : HeaderEnvironment c stats decl nparams
                isUnsafe depth Hc.venv indTypes headerEnv,
              ∃ _ : OrdinaryConstructorCheck Hheaders outEnv, True :=
      Hcheck.bind fun _ Hchecked => by
      rcases Hchecked with ⟨decl, Hheaders, Hchecked, Howners, Htele⟩
      exact (AddInductive.declareConstructors.WF Hheaders
        Hchecked hvisible hnprimCtors Htele).mono fun outEnv Hdeclared => by
          rcases Hdeclared with ⟨Hdeclared, _⟩
          let R : OrdinaryConstructorCheck Hheaders outEnv := {
            checked := Hchecked.checked
            parameterPrefixes := Hchecked.parameterPrefixes
            constructorTails := Hchecked.constructorTails
            ownerNormalForms := Howners
            telescopes := Htele
            declared := Hdeclared
            formation := Hheaders.formation Hchecked
            core := Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases
              Hheaders.translation Hdeclared.translation }
          exact ⟨decl, Hheaders, R, trivial⟩
    have Hphases' :
        ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
          AddInductive.declareConstructors stats indTypes isUnsafe)
            { c with env := headerEnv }).WF fun outEnv =>
          ∃ decl headerEnv',
            ∃ Hheaders : HeaderEnvironment c stats decl nparams
              isUnsafe depth Hc.venv indTypes headerEnv',
            ∃ _ : OrdinaryConstructorCheck Hheaders outEnv, True := by
      intro outEnv hout
      have Hresult := Hphases outEnv hout
      rcases Hresult with ⟨decl, Hheaders, R, _⟩
      exact ⟨decl, headerEnv, Hheaders, R, trivial⟩
    exact Hphases' outEnvFinal houtFinal
  exact Hcombined

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The source-aligned metadata retained by a skeleton-free header result is
enough to close the newly installed mutual block.  This proof uses the
lockstep installation certificate, not a replay of the executable header
fold. -/
theorem HeaderEnvironment.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (Hclosed : MutualInductivesClosed c.env) :
    MutualInductivesClosed headerEnv := by
  rcases H.infos with ⟨numNested, hproduction⟩
  let infos := (AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams).toList
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using
      List.Forall₂.length_eq H.translation.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, H.statsWF.indices,
      List.length_map]
    exact htypesLength.symm
  have huniform : ∀ info ∈ infos,
      info.all = infos.map (fun member => member.name) := by
    simpa [infos] using inductiveTypeInfos_uniformAll stats nparams indTypes
      numNested isUnsafe c.lparams hsize
  have hlookup : ∀ info ∈ infos,
      headerEnv.find? info.name = some (.inductInfo info) := by
    intro info hinfo
    have hconstant : ConstantInfo.inductInfo info ∈ H.entries.map Prod.fst := by
      rw [hproduction]
      exact List.mem_map.mpr ⟨info, hinfo, rfl⟩
    rcases List.mem_map.mp hconstant with ⟨entry, hentry, hentryInfo⟩
    rcases entry with ⟨entryInfo, entryValue⟩
    change entryInfo = ConstantInfo.inductInfo info at hentryInfo
    have hfound := H.installed.findOfMem H.sourceContext.checking.tr.map_wf
      (info := entryInfo) (value := entryValue) hentry
    rw [hentryInfo] at hfound
    exact hfound
  have Hmembers : InductiveMemberInfos headerEnv
      (infos.map fun info => info.name) := by
    have go : ∀ members : List InductiveVal,
        (∀ info ∈ members,
          headerEnv.find? info.name = some (.inductInfo info)) →
        InductiveMemberInfos headerEnv
          (members.map fun info => info.name) := by
      intro members
      induction members with
      | nil => exact fun _ => .nil
      | cons info members ih =>
          intro hall
          exact .cons (hall info (by simp))
            (ih fun member hmember => hall member (by simp [hmember]))
    exact go infos hlookup
  have hentryNames :
      H.entries.map (fun entry => entry.1.name) =
        H.entries.map (fun entry => entry.2.name) := by
    apply List.map_congr_left
    intro entry hentry
    exact H.installed.entryNames hentry
  have hinfosNames : infos.map (fun info => info.name) =
      H.entries.map (fun entry => entry.1.name) := by
    calc
      infos.map (fun info => info.name) =
          (infos.map (fun info => ConstantInfo.inductInfo info)).map
            ConstantInfo.name := by
        rw [List.map_map]
        apply List.map_congr_left
        intro info _
        rfl
      _ = (H.entries.map Prod.fst).map ConstantInfo.name :=
        congrArg (List.map ConstantInfo.name) hproduction.symm
      _ = H.entries.map (fun entry => entry.1.name) := by
        simp [List.map_map, Function.comp_def]
  have hnames : (infos.map fun info => info.name).Nodup := by
    rw [hinfosNames, hentryNames]
    simpa [List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup H.installed.abstract
  intro targetName value hfind
  rcases H.installed.origin H.sourceContext.checking.tr.map_wf hfind with
      hold | hnew
  · have Hsource := Hclosed targetName value hold
    have hpreserves : ∀ {name found},
        c.env.find? name = some found →
          headerEnv.find? name = some found := by
      intro name found hfound
      exact H.installed.preservesFind H.sourceContext.checking.tr.map_wf
        hfound
    refine ⟨Hsource.members.mapEnvironment hpreserves,
      Hsource.target, Hsource.names, ?_⟩
    intro member info hmember hfindMember
    rcases Hsource.members.find hmember with ⟨sourceInfo, hsourceInfo⟩
    have htargetInfo := hpreserves hsourceInfo
    have hinfo : info = sourceInfo := by
      rw [hfindMember] at htargetInfo
      exact ConstantInfo.inductInfo.inj (Option.some.inj htargetInfo)
    subst info
    exact Hsource.parameters member sourceInfo hmember hsourceInfo
  · rcases hnew with ⟨entry, hentry, hname, hvalue⟩
    have hconstant : entry.1 ∈ H.entries.map Prod.fst :=
      List.mem_map.mpr ⟨entry, hentry, rfl⟩
    rw [hproduction] at hconstant
    rcases List.mem_map.mp hconstant with ⟨info, hinfo, hentryInfo⟩
    have hvalueInfo : value = info := by
      have hconstantEq : ConstantInfo.inductInfo value =
          ConstantInfo.inductInfo info := hvalue.trans hentryInfo.symm
      cases hconstantEq
      rfl
    subst value
    have hentryName : entry.1.name = info.name := by
      exact (congrArg ConstantInfo.name hentryInfo).symm
    refine ⟨by simpa [huniform info hinfo] using Hmembers,
      by
        rw [hname, hentryName, huniform info hinfo]
        exact List.mem_map.mpr ⟨info, hinfo, rfl⟩,
      by simpa [huniform info hinfo] using hnames, ?_⟩
    intro member memberInfo hmember hfindMember
    have hmember' : member ∈ infos.map (fun candidate => candidate.name) := by
      simpa only [huniform info hinfo] using hmember
    rcases List.mem_map.mp hmember' with
      ⟨candidate, hcandidate, hcandidateName⟩
    have hcandidateLookup := hlookup candidate hcandidate
    rw [hcandidateName] at hcandidateLookup
    have hmemberInfo : memberInfo = candidate := by
      rw [hfindMember] at hcandidateLookup
      exact ConstantInfo.inductInfo.inj (Option.some.inj hcandidateLookup)
    subst memberInfo
    have hcandidateParams := inductiveTypeInfos_uniformNumParams stats
      nparams indTypes numNested isUnsafe c.lparams hsize candidate (by
        simpa [infos] using hcandidate)
    have hinfoParams := inductiveTypeInfos_uniformNumParams stats nparams
      indTypes numNested isUnsafe c.lparams hsize info (by
        simpa [infos] using hinfo)
    exact hcandidateParams.trans hinfoParams.symm

/-- Skeleton-free header and constructor formation together with the
mutual-family lookup invariant of the kernel environment, for the same
successful execution. -/
theorem AddInductive.formationCoreClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hclosed : MutualInductivesClosed c.env)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c.lparams.Nodup)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) c.env)
    (hpresent : ListedConstructorsPresent c.env) :
    ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ decl headerEnv,
        ∃ Hheaders : HeaderEnvironment c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ _ : OrdinaryConstructorCheck Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  have Hformation := AddInductive.formationCoreWF Hsemantic
    hlevels hlevelParams hindicesSize hindices hconsts hparams
    hcommonParams Hcache Hsuffix Hambient hcommon hnotzero hvisible hnprimTypes
    hconsume hnprimCtors hlparams henv hpresent
  intro outEnv hout
  rcases Hformation outEnv hout with ⟨decl, headerEnv, Hheaders, R, _⟩
  have hclosedHeaders := Hheaders.closesMutuals Hclosed
  exact ⟨decl, headerEnv, Hheaders, R,
    R.declared.closesMutuals hclosedHeaders⟩

end VerifyInductive
end Lean4Lean
