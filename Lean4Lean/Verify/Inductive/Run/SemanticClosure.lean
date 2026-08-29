import Lean4Lean.Verify.Inductive.Run.SemanticFormation
import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The source-aligned metadata retained by a skeleton-free header result is
enough to close the newly installed mutual block.  This proof uses the
lockstep installation certificate, not a replay of the executable header
fold. -/
theorem DeclaredHeadersResult.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (Hclosed : MutualInductivesClosed c.env) :
    MutualInductivesClosed headerEnv := by
  rcases H.production with ⟨numNested, hproduction⟩
  let infos := (AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams).toList
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.translation.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, H.materialized.indices,
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

/-- Skeleton-free header and constructor formation with the persistent
production mutual-family lookup invariant attached to the same successful
execution. -/
theorem AddInductive.semanticFormationCoreClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
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
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ decl headerEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ _ : ConstructorPhasesResult Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  have Hformation := AddInductive.semanticFormationCoreWF Hsemantic
    hlevels hlevelParams hindicesSize hindices hconsts hparams
    hcommonParams Hcache Hsuffix Hambient hcommon hvisible hnprimTypes
    hconsume hnprimCtors
  intro outEnv hout
  rcases Hformation outEnv hout with ⟨decl, headerEnv, Hheaders, R, _⟩
  have hclosedHeaders := Hheaders.closesMutuals Hclosed
  exact ⟨decl, headerEnv, Hheaders, R,
    R.declared.closesMutuals hclosedHeaders⟩

end VerifyInductive
end Lean4Lean
