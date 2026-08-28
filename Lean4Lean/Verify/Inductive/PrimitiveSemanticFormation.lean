import Lean4Lean.Verify.Inductive.PrimitiveSemanticWitnesses
import Lean4Lean.Verify.Inductive.Run.SemanticHeaders

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Package skeleton-free semantic assembly against an atomic primitive
header installation.  The resulting context remains staged until constructor
installation completes the bootstrap batch. -/
def AssembledSemanticHeadersOf.primitiveDeclaredResult
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {envTypes : VEnv} {outEnv : Environment}
    (Hinstalled : AtomicAddConstants c.safety c.env Hc.venv
      (List.zip
        ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
          isUnsafe c.lparams).toList.map (fun info => .inductInfo info))
        Hsemantic.headers.targets)
      outEnv envTypes)
    (H : AssembledSemanticHeadersOf Hc.venv envTypes c.lparams nparams
      indTypes.toList isUnsafe commonParams commonLevel Hsemantic)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel) :
    PrimitiveDeclaredHeadersResult c stats H.decl nparams isUnsafe depth
      Hc.venv indTypes outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  let entries : List (ConstantInfo × VConstVal) :=
    List.zip (infos.toList.map fun info => .inductInfo info)
      Hsemantic.headers.targets
  have hmetadataLength : H.metadata.length = indTypes.toList.length := by
    calc
      H.metadata.length = H.skeleton.types.length :=
        VInductDeclSkeleton.materialize_length H.materialized
      _ = indTypes.toList.length :=
        (TrInductDeclSkeletonHeaders.types_length
          H.skeletonTranslation).symm
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = stats.nindices.toList.length := by simp
      _ = (H.metadata.map Prod.fst).length := congrArg List.length hindices
      _ = H.metadata.length := by simp
      _ = indTypes.toList.length := hmetadataLength
      _ = indTypes.size := by simp
  have hsourceLength : indTypes.toList.length =
      Hsemantic.headers.targets.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hsemantic.headers.translations
  have hinfosLength : infos.toList.length =
      Hsemantic.headers.targets.length := by
    calc
      infos.toList.length = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      _ = indTypes.toList.length := by simp
      _ = Hsemantic.headers.targets.length := hsourceLength
  have hentriesFst : entries.map Prod.fst =
      infos.toList.map (fun info => ConstantInfo.inductInfo info) := by
    apply List.map_fst_zip
    simpa using Nat.le_of_eq hinfosLength
  have hentriesSnd : entries.map Prod.snd =
      Hsemantic.headers.targets := by
    apply List.map_snd_zip
    simpa using Nat.le_of_eq hinfosLength.symm
  let sourceMaterialized :=
    H.toAssembledSemanticHeaders.materializedResult hlevels hlevelParams
      hindices hconsts hparams Hcache Hsuffix Hambient hcommon
  have hsourceHeaders : sourceMaterialized.headers = H.headers := by
    change H.semanticPrefix.complete H.materialized = H.headers
    exact H.headers_eq.symm
  let context : StagedContextWF { c with env := outEnv } :=
    Hc.toStaged.withEnv (venv' := envTypes)
      (Hinstalled.checking Hc.checking.tr) Hinstalled.le
  have hcontextVEnv : context.venv = envTypes := rfl
  have hle : Hc.venv ≤ context.venv := Hinstalled.le
  let materializedMono := sourceMaterialized.mono hle
  have hscope : Hc.mlctx.vlctx = context.mlctx.vlctx := rfl
  let materialized := materializedMono.retargetScope hscope
  exact {
    entries := entries
    production := ⟨numNested, by simpa [infos] using hentriesFst⟩
    sourceAligned := ⟨numNested, by
      change InductiveHeaderEntries infos.toList entries
      exact InductiveHeaderEntries.ofZip hinfosLength⟩
    values := hentriesSnd.trans H.typeConstants.symm
    context := context
    headers := H.headers
    translation := by rw [hcontextVEnv]; exact H.translation
    installed := by rw [hcontextVEnv]; simpa [entries, infos] using Hinstalled
    sourceContext := Hc
    sourceContextVEnv := rfl
    sourceMaterialized := sourceMaterialized
    materialized := materialized
    headerParams := by
      calc
        materialized.headers.params = materializedMono.headers.params := by
          simpa [materialized] using
            checkInductiveTypes.loopInd.MaterializedHeaderResult.retargetScope_headers_params
              materializedMono hscope
        _ = sourceMaterialized.headers.params :=
          checkInductiveTypes.loopInd.MaterializedHeaderResult.mono_headers_params
            sourceMaterialized hle
        _ = H.headers.params := congrArg (fun headers => headers.params)
          hsourceHeaders }

/-- Primitive header installation with the declaration synthesized from the
successful semantic header fold and the finite canonical constructor rows.
No caller-provided skeleton or header translation remains. -/
theorem AddInductive.declareInductiveTypes.primitiveSemanticHeadersWF
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
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ decl, ∃ envTypes : VEnv,
          ∃ Hheaders : PrimitiveDeclaredHeadersResult c stats decl nparams
            isUnsafe depth Hc.venv indTypes outEnv, True := by
  have Hinstall :=
    AddInductive.declareInductiveTypes.installsSemanticHeadersAtomicWF
      (numNested := numNested) Hc Hsemantic hindicesSize hvisible
  exact Hinstall.mono fun outEnv Hresult => by
    rcases Hresult with ⟨envTypes, htypesAdded, Hatomic⟩
    rcases Hshape.checkedConstructorRows Hsemantic htypesAdded with
      ⟨Hconstructors⟩
    rcases AssembledSemanticHeaders.ofTargetsExact (isUnsafe := isUnsafe)
      Hsemantic Hconstructors hcommonParams htypesAdded with ⟨A⟩
    have hindices' : stats.nindices.toList = A.metadata.map Prod.fst := by
      rw [A.metadata_eq]
      exact hindices
    let Hheaders := A.primitiveDeclaredResult Hatomic hlevels hlevelParams
      hindices' hconsts hparams Hcache Hsuffix Hambient hcommon
    exact ⟨A.decl, envTypes, Hheaders, trivial⟩

end VerifyInductive
end Lean4Lean
