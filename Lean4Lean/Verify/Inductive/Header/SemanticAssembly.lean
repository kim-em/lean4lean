import Lean4Lean.Verify.Inductive.Header.LoopInd
import Lean4Lean.Verify.Inductive.Header.SemanticMaterialization
import Lean4Lean.Verify.Inductive.Constructor.ExistentialTargets
import Lean4Lean.Verify.Inductive.Specification.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Final declaration assembled after the installed header environment has
made it possible to translate constructor types.  The semantic prefix is
retained alongside the ordinary header translation so nested lowering can
still project each exact normalized source telescope. -/
structure AssembledSemanticHeaders
    (env envTypes : VEnv) (Us : List Name) (nparams : Nat)
    (sources : List InductiveType) (isUnsafe : Bool)
    (params : List VExpr) (commonLevel : VLevel) where
  skeleton : VInductDeclSkeleton
  decl : VInductDecl
  skeletonTranslation : TrInductDeclSkeletonHeaders env Us nparams sources
    isUnsafe skeleton envTypes
  metadata : List (Nat × VLevel)
  materialized : skeleton.materialize metadata = some decl
  semanticPrefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
    env Us skeleton params commonLevel metadata skeleton.types.length
  translation : TrInductDeclHeaders env Us nparams sources isUnsafe decl
    envTypes
  headers : HeaderCertificate env decl
  headers_eq : headers = semanticPrefix.complete materialized

/-- Final semantic assembly together with the exact header target list from
which it was built.  Keeping this equality at the assembly boundary lets the
production installer be reused without reconstructing target uniqueness. -/
structure AssembledSemanticHeadersOf
    (env envTypes : VEnv) (Us : List Name) (nparams : Nat)
    (sources : List InductiveType) (isUnsafe : Bool)
    (params : List VExpr) (commonLevel : VLevel)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        env Us nparams params commonLevel sources)
    extends AssembledSemanticHeaders env envTypes Us nparams sources isUnsafe
      params commonLevel where
  typeConstants : decl.typeConstants = Hsemantic.headers.targets
  metadata_eq : metadata = Hsemantic.metadata

/-- Join the skeleton-free semantic header traversal with the skeleton-free
constructor target traversal.  The only installation premise is precisely
the equation produced by `semanticHeadersWF`. -/
theorem AssembledSemanticHeaders.ofTargetsExact
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        env Us nparams params commonLevel sources)
    (Hconstructors : CheckedSourceConstructorRows envTypes Us sources)
    (hparams : params.length = nparams)
    (htypesAdded : env.addConstVals Hsemantic.headers.targets =
      some envTypes) :
    Nonempty (AssembledSemanticHeadersOf env envTypes Us nparams sources
      isUnsafe params commonLevel Hsemantic) := by
  let skeleton : VInductDeclSkeleton := {
    uvars := Us.length
    nparams := nparams
    types := assembleInductiveSkeletonTypes Hsemantic.headers.targets
      Hconstructors.targets
    isUnsafe := isUnsafe }
  have htypeConstants : skeleton.typeConstants =
      Hsemantic.headers.targets := by
    change (assembleInductiveSkeletonTypes Hsemantic.headers.targets
      Hconstructors.targets).map
        VInductiveTypeSkeleton.toVConstVal = Hsemantic.headers.targets
    exact assembleInductiveSkeletonTypes_headers
      Hsemantic.headers.translations Hconstructors.translations
  have Hskeleton : TrInductDeclSkeletonHeaders env Us nparams sources
      isUnsafe skeleton envTypes := {
    uvars := rfl
    nparams := rfl
    isUnsafe := rfl
    typesAdded := by simpa [htypeConstants] using htypesAdded
    types := assembleInductiveSkeletonTypes_translated
      Hsemantic.headers.translations Hconstructors.translations }
  have Hprefix := Hsemantic.toSynthesizedPrefix skeleton rfl rfl
    (by simpa [skeleton] using hparams) htypeConstants
  have hmetadataLength : Hsemantic.metadata.length =
      skeleton.types.length := by
    have hpayloadLength : Hsemantic.payloads.length = sources.length := by
      simpa using congrArg List.length Hsemantic.sourceOrder
    have hheaderLength : Hsemantic.headers.targets.length = sources.length :=
      (Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
        Hsemantic.headers.translations).symm
    have hconstructorLength : Hconstructors.targets.length = sources.length :=
      (Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
        Hconstructors.translations).symm
    simp [checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.metadata,
      skeleton, assembleInductiveSkeletonTypes, hpayloadLength,
      hheaderLength, hconstructorLength]
  let decl : VInductDecl := {
    uvars := skeleton.uvars
    nparams := skeleton.nparams
    types := List.zipWith (fun type data =>
      type.toVInductiveType data.1 data.2) skeleton.types Hsemantic.metadata
    isUnsafe := skeleton.isUnsafe }
  have Hmaterialized : skeleton.materialize Hsemantic.metadata =
      some decl := by
    simp [VInductDeclSkeleton.materialize, hmetadataLength, decl]
  let A : AssembledSemanticHeaders env envTypes Us nparams sources isUnsafe
      params commonLevel := {
    skeleton := skeleton
    decl := decl
    skeletonTranslation := Hskeleton
    metadata := Hsemantic.metadata
    materialized := Hmaterialized
    semanticPrefix := Hprefix
    translation :=
      Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.materialized
        Hskeleton Hmaterialized
    headers := Hprefix.complete Hmaterialized
    headers_eq := rfl }
  refine ⟨{
    toAssembledSemanticHeaders := A
    typeConstants := ?_
    metadata_eq := rfl }⟩
  calc
      A.decl.typeConstants = A.skeleton.typeConstants := by
        rw [← VInductDecl.toSkeleton_typeConstants A.decl,
          VInductDeclSkeleton.materialize_toSkeleton A.materialized]
      _ = Hsemantic.headers.targets := htypeConstants

/-- Compatibility projection when only the assembled declaration is needed. -/
theorem AssembledSemanticHeaders.ofTargets
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        env Us nparams params commonLevel sources)
    (Hconstructors : CheckedSourceConstructorRows envTypes Us sources)
    (hparams : params.length = nparams)
    (htypesAdded : env.addConstVals Hsemantic.headers.targets =
      some envTypes) :
    Nonempty (AssembledSemanticHeaders env envTypes Us nparams sources
      isUnsafe params commonLevel) := by
  rcases AssembledSemanticHeaders.ofTargetsExact Hsemantic Hconstructors
      hparams htypesAdded with ⟨H⟩
  exact ⟨H.toAssembledSemanticHeaders⟩

/-- The metadata used to materialize a declaration is exactly the resulting
per-family index-count vector.  This is the declaration-wide counterpart of
`materialize_typeAt`, factored out of the old traversal terminal case so the
skeleton-free assembly path can reuse it. -/
theorem VInductDeclSkeleton.materialize_numIndices
    {skeleton : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {decl : VInductDecl}
    (H : skeleton.materialize metadata = some decl) :
    metadata.map Prod.fst = decl.types.map (·.numIndices) := by
  have zipIndices : ∀ (types : List VInductiveTypeSkeleton)
      (data : List (Nat × VLevel)), data.length = types.length →
      (List.zipWith (fun type datum =>
        type.toVInductiveType datum.1 datum.2) types data).map
          (·.numIndices) = data.map Prod.fst := by
    intro types data hlength
    induction types generalizing data with
    | nil => simpa using hlength
    | cons type types ih =>
      cases data with
      | nil => simp at hlength
      | cons datum data =>
        simp only [List.length_cons] at hlength
        change datum.1 ::
            (List.zipWith (fun type datum =>
              type.toVInductiveType datum.1 datum.2)
              types data).map (·.numIndices) =
            datum.1 :: data.map Prod.fst
        exact congrArg (List.cons datum.1) (ih data (by omega))
  have hlength := VInductDeclSkeleton.materialize_length H
  simp only [VInductDeclSkeleton.materialize] at H
  split at H
  · simp only [Option.some.injEq] at H
    subst decl
    exact (zipIndices skeleton.types metadata hlength).symm
  · contradiction

/-- A translated declaration skeleton preserves family names in source
order, independently of its constructor rows. -/
theorem TrInductDeclSkeletonHeaders.typeNames
    (H : TrInductDeclSkeletonHeaders env Us nparams sources isUnsafe
      skeleton envTypes) :
    skeleton.types.map (·.name) = sources.map (·.name) := by
  have go : ∀ {sourceTypes : List InductiveType}
      {targetTypes : List VInductiveTypeSkeleton},
      List.Forall₂ (TrInductiveTypeSkeletonHeaders env envTypes Us)
        sourceTypes targetTypes →
      targetTypes.map (·.name) = sourceTypes.map (·.name) := by
    intro sourceTypes targetTypes Htypes
    induction Htypes with
    | nil => rfl
    | cons Htype _ ih =>
      simp [Htype.header.name, ih]
  exact go H.types

/-- Repackage a completed skeleton-free semantic traversal in the established
`MaterializedHeaderResult` interface.  All executable statistics and context
facts are supplied by the outer fold; the declaration, header certificate and
normalized source telescopes come solely from semantic assembly. -/
def AssembledSemanticHeaders.materializedResult
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : AssembledSemanticHeaders Hc.venv envTypes c.lparams nparams
      sources isUnsafe params commonLevel)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (sources.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc params depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx
      stats H.decl depth := by
  have hfields := VInductDeclSkeleton.materialize_fields H.materialized
  have herase := VInductDeclSkeleton.materialize_toSkeleton H.materialized
  refine {
    headers := H.semanticPrefix.complete H.materialized
    normalizedSources :=
      H.semanticPrefix.normalizedSourceAtMaterialized H.materialized
    commonLevel := hcommon
    levels := ?_
    levelParams := hlevelParams
    uvars := ?_
    consts := ?_
    indices := hindices.trans
      (VInductDeclSkeleton.materialize_numIndices H.materialized)
    params := ?_
    paramFVars := Hcache.paramFVars
    parameterScope := Hsuffix.parameterDecls
    ambientScope := Hsuffix.ambientDecls
    scopeDecomposition := Hsuffix.context
    ambientLength := Hsuffix.prefixLength
    cachedScope := Hsuffix.cached
    runtimeScope :=
      checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
        Hc Hsuffix
    paramsContext := ?_
    narrowParams := ?_ }
  · exact hlevels.trans
      (H.skeletonTranslation.uvars.symm.trans hfields.1.symm)
  · exact H.skeletonTranslation.uvars.symm.trans hfields.1.symm
  · have hconstMap :
        (H.decl.types.map fun type => Expr.const type.name stats.levels) =
          (H.skeleton.types.map fun type =>
            Expr.const type.name stats.levels) := by
      have h := congrArg (fun d : VInductDeclSkeleton =>
        d.types.map fun type => Expr.const type.name stats.levels) herase
      simpa [VInductDecl.toSkeleton, VInductiveType.toSkeleton,
        Function.comp_def] using h
    calc
      stats.indConsts =
          (sources.map fun source =>
            .const source.name stats.levels).toArray := hconsts
      _ = (H.skeleton.types.map fun type =>
            .const type.name stats.levels).toArray := by
        have hnames :=
          Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeNames
            H.skeletonTranslation
        have h := congrArg (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
          hnames.symm
        simpa [List.map_map, Function.comp_def] using h
      _ = (H.decl.types.map fun type =>
            .const type.name stats.levels).toArray := by rw [hconstMap]
  · have Hcache' : checkInductiveTypes.loopType.ParameterCachePrefix
        Hc.venv c.lparams Hc.mlctx.vlctx stats H.decl.nparams depth := by
      rw [hfields.2.1, H.skeletonTranslation.nparams]
      exact Hcache
    exact Hcache'.complete
  · apply Hsuffix.paramsDefEq Hambient
    exact H.semanticPrefix.parameterCount.trans
      (H.skeletonTranslation.nparams.trans hparams.symm)
  · rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars H.decl]
    have hsize : stats.params.size = H.decl.nparams :=
      hparams.trans
        (H.skeletonTranslation.nparams.symm.trans hfields.2.1.symm)
    simpa [hsize] using Hsuffix.narrowParams

end VerifyInductive
end Lean4Lean
