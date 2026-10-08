import Lean4Lean.Verify.Inductive.Header.Translation
import Lean4Lean.Verify.Inductive.Header.Block

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopType

def headerSkeleton (target : VConstVal) : VInductiveTypeSkeleton where
  toVConstVal := target
  ctors := []

/-- Constructor payloads are irrelevant to header formation.  A synthesized
header can therefore be attached to the final skeleton once its constructor
targets have been recovered. -/
theorem SynthesizedHeader.retarget
    (H : SynthesizedHeader env Us uvars nparams params source
      nindices resultLevel)
    (htarget : target.toVConstVal = source.toVConstVal) :
    SynthesizedHeader env Us uvars nparams params target
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := H.levelCount
  normalizedSource := H.normalizedSource
  normalizedShape := by
    rcases source with ⟨sourceVal, sourceCtors⟩
    rcases target with ⟨targetVal, targetCtors⟩
    simp only at htarget
    subst targetVal
    exact H.normalizedShape
  typeShape decl huvars hnparams := by
    have Hshape := H.typeShape decl huvars hnparams
    rcases source with ⟨sourceVal, sourceCtors⟩
    rcases target with ⟨targetVal, targetCtors⟩
    simp only at htarget
    subst targetVal
    exact Hshape

/-- One source-aligned semantic header payload.  Its constructor list is
deliberately empty; `retarget` attaches the same proof to the final
constructor-bearing skeleton. -/
structure MaterializedSourceHeaderSemantics
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : InductiveType) where
  target : VConstVal
  numIndices : Nat
  resultLevel : VLevel
  translation : TrSourceConst env Us source.name source.type target
  synthesized : SynthesizedHeader env Us Us.length nparams params
    (headerSkeleton target) numIndices resultLevel
  commonLevel : resultLevel ≈ commonLevel

def MaterializedSourceHeaderSemantics.headerType
    (H : MaterializedSourceHeaderSemantics env Us nparams params
      commonResultLevel source) : VInductiveType :=
  (headerSkeleton H.target).toVInductiveType H.numIndices H.resultLevel

/-- Ordered semantic outputs of the skeleton-free mutual-header traversal. -/
structure MaterializedSourceHeaderSemanticAccumulator
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (sources : List InductiveType) where
  payloads : List (Sigma fun source =>
    MaterializedSourceHeaderSemantics env Us nparams params commonLevel source)
  sourceOrder : payloads.map Sigma.fst = sources

namespace MaterializedSourceHeaderSemanticAccumulator

/-- Retarget only the source-list index along an exact ordering equality.
The semantic payloads themselves are copied definitionally, so projections
such as `metadata` remain reducible across the reindexing. -/
def reindexSources
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (h : sources = sources') :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources' where
  payloads := H.payloads
  sourceOrder := H.sourceOrder.trans h

/-- Retarget universe-parameter names along equality without changing any
recovered semantic data. -/
def reindexUs
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (h : Us = Us') :
    MaterializedSourceHeaderSemanticAccumulator env Us' nparams params
      commonLevel sources := by
  cases h
  exact H

def first (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel) :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      resultLevel [source] where
  payloads := [⟨source, target, numIndices, resultLevel, Htranslation,
    Hsynthesized, by rfl⟩]
  sourceOrder := rfl

def snoc
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel (sources ++ [source]) where
  payloads := H.payloads ++ [⟨source, target, numIndices, resultLevel,
    Htranslation, Hsynthesized, hlevel⟩]
  sourceOrder := by simp [H.sourceOrder]

def headers
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    MaterializedSourceHeaderAccumulator env Us sources := by
  have go : ∀ payloads : List (Sigma fun source =>
      MaterializedSourceHeaderSemantics env Us nparams params commonLevel
        source),
      List.Forall₂
        (fun source target =>
          TrSourceConst env Us source.name source.type target)
        (payloads.map Sigma.fst)
        (payloads.map fun payload => payload.2.target) := by
    intro payloads
    induction payloads with
    | nil => exact .nil
    | cons payload payloads ih =>
      rcases payload with ⟨source, payload⟩
      exact .cons payload.translation ih
  refine {
    targets := H.payloads.map fun payload => payload.2.target
    translations := ?_ }
  exact Eq.mp (congrArg (fun orderedSources =>
    List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      orderedSources (H.payloads.map fun payload => payload.2.target))
    H.sourceOrder) (go H.payloads)

def metadata
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) : List (Nat × VLevel) :=
  H.payloads.map fun payload =>
    (payload.2.numIndices, payload.2.resultLevel)

@[simp] theorem metadata_reindexSources
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) (h : sources = sources') :
    (H.reindexSources h).metadata = H.metadata := rfl

@[simp] theorem metadata_reindexUs
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) (h : Us = Us') :
    (H.reindexUs h).metadata = H.metadata := by cases h; rfl

@[simp] theorem metadata_snoc
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (nindices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    (H.snoc source target nindices resultLevel Htranslation Hsynthesized
      hlevel).metadata = H.metadata ++ [(nindices, resultLevel)] := by
  simp [snoc, metadata]

/-- The header-phase declaration has the final family constants and semantic
metadata, but deliberately no constructor constants yet. -/
def headerDecl
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : VInductDecl where
  uvars := Us.length
  nparams := nparams
  types := H.payloads.map fun payload => payload.2.headerType
  isUnsafe := isUnsafe

@[simp] theorem headerDecl_typeConstants
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).typeConstants = H.headers.targets := by
  simp [headerDecl, VInductDecl.typeConstants,
    MaterializedSourceHeaderSemantics.headerType, headerSkeleton, headers]
  intro payload _hpayload
  rcases payload with ⟨source, payload⟩
  rfl

/-- The retained per-family synthesis proofs assemble directly into the
abstract header certificate for the header-only declaration.  In particular
each `normalizedSource` remains available through the originating payload. -/
def headerCertificate
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : HeaderCertificate env (H.headerDecl isUnsafe) where
  params := params
  resultLevel := commonLevel
  commonLevels type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.commonLevel
  typeShapes type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.synthesized.typeShape (H.headerDecl isUnsafe) rfl rfl

/-- Attach the semantic payloads to any constructor-bearing skeleton with
the same ordered header constants. -/
theorem toSynthesizedPrefix
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (skeleton : VInductDeclSkeleton)
    (huvars : skeleton.uvars = Us.length)
    (hnparams : skeleton.nparams = nparams)
    (hparams : params.length = skeleton.nparams)
    (htypes : skeleton.typeConstants = H.headers.targets) :
    SynthesizedHeaderPrefix env Us skeleton params commonLevel H.metadata
      skeleton.types.length := by
  have hpayloadLength : H.payloads.length = skeleton.types.length := by
    have hlength := congrArg List.length htypes
    simpa [VInductDeclSkeleton.typeConstants, headers] using hlength.symm
  refine {
    parameterCount := hparams
    covered := Nat.le_refl _
    checked := ?_ }
  apply List.forall₂_of_getElem
  · simp [metadata, hpayloadLength]
  · intro i hiType hiData
    have hiSkeleton : i < skeleton.types.length := by simpa using hiType
    have hiPayload : i < H.payloads.length := by
      simpa [hpayloadLength] using hiSkeleton
    let payload := H.payloads[i]
    have htarget : skeleton.types[i].toVConstVal = payload.2.target := by
      have hget := congrArg (fun values => values[i]?) htypes
      simp [VInductDeclSkeleton.typeConstants, headers, payload,
        hiPayload] at hget
      rcases hget with ⟨target, htarget, hvalue⟩
      rw [List.getElem?_eq_getElem hiSkeleton] at htarget
      have := Option.some.inj htarget
      subst target
      simpa [payload] using hvalue
    have hmetadata : H.metadata[i] =
        (payload.2.numIndices, payload.2.resultLevel) := by
      simp [metadata, payload, hiPayload]
    have Hheader := payload.2.synthesized.retarget htarget
    rw [hmetadata]
    exact {
      header := by simpa [huvars, hnparams] using Hheader
      commonLevel := payload.2.commonLevel }

end MaterializedSourceHeaderSemanticAccumulator

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- Retarget the runtime scope of a completed header result along exact
scope equality.  Data projections are preserved definitionally after
eliminating the equality, which avoids opaque dependent casts at installed
environment boundaries. -/
def MaterializedHeaderResult.retargetScope
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (h : Δ = Δ') : MaterializedHeaderResult env Us Δ' stats decl depth := by
  cases h
  exact H

@[simp] theorem MaterializedHeaderResult.retargetScope_headers_params
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).headers.params = H.headers.params := by
  cases h
  rfl

@[simp] theorem MaterializedHeaderResult.retargetScope_parameterScope
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).parameterScope = H.parameterScope := by
  cases h
  rfl

@[simp] theorem MaterializedHeaderResult.mono_parameterScope
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).parameterScope = H.parameterScope := rfl

@[simp] theorem MaterializedHeaderResult.mono_headers_params
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).headers.params = H.headers.params := rfl

end checkInductiveTypes.loopInd

namespace checkInductiveTypes.loopType

/-- Every source telescope retained by semantic accumulation is indexed by
the corresponding family of the header-only declaration. -/
theorem MaterializedSourceHeaderSemanticAccumulator.normalizedSourceAt
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < (H.headerDecl isUnsafe).types.length) :
    Nonempty (NormalizedHeaderSourceTelescope env Us params
      (H.headerDecl isUnsafe).nparams
      (H.headerDecl isUnsafe).types[i].numIndices) := by
  have hiPayload : i < H.payloads.length := by
    simpa [MaterializedSourceHeaderSemanticAccumulator.headerDecl] using hi
  let payload := H.payloads[i]
  simpa [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
    MaterializedSourceHeaderSemantics.headerType,
    VInductiveTypeSkeleton.toVInductiveType, payload, hiPayload] using
      payload.2.synthesized.normalizedSource

/-- The skeleton-free header fold retains the concrete source telescope and
its exact semantic family shape from the same checked replay. -/
theorem MaterializedSourceHeaderSemanticAccumulator.normalizedShapeAt
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < (H.headerDecl isUnsafe).types.length) :
    ∃ sourceTelescope : NormalizedHeaderSourceTelescope env Us params
        (H.headerDecl isUnsafe).nparams
        (H.headerDecl isUnsafe).types[i].numIndices,
      ∃ residual exprType,
        env.IsDefEq Us.length [] (H.headerDecl isUnsafe).types[i].type
          (VExpr.wrapForalls
            (sourceTelescope.ownParams ++ sourceTelescope.indices) residual)
          exprType ∧
        env.IsDefEq Us.length
          (sourceTelescope.indices.reverse ++
            sourceTelescope.ownParams.reverse)
          residual (.sort (H.headerDecl isUnsafe).types[i].resultLevel)
            (.sort (.succ (H.headerDecl isUnsafe).types[i].resultLevel)) := by
  have hiPayload : i < H.payloads.length := by
    simpa [MaterializedSourceHeaderSemanticAccumulator.headerDecl] using hi
  let payload := H.payloads[i]
  have htarget : (H.headerDecl isUnsafe).types[i] =
      payload.2.headerType := by
    simp [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
      payload, hiPayload]
  rw [htarget]
  simpa [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
    MaterializedSourceHeaderSemantics.headerType,
    VInductiveTypeSkeleton.toVInductiveType, headerSkeleton] using
      payload.2.synthesized.normalizedShape

/-- Recovered semantic metadata is exactly the index-count vector of the
header-only declaration. -/
theorem MaterializedSourceHeaderSemanticAccumulator.metadata_numIndices
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    H.metadata.map Prod.fst =
      (H.headerDecl isUnsafe).types.map (·.numIndices) := by
  simp [MaterializedSourceHeaderSemanticAccumulator.metadata,
    MaterializedSourceHeaderSemanticAccumulator.headerDecl,
    MaterializedSourceHeaderSemantics.headerType,
    VInductiveTypeSkeleton.toVInductiveType]

/-- Header-only family names remain in exact source order. -/
theorem MaterializedSourceHeaderSemanticAccumulator.headerDecl_names
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).types.map (·.name) =
      sources.map (·.name) := by
  calc
    (H.headerDecl isUnsafe).types.map (·.name) =
        H.payloads.map (fun payload => payload.2.target.name) := by
      simp [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
        MaterializedSourceHeaderSemantics.headerType,
        VInductiveTypeSkeleton.toVInductiveType, headerSkeleton]
    _ = H.payloads.map (fun payload => payload.1.name) := by
      apply List.map_congr_left
      intro payload _hpayload
      exact payload.2.translation.name
    _ = (H.payloads.map Sigma.fst).map (·.name) := by
      simp [List.map_map, Function.comp_def]
    _ = sources.map (·.name) := congrArg (List.map (·.name)) H.sourceOrder

@[simp] theorem MaterializedSourceHeaderSemanticAccumulator.headerDecl_types_length
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).types.length = sources.length := by
  simp [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
    ← H.sourceOrder]

/-- Pointwise exact header translation projected from semantic accumulation.
This is the constructor-phase lookup interface: it does not expose the
payload sigma representation. -/
theorem MaterializedSourceHeaderSemanticAccumulator.headerTranslationAt
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < sources.length) :
    TrSourceConst env Us sources[i].name sources[i].type
      ((H.headerDecl isUnsafe).types[i]'(by
        simpa using hi)).toVConstVal := by
  have hiPayload : i < H.payloads.length := by
    have hlength : H.payloads.length = sources.length := by
      simpa using congrArg List.length H.sourceOrder
    omega
  have hiDecl : i < (H.headerDecl isUnsafe).types.length := by
    simpa using hi
  let payload := H.payloads[i]
  have hsource : payload.1 = sources[i] := by
    have hget := congrArg (fun ordered => ordered[i]?) H.sourceOrder
    simp [payload, hiPayload, hi] at hget
    exact hget
  have htarget :
      ((H.headerDecl isUnsafe).types[i]'hiDecl).toVConstVal =
        payload.2.target := by
    simp [MaterializedSourceHeaderSemanticAccumulator.headerDecl,
      MaterializedSourceHeaderSemantics.headerType,
      VInductiveTypeSkeleton.toVInductiveType, headerSkeleton,
      payload, hiPayload]
  rw [← hsource, htarget]
  exact payload.2.translation

/-- The completed skeleton-free header fold already determines a fully
usable materialized header result before constructor targets are known.
Constructor checking can therefore run against this declaration and produce
those targets without circularly assuming a constructor-bearing skeleton. -/
def MaterializedSourceHeaderSemanticAccumulator.materializedResult
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : MaterializedSourceHeaderSemanticAccumulator Hc.venv c.lparams
      nparams params commonLevel sources)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (sources.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hparamsLength : params.length = nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (H.headerDecl isUnsafe) depth where
  headers := H.headerCertificate isUnsafe
  normalizedSources := H.normalizedSourceAt
  normalizedShapes := H.normalizedShapeAt
  isNotZero := hnotzero
  commonLevel := hcommon
  levels := hlevels
  levelParams := hlevelParams
  uvars := rfl
  consts := hconsts.trans <| by
    have hnames := H.headerDecl_names (isUnsafe := isUnsafe)
    have := congrArg (fun names =>
      (names.map fun name => Expr.const name stats.levels).toArray)
      hnames.symm
    simpa [List.map_map, Function.comp_def] using this
  indices := hindices.trans H.metadata_numIndices
  params := Hcache.complete
  paramFVars := Hcache.paramFVars
  parameterScope := Hsuffix.parameterDecls
  ambientScope := Hsuffix.ambientDecls
  scopeDecomposition := Hsuffix.context
  ambientLength := Hsuffix.prefixLength
  cachedScope := Hsuffix.cached
  runtimeScope := NarrowRuntimeScope.ofParameterSuffix Hc Hsuffix
  paramsContext := Hsuffix.paramsDefEq Hambient <|
    hparamsLength.trans hparams.symm
  narrowParams := by
    rw [← cachedParamVars_eq_paramVars (H.headerDecl isUnsafe)]
    simpa [hparams, MaterializedSourceHeaderSemanticAccumulator.headerDecl]
      using Hsuffix.narrowParams

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
