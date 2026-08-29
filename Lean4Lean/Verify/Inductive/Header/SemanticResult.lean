import Lean4Lean.Verify.Inductive.Header.LoopInd
import Lean4Lean.Verify.Inductive.Header.SemanticMaterialization

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
      some commonLevel) :
    checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (H.headerDecl isUnsafe) depth where
  headers := H.headerCertificate isUnsafe
  normalizedSources := H.normalizedSourceAt
  normalizedShapes := H.normalizedShapeAt
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
