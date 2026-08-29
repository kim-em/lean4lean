import Lean4Lean.Verify.Inductive.PrimitiveSemanticFormation
import Lean4Lean.Verify.Inductive.PrimitiveRunWithStats
import Lean4Lean.Verify.Inductive.Recursor.ConsumeAlpha

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The skeleton-free primitive header path retains production mutual-family
closure without claiming validity for the header-only abstract environment. -/
theorem AddInductive.declareInductiveTypes.primitiveSemanticHeadersClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
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
          isUnsafe depth Hc.venv indTypes outEnv,
          MutualInductivesClosed outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have Hheaders :=
    AddInductive.declareInductiveTypes.primitiveSemanticHeadersWF
      (numNested := numNested) Hsemantic hlevels hlevelParams hindicesSize
      hindices hconsts hparams hcommonParams Hcache Hsuffix Hambient hcommon
      Hshape hvisible
  have Hproduction := declareInductiveTypeInfos_refines c.allowPrimitive
    infos.toList c.env Hc.checking.tr.map_wf
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _ at Hheaders ⊢
  intro outEnv hout
  rcases Hheaders outEnv hout with ⟨decl, envTypes, Hheader, _⟩
  have Hinfos := Hproduction outEnv hout
  exact ⟨decl, envTypes, Hheader,
    Hinfos.closesMutuals Hclosed
      (inductiveTypeInfos_uniformAll stats nparams indTypes numNested
        isUnsafe c.lparams hindicesSize)
      (inductiveTypeInfos_uniformNumParams stats nparams indTypes numNested
        isUnsafe c.lparams hindicesSize)⟩

/-- The real primitive header/check/constructor prefix with its declaration
synthesized from the successful semantic folds. -/
theorem AddInductive.formationCore.primitiveSemanticClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
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
    ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ decl, ∃ headerEnv : Environment,
        ∃ Hheaders : PrimitiveDeclaredHeadersResult c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ R : PrimitiveConstructorPhasesResult Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  have Hheaders :=
    AddInductive.declareInductiveTypes.primitiveSemanticHeadersClosedWF
      (numNested := numNested) Hsemantic Hclosed hlevels hlevelParams
      hindicesSize hindices hconsts hparams hcommonParams Hcache Hsuffix
      Hambient hcommon Hshape hvisible
  exact Hheaders.bind fun headerEnv Hheader => by
    rcases Hheader with ⟨decl, _envTypes, Hheader, hclosedHeader⟩
    exact (AddInductive.primitiveConstructorPhases.WF Hheader Hshape
      hvisible).mono fun outEnv Hresult => by
        rcases Hresult with ⟨R, _⟩
        exact ⟨decl, headerEnv, Hheader, R,
          R.declared.closesMutuals hclosedHeader⟩

/-- Complete primitive run-with-stats result with no caller-provided abstract
declaration or header environment. -/
def SemanticPrimitiveRunWithStatsResult
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (outEnv : Environment) : Prop :=
  ∃ decl, ∃ ctorEnv,
    ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
        sourceEnv indTypes ctorEnv,
      Nonempty (CompletedRecursorPhasesResult R outEnv)

/-- Skeleton-free primitive formation rejoins the common recursor suffix only
after the atomic constructor endpoint has restored a valid context. -/
theorem AddInductive.runWithStats.primitiveSemanticWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
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
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hlparams : c.lparams.Nodup)
    (hnotPartial : c.safety ≠ .partial) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (SemanticPrimitiveRunWithStatsResult c stats nparams depth Hc.venv
        indTypes isUnsafe) := by
  unfold AddInductive.runWithStats
  have Hformation :=
    AddInductive.formationCore.primitiveSemanticClosedWF
      (numNested := numNested) Hsemantic Hclosed hlevels hlevelParams
      hindicesSize hindices
      hconsts hparams hcommonParams Hcache Hsuffix Hambient hcommon Hshape
      hvisible
  have Hcombined := Hformation.bind fun ctorEnv Hresult => by
    rcases Hresult with ⟨decl, _headerEnv, Hheaders, R, hclosed⟩
    have Hmaterialized := Hheaders.sourceMaterialized
    rw [Hheaders.sourceContextVEnv] at Hmaterialized
    exact (R.completed.recursorPhasesWF hclosed hlparams
      (Hshape.materializedLiteralDisjoint Hheaders.translation
        Hmaterialized)
      hnotPartial
      (fun _hallow owner howner =>
        Hshape.recursorsNonprimitive owner howner)).mono
          fun outEnv Hrecursors =>
            show SemanticPrimitiveRunWithStatsResult c stats nparams depth
                Hc.venv indTypes isUnsafe outEnv
            from ⟨decl, ctorEnv, R.completed, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

/-- Declaration-facing primitive result whose declaration is selected by the
successful executable header and constructor traversals. -/
def VerifiedSemanticPrimitiveInductiveRunResult
    (source : AddInductive.Context) (nparams : Nat)
    (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats depth commonParams commonLevel,
    ∃ Hc' : ContextWF c',
    c'.env = source.env ∧
    c'.safety = source.safety ∧
    c'.lparams = source.lparams ∧
    ∃ Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          types.toArray.toList,
    ∃ Hshape : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (source.safety != .safe),
      SemanticPrimitiveRunWithStatsResult c' stats nparams depth Hc'.venv
        types.toArray (source.safety != .safe) outEnv

/-- Source-aligned primitive result, retaining the exact abstract model from
which the executable header traversal began. -/
def VerifiedSemanticPrimitiveInductiveRunResultSourceAligned
    (source : AddInductive.Context) (sourceEnv : VEnv) (nparams : Nat)
    (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats depth commonParams commonLevel,
    ∃ Hc' : ContextWF c',
    c'.env = source.env ∧
    c'.safety = source.safety ∧
    c'.lparams = source.lparams ∧
    c'.allowPrimitive = source.allowPrimitive ∧
    c'.fuel = source.fuel ∧
    Hc'.venv = sourceEnv ∧
    ∃ Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          types.toArray.toList,
    ∃ Hshape : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (source.safety != .safe),
      SemanticPrimitiveRunWithStatsResult c' stats nparams depth Hc'.venv
        types.toArray (source.safety != .safe) outEnv

/-- The complete executable primitive checker, with no caller-supplied
declaration skeleton, constructor targets, or abstract header environment. -/
theorem AddInductive.run.primitiveSemanticSourceAlignedWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF
      (VerifiedSemanticPrimitiveInductiveRunResultSourceAligned c Hc.venv
        nparams types numNested) := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply
      checkInductiveTypes.loopInd.checkInductiveTypes.accumulatesSemanticHeadersSourceAligned
        (fun stats => AddInductive.runWithStats stats nparams
          types.toArray numNested (c.safety != .safe))
        (VerifiedSemanticPrimitiveInductiveRunResultSourceAligned c Hc.venv
          nparams types numNested)
        Hc hctx hnonempty Lean4Lean.consumeTypeAnnotationsCompat
    intro c' stats depth commonParams commonLevel Hc' henv hsafety
      hlparams hallowPrimitive hfuel hvenv Hsemantic
      hlevels hlevelParams hindicesSize hindices _hconstsSize hconsts
      _hnonempty hparams hcommonParams Hcache Hsuffix Hambient hcommon
    have Hclosed' : MutualInductivesClosed c'.env := by
      rw [henv]
      exact Hclosed
    have hvisible : c'.safety ≤
        (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
      rw [hsafety]
      cases h : c.safety with
      | «unsafe» => simp [h]
      | safe => simp [h]
      | «partial» => exact (HnotPartial h).elim
    have Hshape' : PrimitiveInductiveShape c'.lparams nparams
        types.toArray.toList (c.safety != .safe) := by
      simpa [hlparams] using Hshape
    have hlparamsNodup : c'.lparams.Nodup := by
      rw [hlparams]
      exact hnodup
    have hnotPartial : c'.safety ≠ .partial := by
      simpa [hsafety] using HnotPartial
    exact (AddInductive.runWithStats.primitiveSemanticWF
      (numNested := numNested) Hsemantic Hclosed' hlevels hlevelParams
      hindicesSize hindices hconsts hparams hcommonParams Hcache Hsuffix
      Hambient hcommon Hshape' hvisible hlparamsNodup
      hnotPartial).mono
        fun outEnv Hrun =>
          ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
            hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hshape',
            Hrun⟩
  simpa [AddInductive.run] using Hcombined

/-- Compatibility adapter for primitive consumers that do not need the exact
source abstract environment. -/
theorem AddInductive.run.primitiveSemanticWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF
      (VerifiedSemanticPrimitiveInductiveRunResult c nparams types
        numNested) := by
  exact (AddInductive.run.primitiveSemanticSourceAlignedWF nparams numNested
    Hc Hclosed Hshape hctx hnonempty HnotPartial).mono fun _ Hresult => by
      rcases Hresult with
        ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
          hlparams, _hallowPrimitive, _hfuel, _hvenv, Hsemantic, Hshape',
          Hrun⟩
      exact ⟨c', stats, depth, commonParams, commonLevel, Hc', henv,
        hsafety, hlparams, Hsemantic, Hshape', Hrun⟩

end VerifyInductive
end Lean4Lean
