import Lean4Lean.Verify.Inductive.Run.SemanticClosure
import Lean4Lean.Verify.Inductive.Equation.Build
import Lean4Lean.Verify.Inductive.Recursor.ConsumeAlpha

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Complete post-analysis result when the declaration is synthesized by the
successful header and constructor traversals rather than fixed before
execution. -/
def SemanticRunWithStatsResult
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (sourceEnv : VEnv) (outEnv : Environment) : Prop :=
  ∃ decl headerEnv ctorEnv,
    ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv,
    ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
      Nonempty (RecursorPhasesResult R outEnv)

/-- Complete ordinary `runWithStats` refinement from skeleton-free formation.
The existential declaration selected by constructor checking remains the
same declaration through recursor generation and equation reconstruction. -/
theorem AddInductive.runWithStats.semanticWF
    (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context) (depth : Nat) (sourceEnv : VEnv)
    (Hformation :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun ctorEnv => ∃ decl headerEnv,
          ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe
            depth sourceEnv indTypes headerEnv,
          ∃ _ : ConstructorPhasesResult Hheaders ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (SemanticRunWithStatsResult c stats nparams depth indTypes isUnsafe
        sourceEnv) := by
  unfold AddInductive.runWithStats
  have Hcombined := Hformation.bind fun ctorEnv Hresult => by
    rcases Hresult with ⟨decl, headerEnv, Hheaders, R, hclosed⟩
    have hlitHeaders := Hheaders.materializedAvailableLiteralDisjoint
    have hlitCtors :=
      R.declared.installed.availableLiteralDisjoint hlitHeaders
    have hlit : checkPositivityStep.AvailableLiteralDisjoint
        R.declared.context.venv stats.indConsts := by
      simpa [R.declared.contextVEnv] using hlitCtors
    exact (R.recursorPhasesWF hclosed hlparams hloopUArgsReplay hlit
      (fun Htr hfree => hproj _ Htr hfree) hnotPartial hnprim).mono
        fun outEnv Hrecursors =>
          show SemanticRunWithStatsResult c stats nparams depth indTypes
            isUnsafe sourceEnv outEnv
          from ⟨decl, headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

/-- One successful semantic header accumulation closes the complete ordinary
post-analysis checker without any declaration, skeleton, or constructor
target supplied by the caller. -/
theorem AddInductive.runWithStats.semanticClosedWF
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
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c.lparams.Nodup)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation)
    (hnotPartial : c.safety ≠ .partial)
    (hnprimRecursors : c.allowPrimitive = true →
      ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (SemanticRunWithStatsResult c stats nparams depth indTypes isUnsafe
        Hc.venv) := by
  apply AddInductive.runWithStats.semanticWF stats nparams indTypes numNested
    isUnsafe c depth Hc.venv
  · exact AddInductive.semanticFormationCoreClosedWF Hsemantic hlevels
      hlevelParams hindicesSize hindices hconsts hparams hcommonParams
      Hcache Hsuffix Hambient hcommon Hclosed hvisible hnprimTypes
      Lean4Lean.consumeTypeAnnotationsCompat hproj hnprimCtors
  · exact hlparams
  · exact hloopUArgsReplay
  · exact hproj
  · exact hnotPartial
  · exact hnprimRecursors

/-- Remaining environment-wide contracts at the post-header boundary.  The
declaration, its constructor targets, literal disjointness, formation, and
all equation data are deliberately absent: successful execution produces
them. -/
structure SemanticRunVerificationInputs
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth numNested : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (Hc : ContextWF c) : Prop where
  freshTypes : c.allowPrimitive = true → ∀ info ∈
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
      isUnsafe c.lparams).toList,
    ¬ Kernel.Environment.primitives.contains info.name
  freshConstructors : c.allowPrimitive = true →
    ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
    ¬ Kernel.Environment.primitives.contains ctor.name
  loopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat
  freshRecursors : c.allowPrimitive = true →
    ∀ owner (howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)

/-- Declaration-facing result of the complete skeleton-free ordinary
checker.  The semantic accumulator is retained so nested restoration can
refer back to the exact normalized source telescopes selected by the header
traversal. -/
def VerifiedSemanticInductiveRunResult
    (source : AddInductive.Context) (nparams : Nat)
    (types : List InductiveType)
    (numNested : Nat) (outEnv : Environment) : Prop :=
  ∃ c' stats depth commonParams commonLevel,
    ∃ Hc' : ContextWF c',
    c'.env = source.env ∧
    c'.safety = source.safety ∧
    c'.lparams = source.lparams ∧
    ∃ Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams commonParams commonLevel
          types.toArray.toList,
      SemanticRunWithStatsResult c' stats nparams depth
        types.toArray (source.safety != .safe) Hc'.venv outEnv

/-- Source-aligned declaration-facing result of the complete ordinary
checker.  In addition to the semantic certificate, this retains the exact
verification environment from which header checking began. -/
def VerifiedSemanticInductiveRunResultSourceAligned
    (source : AddInductive.Context) (sourceEnv : VEnv) (nparams : Nat)
    (types : List InductiveType)
    (numNested : Nat) (outEnv : Environment) : Prop :=
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
      SemanticRunWithStatsResult c' stats nparams depth
        types.toArray (source.safety != .safe) Hc'.venv outEnv

/-- The complete executable ordinary checker refines a skeleton-free
semantic result.  This replaces `run.materialize`'s caller-supplied abstract
skeleton with the declaration constructed from successful header and
constructor executions. -/
theorem AddInductive.run.semanticSourceAlignedWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial)
    (hproj : ProjectionConstPreservation)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF
      (VerifiedSemanticInductiveRunResultSourceAligned c Hc.venv nparams
        types numNested) := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply checkInductiveTypes.loopInd.checkInductiveTypes.accumulatesSemanticHeadersSourceAligned
      (fun stats => AddInductive.runWithStats stats nparams
        types.toArray numNested (c.safety != .safe))
      (VerifiedSemanticInductiveRunResultSourceAligned c Hc.venv nparams
        types numNested)
      Hc hctx hnonempty Lean4Lean.consumeTypeAnnotationsCompat
    intro c' stats depth commonParams commonLevel Hc' henv hsafety
      hlparams hallowPrimitive hfuel hvenv Hsemantic
      hlevels hlevelParams hindicesSize hindices _hconstsSize hconsts
      _hnonempty hparams hcommonParams Hcache Hsuffix Hambient hcommon
    let I := Hinputs (stats := stats) (depth := depth) Hc'
      hallowPrimitive hfuel Hsemantic
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
    have hlparamsNodup : c'.lparams.Nodup := by
      rw [hlparams]
      exact hnodup
    have hnotPartial : c'.safety ≠ .partial := by
      simpa [hsafety] using HnotPartial
    exact (AddInductive.runWithStats.semanticClosedWF Hsemantic hlevels
      hlevelParams hindicesSize hindices hconsts hparams hcommonParams
      Hcache Hsuffix Hambient hcommon Hclosed' hvisible I.freshTypes
      I.freshConstructors hlparamsNodup I.loopUArgsReplay hproj hnotPartial
      I.freshRecursors).mono fun outEnv Hrun =>
        ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
          hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hrun⟩
  simpa [AddInductive.run] using Hcombined

/-- Compatibility adapter for ordinary consumers that do not need to retain
the exact source verification environment. -/
theorem AddInductive.run.semanticWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial)
    (hproj : ProjectionConstPreservation)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF
      (VerifiedSemanticInductiveRunResult c nparams types numNested) := by
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hnonempty HnotPartial hproj
    (fun Hc' _hallowPrimitive _hfuel Hsemantic =>
      Hinputs Hc' Hsemantic)).mono fun _ Hresult => by
      rcases Hresult with
        ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
          hlparams, _hallowPrimitive, _hfuel, _hvenv, Hsemantic, Hrun⟩
      exact ⟨c', stats, depth, commonParams, commonLevel, Hc', henv,
        hsafety, hlparams, Hsemantic, Hrun⟩

end VerifyInductive
end Lean4Lean
