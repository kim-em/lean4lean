import Lean4Lean.Verify.Inductive.PrimitiveConstructorCompletion
import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Equation.Build

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The non-inductive constructor half of a completed primitive batch
preserves closure of every mutual family visible after the header half. -/
theorem PrimitiveDeclaredConstructorsResult.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveDeclaredConstructorsResult H outEnv)
    (hclosed : MutualInductivesClosed headerEnv) :
    MutualInductivesClosed outEnv :=
  R.installed.closesMutuals H.context.checking.map_wf hclosed
    R.nonInductive

/-- Primitive header installation preserves closure of old families and
closes the newly installed canonical mutual block.  The closure argument is
entirely production-side and therefore does not assert abstract validity at
the header-only staging point. -/
theorem AddInductive.declareInductiveTypes.primitiveHeadersClosedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ H : PrimitiveDeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes outEnv,
          MutualInductivesClosed outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Hprimitive := AddInductive.declareInductiveTypes.primitiveHeadersWF
    (numNested := numNested) Hc Hdecl Hmaterialized hvisible
  have Hproduction := declareInductiveTypeInfos_refines c.allowPrimitive
    infos.toList c.env Hc.checking.tr.map_wf
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _ at Hprimitive ⊢
  intro outEnv hout
  rcases Hprimitive outEnv hout with ⟨Hheaders, _⟩
  have Hinfos := Hproduction outEnv hout
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hdecl.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, Hmaterialized.indices, List.length_map]
    exact htypesLength.symm
  exact ⟨Hheaders, Hinfos.closesMutuals Hclosed
    (inductiveTypeInfos_uniformAll stats numParams indTypes numNested
      isUnsafe c.lparams hsize)
    (inductiveTypeInfos_uniformNumParams stats numParams indTypes numNested
      isUnsafe c.lparams hsize)⟩

/-- The actual primitive header/check/constructor executable prefix, with
mutual closure retained at its first valid endpoint. -/
theorem AddInductive.formationCore.primitiveClosedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (Hshape : PrimitiveInductiveShape c.lparams numParams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ headerEnv : Environment,
        ∃ Hheaders : PrimitiveDeclaredHeadersResult c stats decl numParams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ R : PrimitiveConstructorPhasesResult Hheaders outEnv,
          MutualInductivesClosed outEnv := by
  have Hheaders :=
    AddInductive.declareInductiveTypes.primitiveHeadersClosedWF Hc Hclosed
      (numNested := numNested) Hdecl Hmaterialized hvisible
  exact Hheaders.bind fun headerEnv Hheader => by
    rcases Hheader with ⟨Hheader, hclosedHeader⟩
    exact (AddInductive.primitiveConstructorPhases.WF Hheader Hshape
      hvisible).mono fun outEnv Hresult => by
        rcases Hresult with ⟨R, _⟩
        exact ⟨headerEnv, Hheader, R, R.declared.closesMutuals hclosedHeader⟩

/-- End-to-end `runWithStats` refinement for the finite canonical primitive
branch.  Recursor generation rejoins the common executable suffix only after
the atomic header/constructor batch has restored a valid context. -/
theorem AddInductive.runWithStats.primitiveClosedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (Hshape : PrimitiveInductiveShape c.lparams numParams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hlparams : c.lparams.Nodup)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
    (hnotPartial : c.safety ≠ .partial) :
    (AddInductive.runWithStats stats numParams indTypes numNested isUnsafe
      c).WF fun outEnv =>
        ∃ ctorEnv,
        ∃ R : CompletedConstructorPhases c stats decl numParams isUnsafe
            depth Hc.venv indTypes ctorEnv,
          Nonempty (CompletedRecursorPhasesResult R outEnv) := by
  apply AddInductive.runWithStats.completedPrimitiveWF (hsourceSafety := hsourceSafety) stats numParams
    indTypes numNested isUnsafe c
  · exact AddInductive.formationCore.primitiveClosedWF Hc Hclosed Hdecl
      Hmaterialized Hshape hvisible
  · exact hlparams
  · exact Hshape.materializedLiteralDisjoint Hdecl Hmaterialized
  · exact hnotPartial
  · intro _hallow owner howner
    exact Hshape.recursorsNonprimitive owner howner

/-- Declaration-facing result for a canonical primitive `AddInductive.run`.
It records the independently materialized declaration and the common
completed recursor phase, without pretending that the header-only state was
an ordinary valid context. -/
def VerifiedPrimitiveInductiveRunResult
    (source : AddInductive.Context) (skeleton : VInductDeclSkeleton)
    (envTypes : VEnv) (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats decl depth,
    ∃ Hc' : ContextWF c',
    ∃ Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
      types.toArray.toList (source.safety != .safe) decl envTypes,
    ∃ Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth,
    ∃ ctorEnv,
    ∃ R : CompletedConstructorPhases c' stats decl skeleton.nparams
      (source.safety != .safe) depth Hc'.venv types.toArray ctorEnv,
      types.toArray.toList ≠ [] ∧
      Nonempty (CompletedRecursorPhasesResult R outEnv)


end VerifyInductive
end Lean4Lean
