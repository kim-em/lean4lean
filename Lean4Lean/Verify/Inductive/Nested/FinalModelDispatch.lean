import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterEvidence
import Lean4Lean.Verify.Inductive.Nested.NoPrimitiveRunInputs

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Final model dispatch for exact nested runs

This module is the narrow bridge between the exact executable nested run and
the public `InductiveFinalResult`.  Formation, recursors, equations, closure,
and unsafe restoration tags are already consequences of the exact run.  The
only remaining model premise is semantic coherence of the restored source
constructors in the exact final abstract environment.
-/

/-- Constructor coherence at the exact final environment produced by a nested
run.  Naming this boundary keeps declaration dispatch independent of the
internal safe/unsafe assembly split. -/
def NestedExactConstructorSemantics
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv) : Prop :=
  InductiveConstructorsSemanticallyCoherent safety outEnv
    (E.assembly.finalBaseVEnv.addDefEqRules
      (E.assembly.primaryRules ++ E.assembly.auxiliaryRules))

/-- Uniformly turn an exact safe or unsafe nested execution into the public
final result.  The lowering trace is reindexed only by the exact production
context equality retained in `E`; no separately chosen production witness is
used. -/
theorem NestedExactFinalRunResult.inductiveFinalResult
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) decl lparams nparams
      isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed sourceProdEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hconstructors : NestedExactConstructorSemantics E) :
    Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
      isUnsafe) := by
  have Hlower' : NestedLoweringResultClosed E.productionContext.env fuel
      nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := by
    simpa only [E.productionContext_env] using Hlower
  cases isUnsafe with
  | false =>
      exact E.safeInductiveFinalResult wf Hlower' hempty hconstructors
  | true =>
      exact E.unsafeInductiveFinalResult wf Hlower' hempty hconstructors

/-- Evidence provider for the assembly associated with the *actual* ordinary
production and restoration selected by the executable nested run. -/
def NestedFinalAssemblyProvider
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ (c' : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (depth : Nat)
    (commonParams : List VExpr) (commonLevel : VLevel)
    (Hc' : ContextWF c'),
    c'.env = env →
    c'.safety =
      (nestedAddInductiveContext env lparams isUnsafe false fuel).safety →
    c'.lparams = lparams →
    checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
      Hc'.venv c'.lparams nparams commonParams commonLevel
        res.types.toArray.toList →
    ∀ loweredEnv,
    (P : NestedInstalledProduction loweredEnv) →
    ∀ restoredEnv
      (Hrestored : RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)),
      ∃ sourceDecl, Nonempty (NestedFinalAssemblyProducerEvidence P
        Hrestored Hc'.venv sourceDecl lparams nparams isUnsafe
          (if isUnsafe then .unsafe else .safe))

/-- Final-result refinement for the nested post-lowering branch, factored at
the exact assembly boundary still being derived from production. Constructor
parameter domains are reconstructed internally from the exact replay and the
single producer-locality compatibility contract. -/
theorem Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams
      sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation)
    (hconstructorLocality : ConstructorParameterReplayLocality)
    (Hassembly : NestedFinalAssemblyProvider env lparams nparams sourceTypes
      isUnsafe fuel res) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  let Hc' : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe false fuel) :=
    ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false fuel
  have hctx : Hc'.mlctx.vlctx = [] := rfl
  have Hc'_venv : Hc'.venv =
      ves.venv (if isUnsafe then .unsafe else .safe) := rfl
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hctx : ContextWF c') →
      c'.allowPrimitive = false →
      c'.fuel = fuel →
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hctx.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      SemanticRunVerificationInputs c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe false fuel).safety !=
          .safe) Hctx := by
    intro c' stats depth commonParams commonLevel Hctx hallow _hfuel _Hsemantic
    exact SemanticRunVerificationInputs.ofNoPrimitive hallow
      hloopUArgsReplay
  have HlowerInitialClosed : NestedLoweringResultClosed env
      fuel.inductiveFuel nparams sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } res := by
    simpa using Hlower
  have HlowerInitial : NestedLoweringResult env fuel.inductiveFuel nparams
      sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } res := by
    exact HlowerInitialClosed.toResult
  have hnonempty : 0 < res.types.toArray.size :=
    HlowerInitial.resultTypesSizePos
  have Hrun :=
    Environment.addInductiveAfterLowering.nestedFinalExistentialSourceSemanticWF
      env lparams nparams sourceTypes isUnsafe false fuel res
      (fun _ => True) Hc' wf.inductivesClosed hctx
      hnonempty (inductiveSafety_notPartial isUnsafe) hproj
      Hinputs Hlower.toResult hnested
      (fun c' stats depth commonParams commonLevel Hctx henv hsafety hlparams
          Hsemantic loweredEnv P restoredEnv Hrestored => by
        rcases Hassembly c' stats depth commonParams commonLevel Hctx henv
            hsafety hlparams Hsemantic loweredEnv P restoredEnv Hrestored with
          ⟨sourceDecl, HE⟩
        exact ⟨sourceDecl, trivial, HE⟩)
  exact Hrun.mono fun outEnv Hout => by
    rcases Hout with ⟨c', Hctx, henv, hsafety, hlparams, hallow, hfuel,
      hvenv, ⟨R⟩⟩
    rcases R with ⟨sourceDecl, _haccepted, E⟩
    have hsource : Hctx.venv = ves.venv
        (if isUnsafe then .unsafe else .safe) := by
      exact hvenv.trans Hc'_venv
    have E' : NestedExactFinalRunResult res env sourceTypes
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv := by
      simpa only [hsource] using E
    have HlowerExact : NestedLoweringResultClosed E'.productionContext.env
        fuel.inductiveFuel nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res := by
      simpa only [E'.productionContext_env] using HlowerInitialClosed
    have hconstructors : NestedExactConstructorSemantics E' := by
      have Hparams := E'.restoredConstructorParameterDomains HlowerExact rfl
        hconstructorLocality
        (E'.restoredFamilyParameterScopes HlowerExact rfl)
      cases isUnsafe with
      | false =>
          exact E'.safeConstructorSemanticsOfParameterDomains wf HlowerExact
            rfl Hparams
      | true =>
          exact E'.unsafeConstructorSemanticsOfParameterDomains wf HlowerExact
            rfl Hparams
    exact E'.inductiveFinalResult wf HlowerInitialClosed rfl hconstructors

end VerifyInductive
end Lean4Lean
