import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterEvidence
import Lean4Lean.Verify.Inductive.Nested.NoPrimitiveRunInputs
import Lean4Lean.Verify.Inductive.Nested.AssemblyProviderEvidence

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
    (Hsources : SourceSyntaxChecks sourceTypes)
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
  have Hmetadata : MaterializedInductivePrefix decl
      E.production.loweredDecl := by
    simpa only [E.production_eq] using E.assembly.materialized
  cases isUnsafe with
  | false =>
      exact E.safeInductiveFinalResult wf Hlower' Hmetadata
        Hsources hempty hconstructors
  | true =>
      exact E.unsafeInductiveFinalResult wf Hlower' Hmetadata
        Hsources hempty hconstructors

/-- Final-result refinement for the nested post-lowering branch.  Exact
assembly and constructor parameter domains are reconstructed internally from
the checked production, lowering, validation, and restoration traces. -/
theorem Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringResultClosed env fuel.inductiveFuel nparams
      sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0) :
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
    Environment.addInductiveAfterLowering.nestedValidatedExistentialSourceSemanticWF
      env lparams nparams sourceTypes isUnsafe false fuel res
      Hc' wf.inductivesClosed wf.constructorOwners hctx
      hnonempty (inductiveSafety_notPartial isUnsafe)
      Hinputs Hsources rfl Hlower hnested
  exact Hrun.mono fun outEnv Hout => by
    rcases Hout with ⟨c', Hctx, henv, hsafety, hlparams, hallow, hfuel,
      hvenv, sourceDecl, ⟨V⟩⟩
    have hsource : Hctx.venv = ves.venv
        (if isUnsafe then .unsafe else .safe) := by
      exact hvenv.trans Hc'_venv
    have V' : NestedValidatedRunResult res env sourceTypes
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv := by
      simpa only [hsource] using V
    rcases V'.assemblyNative wf Hsources with ⟨⟨C, hproduction⟩⟩
    have Hvalid : CheckingEnv.Valid
        (if isUnsafe then .unsafe else .safe) env
          (ves.venv (if isUnsafe then .unsafe else .safe)) :=
      (wf.tr (safety := if isUnsafe then .unsafe else .safe)).toCheckingValid
        (wf.hasPrimitives (safety := if isUnsafe then .unsafe else .safe))
        wf.safePrimitives wf.typeAnnotationWrappers
    let E' : NestedExactFinalRunResult res env sourceTypes
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv := {
      loweredEnv := V'.loweredEnv
      production := V'.production
      productionContext := V'.productionContext
      productionContextWF := V'.productionContextWF
      productionContext_env := V'.productionContext_env
      productionContext_lparams := V'.productionContext_lparams
      productionContext_safety := V'.productionContext_safety
      production_c := V'.production_c
      production_nparams := V'.production_nparams
      production_isUnsafe := V'.production_isUnsafe
      production_initialEnv := V'.production_initialEnv
      production_indTypes := V'.production_indTypes
      validationFuel := V'.validationFuel
      lowering := V'.lowering
      restoration := V'.restoration
      primitiveSafe := V'.primitiveSafe
      validationEnv := V'.validationEnv
      validationEnvironment := by
        simpa only [V'.productionContext_allowPrimitive] using
          V'.validationEnvironment
      recursorTypeValidation := V'.recursorTypeValidation
      recursorRuleValidation := V'.recursorRuleValidation
      auxiliaryHeaderEnv := V'.auxiliaryHeaderEnv
      headerValidationEnvironment := V'.headerValidationEnvironment
      parameterValidation := V'.parameterValidation
      auxiliaryVEnv := V'.auxiliaryVEnv
      auxiliaryMLCtx := V'.auxiliaryMLCtx
      auxiliaryMLCtx_lctx := V'.auxiliaryMLCtx_lctx
      auxiliaryMLCtxWF := V'.auxiliaryMLCtxWF
      validatedAuxiliaries := V'.validatedAuxiliaries
      auxiliarySelection := V'.auxiliarySelection
      auxiliaryTranslations := V'.auxiliaryTranslations
      nativeSource := V'.nativeSource
      nativeSourceDecl_eq := V'.nativeSourceDecl_eq
      assembly := C
      production_eq := hproduction
      finalResult := C.finalEnvironment Hvalid }
    have HlowerExact : NestedLoweringResultClosed E'.productionContext.env
        fuel.inductiveFuel nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res := by
      simpa only [E'.productionContext_env] using HlowerInitialClosed
    have hconstructors : NestedExactConstructorSemantics E' := by
      have Hparams := E'.restoredConstructorParameterDomainsNative
        (E'.restoredFamilyParameterScopes HlowerExact rfl)
      have Howners : ConstructorOwnersPresent E'.productionContext.env := by
        rw [E'.productionContext_env]
        exact wf.constructorOwners
      have Hmetadata : MaterializedInductivePrefix sourceDecl
          E'.production.loweredDecl := by
        simpa only [E'.production_eq] using E'.assembly.materialized
      cases isUnsafe with
      | false =>
          exact E'.safeConstructorSemanticsOfParameterDomains wf HlowerExact
            Hmetadata Hsources Howners rfl Hparams
      | true =>
          exact E'.unsafeConstructorSemanticsOfParameterDomains wf HlowerExact
            Hmetadata Hsources Howners rfl Hparams
    exact E'.inductiveFinalResult wf Hsources HlowerInitialClosed rfl
      hconstructors

end VerifyInductive
end Lean4Lean
