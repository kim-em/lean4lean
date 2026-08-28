import Lean4Lean.Verify.Inductive.Nested.EndToEnd

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Operational family alignment retained for primary iota restoration -/

/-- The lowest end-to-end join at which the restored generated recursor
telescope and the lockstep source/restored constructor mapping are both
available for one original family.  Later primary-iota proofs must retain
this object rather than projecting only the source recursor and constructor
translations, because those projections forget the telescope identities
needed to type the restored LHS application. -/
structure RestoredPrimaryOperationalFamilyAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) : Type where
  fvars : List FVarId
  stepState : Lean4Lean.ElimNestedInductive.State
  target : InductiveType
  loweredState : Lean4Lean.ElimNestedInductive.State
  params : result.params = (fvars.map Expr.fvar).toArray
  paramsNodup : fvars.Nodup
  paramsSize : result.params.size = nparams
  targetAt : result.types[familyIdx]? = some target
  oldRecName : Lean.mkRecName sourceTypes[familyIdx].name =
    Lean.mkRecName result.types.toArray[familyIdx]!.name
  constructorNames : Hstep.oldInfo.ctors =
    target.ctors.map (fun ctor => ctor.name)
  mappings : LoweredConstructorMappings loweredSourceEnv result.params
    nparams result sourceTypes[familyIdx].ctors stepState
      (target.ctors, loweredState)
  restorationTrace : StateForMTrace
    (RestoredConstructorStep result loweredEnv)
    (target.ctors.map (fun ctor => ctor.name)) Hstep.restored.headerEnv
      Hstep.restored.constructorEnv
  constructors : RestoredConstructorMappingTrace result loweredSourceEnv
    loweredEnv result.params nparams c.safety c.lparams
      sourceTypes[familyIdx].ctors stepState target.ctors loweredState
      Hstep.restored.headerEnv Hstep.restored.constructorEnv
  recursor : GeneratedRecursorRestorationTelescopeAlignment result loweredEnv
    auxRec Hstep.restored.recursor.restored.newInfo
      (Hprod.generated.entry familyIdx hentry)

/-- Select the exact lowering/restoration pair for one constructor position
from the lockstep family trace.  This is the pointwise operational input used
by the constructor half of the restored LHS telescope proof. -/
theorem RestoredConstructorMappingTrace.at
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (i : Nat) (hsource : i < sources.length)
    (htarget : i < targets.length) :
    ∃ before after stepSource stepTarget,
      LoweredConstructorMapping mappingEnv params nparams result
        sources[i] before (targets[i], after) ∧
      ∃ HctorStep : RestoredConstructorStep result loweredEnv targets[i].name
          stepSource stepTarget,
        safety ≤ (ConstantInfo.ctorInfo HctorStep.oldInfo).safety ∧
        HctorStep.oldInfo.levelParams = lparams ∧
        HctorStep.oldInfo.name = targets[i].name ∧
        HctorStep.oldInfo.type = targets[i].type := by
  induction H generalizing i with
  | nil => simp at hsource
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases i with
    | zero =>
      exact ⟨state, nextState, sourceProdEnv, middleProdEnv, Hmapping,
        Hstep, by simpa using hsafety, by simpa using hlevels,
        by simpa using hname, by simpa using htype⟩
    | succ i =>
      simpa using ih i (by simpa using hsource) (by simpa using htarget)

/-- Construct the joint operational certificate directly from a closed
lowering run and the exact family restoration step. -/
theorem NestedLoweringResultClosed.primaryOperationalFamilyAlignmentAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    Nonempty (RestoredPrimaryOperationalFamilyAlignment H Hprod familyIdx
      hfamily hentry Hstep) := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      htarget, hnames, Hmappings, Htrace, Hconstructors⟩
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
      ⟨_fvars, _stepState, mappedTarget, _loweredState, _hparams, _hnodup,
        _hsize, Hmapping, hmappedTarget⟩
    obtain ⟨hresult, hmappedEq⟩ := _root_.getElem?_eq_some_iff.mp hmappedTarget
    have harray : result.types.toArray[familyIdx]! = mappedTarget := by
      simp [Array.getElem!_eq_getD, Array.getD, hresult, hmappedEq]
    rw [harray, Hmapping.name]
  have hresultNparams : result.nparams = nparams :=
    H.toResult.resultNParams
  have hresultParams : result.params.size = result.nparams :=
    H.resultParamsSize
  rcases Hprod.restoredPrimaryTelescopeAlignment familyIdx hentry
      Hstep.restored.recursor holdRecName hresultNparams hresultParams with
    ⟨Hrecursor⟩
  exact ⟨{
    fvars := fvars
    stepState := stepState
    target := target
    loweredState := loweredState
    params := hparams
    paramsNodup := hnodup
    paramsSize := hsize
    targetAt := htarget
    oldRecName := holdRecName
    constructorNames := hnames
    mappings := Hmappings
    restorationTrace := Htrace
    constructors := Hconstructors
    recursor := Hrecursor }⟩

end VerifyInductive
end Lean4Lean
