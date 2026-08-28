import Lean4Lean.Verify.Inductive.OrdinaryFinalDispatch
import Lean4Lean.Verify.Inductive.PrimitiveFinalSpecification
import Lean4Lean.Verify.Inductive.Run.FinalResult
import Lean4Lean.Verify.Inductive.Nested.FinalModelDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The remaining producer/translation compatibility contracts shared by all
inductive execution paths.  Keeping them explicit at the declaration boundary
makes the eventual assumption audit finite and reviewable. -/
structure InductiveVerificationAssumptions : Prop where
  loopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat
  projections : ProjectionConstPreservation

/-- Uniform final result for the ordinary, non-nested post-lowering branch. -/
theorem Environment.addInductiveAfterLowering.ordinaryInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  exact (Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF
    env lparams nparams sourceTypes isUnsafe fuel res ves wf Hsources
    Hlower haux hloopUArgsReplay hproj).mono
      fun _ ⟨ves', wf', hle, Hspec⟩ =>
        ⟨InductiveFinalResult.ofModel ves' wf' hle Hspec⟩

/-- Uniform final result for the canonical primitive Bool/Nat post-lowering
branch, valid both before and after the bootstrap `Eq` declaration. -/
theorem Environment.addInductiveAfterLowering.primitiveInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductiveAfterLowering.primitiveFinalSpecificationModelWF
      env lparams nparams types false fuel res ves wf Hshape
      hloopUArgsReplay hproj htypes haux).mono
      fun _ ⟨ves', wf', hle, Hspec⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- Uniform `Environment.addInductive` result for canonical primitive
Bool/Nat declarations. -/
theorem Environment.addInductive.primitiveInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (A : InductiveVerificationAssumptions) :
    (Environment.addInductive env lparams nparams types isUnsafe true
      fuel).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductive.primitiveFinalSpecificationModelWF
      env lparams nparams types false fuel ves wf Hshape
      A.loopUArgsReplay A.projections).mono
      fun _ ⟨ves', wf', hle, Hspec⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- Checked declaration-facing form of
`primitiveInductiveFinalResultWF`. -/
theorem addInductiveDeclaration.primitiveInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (addInductiveDeclaration.primitiveFinalSpecificationModelWF
      env lparams nparams types false fuel ves wf Hshape
      hloopUArgsReplay hproj).mono
      fun _ ⟨ves', wf', hle, Hspec⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- Dispatch over the actual lowering result.  The zero-auxiliary case is
closed directly; the continuation is exactly the nonzero nested branch and
receives the closed lowering trace selected by execution. -/
theorem Environment.addInductive.inductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (A : InductiveVerificationAssumptions)
    (HnestedAssembly : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResultClosed env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      res.aux2nested.size ≠ 0 →
      NestedFinalAssemblyProvider env lparams nparams types isUnsafe fuel res) :
    (Environment.addInductive env lparams nparams types isUnsafe false
      fuel).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  refine Environment.addInductive.checkedLoweringClosedWF env lparams nparams
    types isUnsafe false fuel wf.inductivesClosed
      (VEnvs.WF.environmentTypesClosed wf)
      (fun outEnv => Nonempty (InductiveFinalResult outEnv ves lparams
        nparams types isUnsafe)) ?_
  intro res Hsources Hlower
  by_cases haux : res.aux2nested.size = 0
  · exact Environment.addInductiveAfterLowering.ordinaryInductiveFinalResultWF
      env lparams nparams types isUnsafe fuel res ves wf Hsources
      Hlower.toResult haux A.loopUArgsReplay A.projections
  · exact
      Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
        env lparams nparams types isUnsafe fuel res ves wf Hlower haux
        A.loopUArgsReplay A.projections
        (HnestedAssembly res Hsources Hlower haux)

/-- Checked `addDecl` composition for the non-primitive branch. Primitive
recognition is synchronized by the exact executable precheck equality;
ordinary-versus-nested dispatch remains internal. -/
theorem addInductiveDeclaration.inductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hcheck : Environment.checkPrimitiveInductive env lparams nparams types
      isUnsafe = .ok false)
    (A : InductiveVerificationAssumptions)
    (HnestedAssembly : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResultClosed env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      res.aux2nested.size ≠ 0 →
      NestedFinalAssemblyProvider env lparams nparams types isUnsafe fuel res) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have Hrun := Environment.addInductive.inductiveFinalResultWF env lparams
    nparams types isUnsafe fuel ves wf A HnestedAssembly
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
