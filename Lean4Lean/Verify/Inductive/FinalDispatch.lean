import Lean4Lean.Verify.Inductive.OrdinaryFinalDispatch
import Lean4Lean.Verify.Inductive.PrimitiveFinalSpecification
import Lean4Lean.Verify.Inductive.Run.FinalResult
import Lean4Lean.Verify.Inductive.Nested.FinalModelDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Uniform final result for the ordinary, non-nested post-lowering branch. -/
theorem Environment.addInductiveAfterLowering.ordinaryInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  exact (Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF
    env lparams nparams sourceTypes isUnsafe fuel res ves wf Hsources
    Hlower haux).mono
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
      htypes haux).mono
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
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true
      fuel).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductive.primitiveFinalSpecificationModelWF
      env lparams nparams types false fuel ves wf Hshape).mono
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
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (addInductiveDeclaration.primitiveFinalSpecificationModelWF
      env lparams nparams types false fuel ves wf Hshape).mono
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
    (ves : VEnvs) (wf : ves.WF env) :
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
      Hlower.toResult haux
  · exact
      Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
        env lparams nparams types isUnsafe fuel res ves wf Hsources Hlower haux

/-- Checked `addDecl` composition for the non-primitive branch. Primitive
recognition is synchronized by the exact executable precheck equality;
ordinary-versus-nested dispatch remains internal. -/
theorem addInductiveDeclaration.inductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hcheck : Primitive.checkInductive env lparams nparams types
      isUnsafe = .ok false) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have Hrun := Environment.addInductive.inductiveFinalResultWF env lparams
    nparams types isUnsafe fuel ves wf
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
