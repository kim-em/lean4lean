import Lean4Lean.Verify.Inductive.OrdinaryFinalDispatch
import Lean4Lean.Verify.Inductive.PrimitiveFinalSpecification
import Lean4Lean.Verify.Inductive.Run.FinalResult
import Lean4Lean.Verify.Inductive.Nested.FinalModelDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Context strengthening (`VEnv.Strengthening`) of every abstract environment
in which the verified checker runs while `Environment.addInductive` checks and
installs the mutual inductive declaration `types` on top of the abstract
environment `venv` (the model of `env` at the declaration's safety level):

* `source`: the intermediate environments of the declaration itself
  (`InductiveStrengthening`).  These are used by the ordinary path through
  the lowering result below, and by the nested path for the restored source
  declaration (header, constructor-parameter, recursor-type and recursor-rule
  validation);
* `lowered`: the intermediate environments of the declaration produced by
  nested-inductive lowering, for the lowering result actually computed by the
  executable (`NestedLoweringResult` is the trace of
  `ElimNestedInductive.run`).  Without nested occurrences this is the source
  declaration again.

This is a hypothesis about this declaration only: every environment it
mentions is pinned by the abstract translation of the source or lowered
declaration. -/
structure InductiveDeclStrengthening (venv : VEnv) (env : Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig) : Prop where
  source : InductiveStrengthening venv lparams nparams types isUnsafe
  lowered : ∀ res, NestedLoweringResult env fuel.inductiveFuel nparams types
      { lvls := lparams.map .param, newTypes := types.toArray } res →
    InductiveStrengthening venv lparams nparams res.types isUnsafe

/-- The safety flag the executable passes to the post-lowering run agrees with
the source `isUnsafe` flag. -/
theorem inductiveSafety_ne_safe (isUnsafe : Bool) :
    ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) = isUnsafe := by
  cases isUnsafe <;> rfl

/-- Uniform final result for the ordinary, non-nested post-lowering branch. -/
theorem Environment.addInductiveAfterLowering.ordinaryInductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0)
    (hstrs : InductiveStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
      res.types ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe)) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  exact (Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF (hstrs := hstrs)
    env lparams nparams sourceTypes isUnsafe fuel res ves wf Hsources HsourcesB
    Hlower haux).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
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
    (haux : res.aux2nested.size = 0)
    (hstrs : InductiveStrengthening (ves.venv .safe) lparams nparams
      types isUnsafe) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductiveAfterLowering.primitiveFinalSpecificationModelWF (hstrs := hstrs)
      env lparams nparams types false fuel res ves wf Hshape
      htypes haux).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
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
    (hstrs : InductiveStrengthening (ves.venv .safe) lparams nparams
      types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true
      fuel).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductive.primitiveFinalSpecificationModelWF (hstrs := hstrs)
      env lparams nparams types false fuel ves wf Hshape).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
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
    (hstrs : InductiveStrengthening (ves.venv .safe) lparams nparams
      types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (addInductiveDeclaration.primitiveFinalSpecificationModelWF (hstrs := hstrs)
      env lparams nparams types false fuel ves wf Hshape).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- Dispatch over the actual lowering result.  The source-facing
specification requires the source declaration to have no loose bound
variables (`SourceBVarClosed`): lowering re-closes constructor types over the
opened parameters, which would silently repair such variables, so the checked
block is literally the source only under that hypothesis.  The zero-auxiliary case is
closed directly; the continuation is exactly the nonzero nested branch and
receives the closed lowering trace selected by execution. -/
theorem Environment.addInductive.inductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (HsourcesB : SourceBVarClosed types)
    (hstrs : InductiveDeclStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) env lparams nparams
      types isUnsafe fuel) :
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
  have hlowered : InductiveStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams res.types
      ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) := by
    rw [inductiveSafety_ne_safe]; exact hstrs.lowered res Hlower.toResult
  by_cases haux : res.aux2nested.size = 0
  · exact Environment.addInductiveAfterLowering.ordinaryInductiveFinalResultWF
      (hstrs := hlowered)
      env lparams nparams types isUnsafe fuel res ves wf Hsources HsourcesB
      Hlower.toResult haux
  · exact
      Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
        env lparams nparams types isUnsafe fuel res ves wf Hsources Hlower haux
        hstrs.source hlowered

/-- Checked `addDecl` composition for the non-primitive branch. Primitive
recognition is synchronized by the exact executable precheck equality;
ordinary-versus-nested dispatch remains internal. -/
theorem addInductiveDeclaration.inductiveFinalResultWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (HsourcesB : SourceBVarClosed types)
    (hcheck : Primitive.checkInductive env lparams nparams types
      isUnsafe = .ok false)
    (hstrs : InductiveDeclStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) env lparams nparams
      types isUnsafe fuel) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveFinalResult outEnv ves lparams nparams types
          isUnsafe) := by
  have Hrun := Environment.addInductive.inductiveFinalResultWF (hstrs := hstrs) env lparams
    nparams types isUnsafe fuel ves wf HsourcesB
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
