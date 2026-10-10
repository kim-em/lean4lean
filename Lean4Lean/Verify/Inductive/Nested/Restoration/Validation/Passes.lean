import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorationRun
import Lean4Lean.Verify.Inductive.Install.BlockCertificate

/-! # The validation passes (owner: Restoration-A)

The semantic content of the four validation passes of `restoreNestedAfterInstall`
(`RestorationRun`), each stated against a checker environment `CheckerEnv safety E V` for the
side environment `E` it runs in, as the wave 1A checker verification reads it
(`TypeChecker.checkType.WF`, `ensureSort.WF`, `checkNoMVarNoFVar.WF`): the checked syntax
translates and is typed in the model `V`. These are the boundary theorems of the
`Validation/` directory; the restoration owner (Restoration-B) instantiates them with the
models of the side environments it builds from the restoration folds, and the stripped
environment's model is `stripRecursorRules.checkingValid`.

Source branch: `Nested/Restoration/Validation/{Checks,Environment,ConstructorEnvironment,
StrippedEnvironment,StrippedRecursorShapes,ParameterScopes,ParameterPrefix,Result}.lean` and
`Nested/Restoration/Uniform/{Declarations,Recursors,Whnf}.lean` (parameter uniformity of the
restored telescopes under `whnf`, read by the recursor-type validation). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv}

/-- The restored recursor read by the recursor validation passes. -/
abbrev restoredRecursorOf (res : ElimNestedInductive.Result) (loweredEnv : Environment)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (recInfo : RecursorVal) : RecursorVal :=
  res.restoreRecursor loweredEnv recNameMap allIndNames recName (recNameMap.getD recName recName)
    recInfo

/-- `validateSourceConstructorTypes`: every source constructor type is closed and a type of
the checker's model (the restored header environment). -/
theorem validateSourceConstructorTypes.run.WF (C : CheckerEnv safety env venv)
    (lparams : List Name) (fuel : FuelConfig) (types : List InductiveType)
    (h : validateSourceConstructorTypes.run env lparams safety fuel types = .ok ()) :
    ∀ type ∈ types, ∀ ctor ∈ type.ctors,
      ∃ T, TrExprS venv lparams [] ctor.type T ∧ venv.IsType lparams.length [] T := by
  -- WAVE 3 STUB (Restoration-A): `TypeChecker.checkType.WF` and `ensureSort.WF` in the
  -- initial checker context of `C` (`VContext.mk1`), over the two `forM`s.
  have := C; have := h; sorry

/-- `validateRestoredRecursorTypes.check`: the lowered recursor exists and its restored type is
closed and a type of the checker's model (the restored constructor environment). -/
theorem validateRestoredRecursorTypes.check.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (h : validateRestoredRecursorTypes.check env loweredEnv safety fuel res recNameMap
      allIndNames recName = .ok ()) :
    ∃ recInfo, loweredEnv.find? recName = some (.recInfo recInfo) ∧
      ∃ T, TrExprS venv (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
          recInfo).levelParams []
        (restoredRecursorOf res loweredEnv recNameMap allIndNames recName recInfo).type T ∧
      venv.IsType (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
        recInfo).levelParams.length [] T := by
  -- WAVE 3 STUB (Restoration-A): the source branch's `Validation/Checks.lean`
  -- (`validateRestoredRecursorTypes.check.WF`).
  have := C; have := h; sorry

/-- `validateRestoredRecursorTypes.run`, over the source and auxiliary recursors. -/
theorem validateRestoredRecursorTypes.run.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name)
    (h : validateRestoredRecursorTypes.run env loweredEnv safety fuel res recNameMap allIndNames
      types auxRecNames = .ok ()) :
    ∀ recName ∈ types.map (mkRecName ·.name) ++ auxRecNames,
      validateRestoredRecursorTypes.check env loweredEnv safety fuel res recNameMap allIndNames
        recName = .ok () := by
  -- WAVE 3 STUB (Restoration-A): the two `forM`s of `validateRestoredRecursorTypes.run`.
  have := C; have := h; sorry

/-- `validateRestoredRecursorRules.check`: the lowered recursor exists and the reduct of every
restored rule is closed and typed in the checker's model (the stripped restored
environment). -/
theorem validateRestoredRecursorRules.check.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (h : validateRestoredRecursorRules.check env loweredEnv safety fuel res recNameMap
      allIndNames recName = .ok ()) :
    ∃ recInfo, loweredEnv.find? recName = some (.recInfo recInfo) ∧
      ∀ rule ∈ (restoredRecursorOf res loweredEnv recNameMap allIndNames recName recInfo).rules,
        ∃ rhs T, TrExprS venv (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
            recInfo).levelParams [] rule.rhs rhs ∧
          venv.HasType (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
            recInfo).levelParams.length [] rhs T := by
  -- WAVE 3 STUB (Restoration-A): `TypeChecker.checkType.WF` over the rules' `forM`.
  have := C; have := h; sorry

/-- `validateRestoredRecursorRules.run`, over the source and auxiliary recursors. -/
theorem validateRestoredRecursorRules.run.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name)
    (h : validateRestoredRecursorRules.run env loweredEnv safety fuel res recNameMap allIndNames
      types auxRecNames = .ok ()) :
    ∀ recName ∈ types.map (mkRecName ·.name) ++ auxRecNames,
      validateRestoredRecursorRules.check env loweredEnv safety fuel res recNameMap allIndNames
        recName = .ok () := by
  -- WAVE 3 STUB (Restoration-A): the two `forM`s of `validateRestoredRecursorRules.run`.
  have := C; have := h; sorry

/-- `validateNestedAuxiliaries`: the lowering's local context translates to a well-formed
checker context of the model (the restored header environment), in which every cached nested
occurrence `I Ds` translates and is typed. -/
theorem validateNestedAuxiliaries.WF (C : CheckerEnv safety env venv) (lparams : List Name)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (h : validateNestedAuxiliaries env lparams safety fuel res = .ok ()) :
    ∃ mlctx : TypeChecker.MLCtx, mlctx.lctx = res.lctx ∧ mlctx.WF venv lparams ∧
      ∀ n nested, res.aux2nested.find? n = some nested →
        ∃ e T, TrExprS venv lparams mlctx.vlctx nested e ∧
          venv.HasType lparams.length mlctx.vlctx.toCtx e T := by
  -- WAVE 3 STUB (Restoration-A): the source branch's `validateNestedAuxiliaries.WF`
  -- (`Nested/Lowering/Basic.lean`): `TypeChecker.M.run` in the lowering's `lctx`
  -- (`NestedBindingContextWF`), `checkType.WF` over the cache's `forM`.
  have := C; have := h; sorry

/-- **The stripped restored environment** (the output with the new recursors' rules removed,
in which the restored rules are validated) is a valid checking environment of the recursor
stage: the new recursors are constants there and none of the block's ι rules is registered. -/
theorem stripRecursorRules.checkingValid {outEnv : Environment} {venv outVEnv : VEnv}
    {decl : VInductDecl} (H : AddInduct safety env.constants venv decl outEnv.constants outVEnv)
    (hchk : CheckingEnv.Valid safety outEnv outVEnv) :
    CheckingEnv.Valid safety (stripRecursorRules outEnv (H.rvals.map (·.name))) H.envR := by
  -- WAVE 3 STUB (Restoration-A): the source branch's `Validation/StrippedEnvironment.lean`
  -- (the overwriting lemma for well-formed `SMap`s, `Aligned` under replacement of a constant
  -- by one with the same name, safety, universes and type) and
  -- `Validation/StrippedRecursorShapes.lean`; the rule stage adds no constant
  -- (`VEnv.addRules_le`, `addInduct_pats_origin`).
  have := H; have := hchk; sorry

end VerifyInductive
end Lean4Lean
