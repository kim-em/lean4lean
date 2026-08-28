import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Successful nested restoration retains the exact declaration fold, the
canonical-order side environment, and the exact successful native parameter
validation run before auxiliary validation begins. -/
structure RestoredAfterInstallResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (lparams : List Name) (safety : DefinitionSafety) (fuel : FuelConfig)
    (auxRecNames : List Name) (Validated : Environment → Prop)
    (outEnv : Environment) : Prop where
  restoration : Nonempty (RestoredNestedDeclarationsResult res loweredEnv
    sourceEnv recNameMap allIndNames types auxRecNames ((), outEnv))
  constructorParameterValidation : ∃ validationEnv,
    Nonempty (RestoredConstructorValidationEnvironment res loweredEnv
      sourceEnv allIndNames types validationEnv) ∧
    Lean4Lean.validateRestoredConstructorParameters.run validationEnv
      lparams safety fuel types res = .ok ()
  validated : Validated outEnv

/-- Compose the verified declaration-restoration folds with the exact native
constructor-parameter validation and the auxiliary validation pass. -/
theorem Environment.restoreNestedAfterInstall.WF
    (env loweredEnv : Environment) (lparams : List Name)
    (types : List InductiveType) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type res.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type res.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs res.nparams)
    (Haux : ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type res.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs res.nparams)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv validationEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv types).2 (types.map (·.name))
        types (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
        ((), restoredEnv)) →
      Nonempty (RestoredConstructorValidationEnvironment res loweredEnv env
        (types.map (·.name)) types validationEnv) →
      Lean4Lean.validateRestoredConstructorParameters.run validationEnv
        lparams safety fuel types res = .ok () →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety
      allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types lparams safety fuel
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 Validated outEnv := by
  let recNames := (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
  let recNameMap := (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
  let allIndNames := types.map (·.name)
  have Hdeclarations := restoreNestedDeclarations_refines res loweredEnv env
    recNameMap allIndNames allowPrimitive types recNames Htypes (by
      simpa [recNames] using Haux)
  have HrestoredEnv :
      ((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
        recNameMap allIndNames allowPrimitive types recNames env).WF
          fun restoredEnv => Nonempty (RestoredNestedDeclarationsResult res
            loweredEnv env recNameMap allIndNames types recNames
              ((), restoredEnv)) := by
    exact Hdeclarations.map fun restored Hrestored => by
      rcases restored with ⟨unit, restoredEnv⟩
      rcases unit with ⟨⟩
      exact Hrestored
  have HvalidationEnvironment :=
    restoreNestedConstructors_validationWF res loweredEnv env allIndNames
      allowPrimitive types (fun indType hind => by
        rcases Htypes indType hind with ⟨oldInfo, hlookup, _⟩
        exact ⟨oldInfo, hlookup⟩)
  have HvalidationEnv :
      ((·.2) <$> Lean4Lean.restoreNestedConstructors res loweredEnv
        allIndNames allowPrimitive types env).WF fun validationEnv =>
          Nonempty (RestoredConstructorValidationEnvironment res loweredEnv
            env allIndNames types validationEnv) := by
    exact HvalidationEnvironment.map fun restored Hrestored => by
      rcases restored with ⟨unit, validationEnv⟩
      rcases unit with ⟨⟩
      exact Hrestored.2
  have Houtput :
      (((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
          recNameMap allIndNames allowPrimitive types recNames env).bind
        fun restoredEnv =>
          ((·.2) <$> Lean4Lean.restoreNestedConstructors res loweredEnv
            allIndNames allowPrimitive types env).bind fun validationEnv =>
          (Lean4Lean.validateRestoredConstructorParameters.run validationEnv
            lparams safety fuel types res).bind fun _ =>
          (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety
            fuel res).bind fun _ => Except.pure restoredEnv).WF
        (RestoredAfterInstallResult res env loweredEnv recNameMap allIndNames
          types lparams safety fuel recNames Validated) :=
    HrestoredEnv.bind fun restoredEnv Hrestored => by
      exact HvalidationEnv.bind fun validationEnv HvalidationEnv => by
        have Hparameter :
            (Lean4Lean.validateRestoredConstructorParameters.run validationEnv
              lparams safety fuel types res).WF fun _ =>
                Lean4Lean.validateRestoredConstructorParameters.run
                  validationEnv lparams safety fuel types res = .ok () := by
          intro unit hrun
          rcases unit with ⟨⟩
          exact hrun
        exact Hparameter.bind fun _ Hparameter => by
          exact (Hvalidate restoredEnv validationEnv (by
            simpa [recNames, recNameMap, allIndNames] using Hrestored)
            (by simpa [allIndNames] using HvalidationEnv)
            Hparameter).bind
              fun _ Hvalidated => Except.WF.pure (show
                RestoredAfterInstallResult res env loweredEnv recNameMap
                  allIndNames types lparams safety fuel recNames Validated
                    restoredEnv from
                  ⟨Hrestored, ⟨validationEnv, HvalidationEnv, Hparameter⟩,
                    Hvalidated⟩)
  simpa [Environment.restoreNestedAfterInstall, recNames, recNameMap,
    allIndNames, StateT.run, bind, Except.bind, pure] using Houtput

end VerifyInductive
end Lean4Lean
