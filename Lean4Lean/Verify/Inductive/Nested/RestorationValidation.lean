import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidation
import Lean4Lean.Verify.Inductive.Nested.RestorationNonprimitive

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
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (auxRecNames : List Name) (Validated : Environment → Prop)
    (outEnv : Environment) : Prop where
  restoration : Nonempty (RestoredNestedDeclarationsResult res loweredEnv
    sourceEnv recNameMap allIndNames types auxRecNames ((), outEnv))
  primitiveSafe : ∃ entries,
    PrimitiveSafeFreshConstantTrace allowPrimitive sourceEnv entries outEnv
  constructorParameterValidation : ∃ validationEnv,
    Nonempty (RestoredConstructorValidationEnvironment res loweredEnv
      sourceEnv allIndNames allowPrimitive types validationEnv)
  auxiliaryHeaderValidation : ∃ auxiliaryHeaderEnv,
    Nonempty (RestoredHeaderValidationEnvironment loweredEnv sourceEnv
      allIndNames types auxiliaryHeaderEnv) ∧
    Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
      lparams safety fuel types res = .ok () ∧
    Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv lparams safety
      fuel res = .ok ()
  recursorTypeValidation : ∃ validationEnv,
    Nonempty (RestoredConstructorValidationEnvironment res loweredEnv
      sourceEnv allIndNames allowPrimitive types validationEnv) ∧
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
      lparams safety fuel res recNameMap allIndNames types auxRecNames = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run outEnv loweredEnv lparams
      safety fuel res recNameMap allIndNames types auxRecNames = .ok ()
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
    (hsourceWF : env.constants.WF)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv validationEnv auxiliaryHeaderEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv types).2 (types.map (·.name))
        types (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
        ((), restoredEnv)) →
      Nonempty (RestoredConstructorValidationEnvironment res loweredEnv env
        (types.map (·.name)) allowPrimitive types validationEnv) →
      Nonempty (RestoredHeaderValidationEnvironment loweredEnv env
        (types.map (·.name)) types auxiliaryHeaderEnv) →
      Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
        lparams safety fuel types res = .ok () →
      Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
        lparams safety fuel res (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 = .ok () →
      Lean4Lean.validateRestoredRecursorRules.run restoredEnv loweredEnv
        lparams safety fuel res
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 = .ok () →
      (Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv lparams safety
        fuel res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety
      allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types lparams safety allowPrimitive fuel
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 Validated outEnv := by
  let recNames := (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
  let recNameMap := (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
  let allIndNames := types.map (·.name)
  have Hdeclarations := restoreNestedDeclarations_refines_primitiveSafe res
    loweredEnv env recNameMap allIndNames allowPrimitive types recNames Htypes
      (by simpa [recNames] using Haux) hsourceWF
  have HrestoredEnv :
      ((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
        recNameMap allIndNames allowPrimitive types recNames env).WF
          fun restoredEnv =>
            Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
              recNameMap allIndNames types recNames ((), restoredEnv)) ∧
            ∃ entries, PrimitiveSafeFreshConstantTrace allowPrimitive env
              entries restoredEnv := by
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
            env allIndNames allowPrimitive types validationEnv) := by
    exact HvalidationEnvironment.map fun restored Hrestored => by
      rcases restored with ⟨unit, validationEnv⟩
      rcases unit with ⟨⟩
      exact Hrestored.2
  have HauxiliaryHeaderEnvironment :=
    restoreNestedHeaders_validationWF loweredEnv env allIndNames
      allowPrimitive types
  have HauxiliaryHeaderEnv :
      ((·.2) <$> Lean4Lean.restoreNestedHeaders loweredEnv allIndNames
        allowPrimitive types env).WF fun auxiliaryHeaderEnv =>
          Nonempty (RestoredHeaderValidationEnvironment loweredEnv env
            allIndNames types auxiliaryHeaderEnv) := by
    exact HauxiliaryHeaderEnvironment.map fun restored Hrestored => by
      rcases restored with ⟨resultUnit, auxiliaryHeaderEnv⟩
      rcases resultUnit with ⟨⟩
      exact Hrestored.2
  have Houtput :
      (((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
          recNameMap allIndNames allowPrimitive types recNames env).bind
        fun restoredEnv =>
          ((·.2) <$> Lean4Lean.restoreNestedConstructors res loweredEnv
            allIndNames allowPrimitive types env).bind fun validationEnv =>
          ((·.2) <$> Lean4Lean.restoreNestedHeaders loweredEnv allIndNames
            allowPrimitive types env).bind fun auxiliaryHeaderEnv =>
          (Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
            lparams safety fuel types res).bind fun _ =>
          (Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
            lparams safety fuel res recNameMap allIndNames types recNames).bind
            fun _ =>
          (Lean4Lean.validateRestoredRecursorRules.run restoredEnv loweredEnv
            lparams safety fuel res recNameMap allIndNames types recNames).bind
            fun _ =>
          (Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv lparams
            safety fuel res).bind fun _ => Except.pure restoredEnv).WF
        (RestoredAfterInstallResult res env loweredEnv recNameMap allIndNames
          types lparams safety allowPrimitive fuel recNames Validated) :=
    HrestoredEnv.bind fun restoredEnv HrestoredData => by
      rcases HrestoredData with ⟨Hrestored, Hprimitive⟩
      exact HvalidationEnv.bind fun validationEnv HvalidationEnv => by
        exact HauxiliaryHeaderEnv.bind fun auxiliaryHeaderEnv
            HauxiliaryHeaderEnv => by
          have Hparameter :
            (Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
              lparams safety fuel types res).WF fun _ =>
                Lean4Lean.validateRestoredConstructorParameters.run
                  auxiliaryHeaderEnv lparams safety fuel types res = .ok () := by
            intro unit hrun
            rcases unit with ⟨⟩
            exact hrun
          exact Hparameter.bind fun _ Hparameter => by
            have HrecursorTypes :
                (Lean4Lean.validateRestoredRecursorTypes.run validationEnv
                  loweredEnv lparams safety fuel res recNameMap allIndNames
                    types recNames).WF fun _ =>
                  Lean4Lean.validateRestoredRecursorTypes.run validationEnv
                    loweredEnv lparams safety fuel res recNameMap allIndNames
                      types recNames = .ok () := by
              intro unit hrun
              rcases unit with ⟨⟩
              exact hrun
            exact HrecursorTypes.bind fun _ HrecursorTypes => by
              have HrecursorRules :
                  (Lean4Lean.validateRestoredRecursorRules.run restoredEnv
                    loweredEnv lparams safety fuel res recNameMap allIndNames
                      types recNames).WF fun _ =>
                    Lean4Lean.validateRestoredRecursorRules.run restoredEnv
                      loweredEnv lparams safety fuel res recNameMap allIndNames
                        types recNames = .ok () := by
                intro unit hrun
                rcases unit with ⟨⟩
                exact hrun
              exact HrecursorRules.bind fun _ HrecursorRules => by
                have Hvalidated := Hvalidate restoredEnv validationEnv
                  auxiliaryHeaderEnv (by
                  simpa [recNames, recNameMap, allIndNames] using Hrestored)
                  (by simpa [allIndNames] using HvalidationEnv)
                  (by simpa [allIndNames] using HauxiliaryHeaderEnv)
                  Hparameter (by
                    simpa [recNames, recNameMap, allIndNames] using
                      HrecursorTypes)
                  (by simpa [recNames, recNameMap, allIndNames] using
                    HrecursorRules)
                have HvalidatedRun :
                  (Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv
                    lparams safety fuel res).WF fun _ =>
                      Validated restoredEnv ∧
                      Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv
                        lparams safety fuel res = .ok () := by
                  intro unit hrun
                  exact ⟨Hvalidated unit hrun, by simpa using hrun⟩
                exact HvalidatedRun.bind fun _ Hresult =>
                  Except.WF.pure (show
                    RestoredAfterInstallResult res env loweredEnv recNameMap
                      allIndNames types lparams safety allowPrimitive fuel
                        recNames Validated
                        restoredEnv from
                      ⟨Hrestored,
                        Hprimitive,
                        ⟨validationEnv, HvalidationEnv⟩,
                        ⟨auxiliaryHeaderEnv, HauxiliaryHeaderEnv, Hparameter,
                          Hresult.2⟩,
                        ⟨validationEnv, HvalidationEnv, HrecursorTypes⟩,
                        HrecursorRules,
                        Hresult.1⟩)
  simpa [Environment.restoreNestedAfterInstall, recNames, recNameMap,
    allIndNames, StateT.run, bind, Except.bind, pure] using Houtput

end VerifyInductive
end Lean4Lean
