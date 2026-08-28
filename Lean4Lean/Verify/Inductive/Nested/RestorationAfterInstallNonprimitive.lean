import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.Nested.RestorationNonprimitive

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Primitive-safe post-install restoration

The generic post-install verifier predates the primitive-safe restoration
trace and projects it away before auxiliary validation.  This exact-run
variant retains the companion trace through the same executable bind. -/

/-- Successful nested restoration together with the primitive-safety facts
returned by every exact `checkName` and the subsequent validation result. -/
structure PrimitiveSafeRestoredAfterInstallResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) (allowPrimitive : Bool)
    (Validated : Environment → Prop) (outEnv : Environment) : Prop where
  restoration : Nonempty (RestoredNestedDeclarationsResult res loweredEnv
    sourceEnv recNameMap allIndNames types auxRecNames ((), outEnv))
  primitiveSafe : ∃ entries,
    PrimitiveSafeFreshConstantTrace allowPrimitive sourceEnv entries outEnv
  validated : Validated outEnv

/-- Compose the exact declaration-restoration refinement, its independently
proved primitive-safe companion, and the unchanged auxiliary validation pass.
Both restoration facts are obtained from one successful executable result. -/
theorem Environment.restoreNestedAfterInstall.primitiveSafeWF
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
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv types).2 (types.map (·.name))
        types (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety
      allowPrimitive fuel res).WF fun outEnv =>
        PrimitiveSafeRestoredAfterInstallResult res env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 allowPrimitive
          Validated outEnv := by
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
      rcases restored with ⟨resultUnit, restoredEnv⟩
      rcases resultUnit with ⟨⟩
      exact Hrestored
  have Houtput :
      (((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
          recNameMap allIndNames allowPrimitive types recNames env).bind
        fun restoredEnv =>
          (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
            res).bind fun _ => Except.pure restoredEnv).WF
        (PrimitiveSafeRestoredAfterInstallResult res env loweredEnv recNameMap
          allIndNames types recNames allowPrimitive Validated) :=
    HrestoredEnv.bind fun restoredEnv Hrestored => by
      exact (Hvalidate restoredEnv (by
        simpa [recNames, recNameMap, allIndNames] using
          Hrestored.1)).bind fun _ Hvalidated =>
            Except.WF.pure ⟨Hrestored.1, Hrestored.2, Hvalidated⟩
  simpa [Environment.restoreNestedAfterInstall, recNames, recNameMap,
    allIndNames, StateT.run, bind, Except.bind, pure] using Houtput

/-- Lowering/ordinary-production specialization of the primitive-safe
post-install verifier.  The declaration lookup and telescope premises are
derived exactly as in `ofLoweringWF`; the output additionally retains every
successful primitive-name check. -/
theorem Environment.restoreNestedAfterInstall.ofLoweringPrimitiveSafeWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
    (Hlower : NestedLoweringResult c.env loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv c.env
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall c.env loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        PrimitiveSafeRestoredAfterInstallResult res c.env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 allowPrimitive
          Validated outEnv := by
  have hnparams : res.nparams = nparams := Hlower.resultNParams
  apply Environment.restoreNestedAfterInstall.primitiveSafeWF c.env
    loweredEnv lparams sourceTypes safety allowPrimitive fuel res
  · intro owner howner
    simpa [hnparams] using
      H.restorationSourcesOfLowering Hc Hlower owner howner
  · intro recName hrecName
    simpa [hnparams] using
      H.auxRestorationSourcesOfLowering Hc Hlower recName hrecName
  · exact Hc.checking.tr.map_wf
  · exact Hvalidate

end VerifyInductive
end Lean4Lean
