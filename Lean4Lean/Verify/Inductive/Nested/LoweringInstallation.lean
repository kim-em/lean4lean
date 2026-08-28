import Lean4Lean.Verify.Inductive.Nested.LoweringTrace
import Lean4Lean.Verify.Inductive.Nested.Compilation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Build the lockstep constructor trace from verified lowered installation.
The only list premise is that all mapped targets belong to the installed
owner; in the family specialization this is immediate because `targets` is
that owner's constructor list. -/
theorem RestoredConstructorMappingTrace.ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hprod : RecursorPhasesResult R loweredEnv)
    (howner : owner ∈ indTypes.toList)
    (Hmapping : LoweredConstructorMappings mappingEnv params nparams result
      sources state (targets, finalState))
    (Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv)
    (Htargets : ∀ target ∈ targets, target ∈ owner.ctors) :
    RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
      c.safety c.lparams sources state targets finalState sourceProdEnv
        targetProdEnv := by
  cases Hmapping with
  | nil =>
    cases Htrace
    exact .nil _ _
  | cons Hhead Htail =>
    cases Htrace with
    | cons Hstep Hsteps =>
      have Hmetadata := Hstep.metadataOfInstalled Hprod howner
        (Htargets _ (by simp)) rfl
      apply RestoredConstructorMappingTrace.cons Hhead Hstep
      · exact Hmetadata.1
      · exact Hmetadata.2.1
      · exact Hmetadata.2.2.1
      · exact Hstep.oldType_eq_ofInstalled Hprod howner
          (Htargets _ (by simp)) rfl
      · apply RestoredConstructorMappingTrace.ofInstalled Hprod howner
          Htail Hsteps
        intro target htarget
        exact Htargets target (by simp [htarget])

/-- End-to-end freshness bridge for restoration: lowering proves auxiliary
families fresh in the production source, and lockstep installation turns that
into abstract freshness for every constructor recognized through those
families. -/
theorem NestedLoweringRun.restoreAuxConstructorsFreshOfInstallation
    (H : NestedLoweringRun sourceProdEnv fuel nparams types initialState
      (result, finalState))
    (Hinstall : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv :=
  Hinstall.restoreAuxConstructorsFresh hwf Howners
    (H.resultFamilyNamesFreshOfEmpty hwf hempty)

end VerifyInductive
end Lean4Lean
