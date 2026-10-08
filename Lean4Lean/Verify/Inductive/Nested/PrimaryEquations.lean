import Lean4Lean.Verify.Inductive.CompletedEquationSetup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The production lookup used by a primary restoration step is the exact
generated recursor entry at the corresponding source-family position.  The
ordinary equation proof and the restoration trace can therefore be indexed by
one shared rule list. -/
theorem CompletedRecursorPhasesResult.restoredPrimaryInfo_eq_generated
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (owner : Nat) (hentry : owner < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[owner]!.name) :
    Hstep.oldInfo = (H.generated.entry owner hentry).info := by
  let E := H.generated.entry owner hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[owner].1.name =
      some H.entries[owner].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have hstepLookup : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo Hstep.oldInfo) := by
    simpa [holdRecName] using Hstep.lookup
  exact ConstantInfo.recInfo.inj
    (Option.some.inj (hstepLookup.symm.trans hlookupE))

/-- A complete restored-primary nested rule list supplies the append-facing
certificate used by restoration assembly. -/
theorem NestedIotaListCertificate.toBuild
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : NestedIotaListCertificate decl block rules) :
    NestedIotaBuildCertificate decl block rules where
  covered := Nat.le_of_eq H.length
  shapes i hrule hctor := H.rules i hctor hrule

end VerifyInductive
end Lean4Lean
