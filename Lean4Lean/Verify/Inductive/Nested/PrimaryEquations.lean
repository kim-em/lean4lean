import Lean4Lean.Verify.Inductive.Equation.Setup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The production lookup used by a primary restoration step is the exact
generated recursor entry at the corresponding source-family position.  The
ordinary equation proof and the restoration trace can therefore be indexed by
one shared rule list. -/
theorem RecursorPhasesResult.restoredPrimaryInfo_eq_generated
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
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

/-- Exact pointwise join between ordinary generated-rule semantics and the
rule selected by executable primary restoration.  No equation witness is
chosen by the caller: the installed recursor lookup fixes the generated entry,
and `RulesRestoration.entry` fixes the restored rule at the same constructor
index. -/
theorem RecursorPhasesResult.restoredPrimaryGeneratedRuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (owner : Nat) (hentry : owner < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[owner]!.name)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrestored : i < Hstep.restored.newInfo.rules.length) :
    ∃ hsource : i < (H.generated.entry owner hentry).info.rules.length,
      ∃ A : H.GeneratedRuleAlignment owner hentry i hctor,
        RuleRestoration result outEnv auxRec oldRecName
          Hstep.restored.newRecName
          (H.generated.entry owner hentry).info.rules[i]
          Hstep.restored.newInfo.rules[i] := by
  rcases H.generatedRuleAlignment owner hentry i hctor with ⟨A⟩
  have holdInfo := H.restoredPrimaryInfo_eq_generated owner hentry Hstep
    holdRecName
  have hsource : i < Hstep.oldInfo.rules.length := by
    rw [holdInfo]
    exact A.sourceRule_lt
  have Hrule := Hstep.restored.restoration.rules.entry i hsource hrestored
  exact ⟨A.sourceRule_lt, A, by simpa only [holdInfo] using Hrule⟩

/-- A complete primary-rule certificate is, in particular, the append-facing
build certificate consumed by nested compilation.  Keeping this projection
explicit lets the restored-primary equation proof target the pointwise
`IotaListCertificate` judgment directly; list coverage is then no longer a
separate callback. -/
theorem IotaListCertificate.toBuild
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    {rules : List VDefEq}
    (H : IotaListCertificate env decl block rules) :
    IotaBuildCertificate env decl block rules where
  covered := Nat.le_of_eq H.length
  shapes i hrule hctor := H.rules i hctor hrule

/-- A complete restored-primary nested rule list supplies the append-facing
certificate used by restoration assembly. -/
theorem NestedIotaListCertificate.toBuild
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : NestedIotaListCertificate decl block rules) :
    NestedIotaBuildCertificate decl block rules where
  covered := Nat.le_of_eq H.length
  shapes i hrule hctor := H.rules i hctor hrule

/-- Source-family semantics determine the exact primary recursor certificate.
Together with pointwise source iota rules, this packages the primary inputs
and exact flattened constructor count used by nested compilation assembly.

The block remains an argument, so later auxiliary recursors and rules may be
present without entering the source-family traversal. -/
theorem RestoredSourceInductiveSemanticTrace.primaryCompilationPrefix
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {primaryRecursors : List VConstVal}
    {block : VInductBlock} {primaryRules : List VDefEq}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners primaryRecursors)
    (htypes : decl.types = owners)
    (Hrules : NestedIotaListCertificate decl block primaryRules) :
    NestedRecursorCertificate decl primaryRecursors ∧
      NestedIotaBuildCertificate decl block primaryRules ∧
      primaryRules.length = decl.ownedConstructors.length := by
  exact ⟨H.recursorCertificate htypes, Hrules.toBuild, Hrules.length⟩

end VerifyInductive
end Lean4Lean
