import Lean4Lean.Verify.Inductive.Equation.Canonical

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Build the ordinary abstract compilation package from a completed
constructor/recursor boundary, independently of whether formation used the
ordinary or atomic primitive installation history. -/
theorem CompletedRecursorPhasesResult.ordinaryCompilationOfRuleBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (Hrules : IotaBuildCertificate R.context.venv decl
      (H.blockCertificate rules hrules).block rules)
    (hrulesLength : rules.length = decl.ownedConstructors.length) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block := by
  let Hgenerated : GeneratedRecursors c.safety R.context.venv
      c.lparams H.elimLevel H.localContext stats indTypes H.recInfos
      H.entries := by
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  apply Hgenerated.ordinaryCompilationCertificate_ofRuleBuild H.localWF
    H.bindings H.params H.noAlias H.cardinality R.core
  · exact R.headerValues
  · exact R.constructorValues
  · rfl
  · exact Hrules
  · simpa [CompletedBlockCertificate.block] using hrulesLength
  · exact (H.blockCertificate rules hrules).names

/-- Close a completed executable recursor run against the independent
ordinary inductive specification. -/
theorem CompletedRecursorPhasesResult.addInductOfOrdinaryCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfOrdinaryCompilation
    R.formation R.core hnonempty Hcompile

/-- Nested compilation has the same completed formation boundary. -/
theorem CompletedRecursorPhasesResult.addInductOfNestedCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfNestedCompilation
    R.formation R.core hnonempty Hcompile

end VerifyInductive
end Lean4Lean
