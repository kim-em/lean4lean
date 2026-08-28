import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaSourceTyping
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaLhsApplication

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Restored primary-iota left-hand-side source typing -/

/-- The application certificate plus the exact restoration target telescope
constructs the complete source-typing package. Context well-formedness is
derived by `sourceTypingOfTargetLhs`; the certificate supplies only the LHS
judgment that cannot follow from environment monotonicity. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.LhsApplicationCertificate.sourceTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    {S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor}
    {targetEnv : VEnv} {targetScope : VLCtx}
    (C : S.LhsApplicationCertificate targetEnv)
    (HtargetContext :
      (abstractForallContext [] targetScope).WF targetEnv Us.length)
    (hdomains : targetScope.toCtx.reverse = S.source.domains) :
    RestoredPrimaryIotaSourceTyping targetEnv S.source :=
  S.sourceTypingOfTargetLhs HtargetContext hdomains C.targetTyping

end VerifyInductive
end Lean4Lean
