import Lean4Lean.Verify.Inductive.PrimitiveConstructorCompletion
import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.DeclaredRecursorPhases
import Lean4Lean.Verify.Inductive.CompletedRuleTranslation
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The non-inductive constructor half of a completed primitive batch
preserves closure of every mutual family visible after the header half. -/
theorem PrimitiveDeclaredConstructorsResult.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : PrimitiveDeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveDeclaredConstructorsResult H outEnv)
    (hclosed : MutualInductivesClosed headerEnv) :
    MutualInductivesClosed outEnv :=
  R.installed.closesMutuals H.context.checking.map_wf hclosed
    R.nonInductive

end VerifyInductive
end Lean4Lean
