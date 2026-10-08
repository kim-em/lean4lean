import Lean4Lean.Verify.Inductive.PrimitiveConstructorCompletion
import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Equation.Build

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

/-- Declaration-facing result for a canonical primitive `AddInductive.run`.
It records the independently materialized declaration and the common
completed recursor phase, without pretending that the header-only state was
an ordinary valid context. -/
def VerifiedPrimitiveInductiveRunResult
    (source : AddInductive.Context) (skeleton : VInductDeclSkeleton)
    (envTypes : VEnv) (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats decl depth,
    ∃ Hc' : ContextWF c',
    ∃ Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
      types.toArray.toList (source.safety != .safe) decl envTypes,
    ∃ Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth,
    ∃ ctorEnv,
    ∃ R : CompletedConstructorPhases c' stats decl skeleton.nparams
      (source.safety != .safe) depth Hc'.venv types.toArray ctorEnv,
      types.toArray.toList ≠ [] ∧
      Nonempty (CompletedRecursorPhasesResult R outEnv)


end VerifyInductive
end Lean4Lean
