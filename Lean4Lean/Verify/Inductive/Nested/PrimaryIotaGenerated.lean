import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Verify.Inductive.Nested.Replacement
import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.CompletedRecursorSetup
import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.Header.LoopType
import Lean4Lean.Verify.Inductive.Recursor.Rules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Data-valued package for the exact completed recursor phase selected by a
successful semantic run.  Unlike `SemanticRunWithStatsResult`, this retains
the existential witnesses as data and can therefore index later certificates
without proof-irrelevance erasing run identity. -/
structure NestedInstalledProduction (outEnv : Environment) where
  c : AddInductive.Context
  stats : AddInductive.InductiveStats
  loweredDecl : VInductDecl
  nparams : Nat
  depth : Nat
  isUnsafe : Bool
  initialEnv : VEnv
  indTypes : Array InductiveType
  headerEnv : Environment
  ctorEnv : Environment
  headers : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
    initialEnv indTypes headerEnv
  constructors : ConstructorPhasesResult headers ctorEnv
  production : CompletedRecursorPhasesResult constructors.completed outEnv

end VerifyInductive
end Lean4Lean
