import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.Header.Telescope
import Lean4Lean.Verify.Inductive.Rules.RuleSyntax

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Data-valued package for the exact completed recursor phase selected by a
successful semantic run.  Unlike `OrdinaryInstallation`, this retains
the existential witnesses as data and can therefore index later certificates
without proof-irrelevance erasing run identity. -/
structure LoweredRun (outEnv : Environment) where
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
  headers : HeaderEnvironment c stats loweredDecl nparams isUnsafe depth
    initialEnv indTypes headerEnv
  constructors : OrdinaryConstructorCheck headers ctorEnv
  recursors : RecursorCheck constructors.toConstructorCheck outEnv

end VerifyInductive
end Lean4Lean
