import Lean4Lean.Verify.Inductive.Run.SemanticRun

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The independent ordinary-inductive judgment produced by a successful
checker run, including the translation of the exact source syntax.  Keeping
the source translation beside `AddInduct` prevents a final-environment model
from silently being attributed to a different (for example, lowered)
declaration. -/
structure InductiveSpecificationResult
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (finalVEnv : VEnv) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  source : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  extension : VEnv.AddInduct sourceEnv decl finalVEnv

/-- Ordinary runs and primitive-bootstrap runs share the same independent
source judgment; this alias documents the ordinary use site. -/
abbrev OrdinaryInductiveSpecificationResult := InductiveSpecificationResult

end VerifyInductive
end Lean4Lean
