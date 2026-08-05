import Lean4Lean.Environment

/-!
Executable acceptance regressions for ordinary and mutually recursive
inductives. Declarations are assembled directly so the tests exercise
`Lean4Lean.addDecl`, rather than Lean's host elaborator/kernel.
-/

namespace Lean4Lean.Tests.RecursiveInductive

open Lean

def natLikeDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LNatLike
    type := .sort 1
    ctors := [{
      name := `L4LNatLike.zero
      type := .const `L4LNatLike []
    }, {
      name := `L4LNatLike.succ
      type := .forallE `n (.const `L4LNatLike [])
        (.const `L4LNatLike []) .default
    }]
  }] false

def evenOddDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LEven
    type := .sort 1
    ctors := [{
      name := `L4LEven.zero
      type := .const `L4LEven []
    }, {
      name := `L4LEven.succ
      type := .forallE `n (.const `L4LOdd [])
        (.const `L4LEven []) .default
    }]
  }, {
    name := `L4LOdd
    type := .sort 1
    ctors := [{
      name := `L4LOdd.succ
      type := .forallE `n (.const `L4LEven [])
        (.const `L4LOdd []) .default
    }]
  }] false

private def expectAccepted (label : String) (env : Kernel.Environment)
    (decl : Declaration) : MetaM Unit := do
  match Lean4Lean.addDecl env decl with
  | .ok _ => pure ()
  | .error e =>
    throwError "{label} was rejected: {← (e.toMessageData {}).toString}"

run_meta do
  let env := (← getEnv).toKernelEnv
  expectAccepted "ordinary recursive inductive" env natLikeDecl
  expectAccepted "mutually recursive inductive" env evenOddDecl

end Lean4Lean.Tests.RecursiveInductive
