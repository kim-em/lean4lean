import Lean4Lean.Environment

/-!
Certified projection checking now deliberately requires a checked canonical
`.casesOn` witness.  The kernel-facing inductive installer does not create that
later elaborator auxiliary, so a projection at this intermediate boundary is
rejected rather than accepted without a verification certificate.
-/

namespace Lean4Lean.Tests.ProjectionWithoutCasesOn

open Lean

private def structureDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LProjectionFresh
    type := .sort 1
    ctors := [{
      name := `L4LProjectionFresh.mk
      type := .forallE `value (.const ``Nat [])
        (.const `L4LProjectionFresh []) .default
    }]
  }] false

private def projectionDecl : Declaration :=
  .defnDecl {
    name := `L4LProjectionFresh.value
    levelParams := []
    type := .forallE `self (.const `L4LProjectionFresh [])
      (.const ``Nat []) .default
    value := .lam `self (.const `L4LProjectionFresh [])
      (.proj `L4LProjectionFresh 0 (.bvar 0)) .default
    hints := .abbrev
    safety := .safe
  }

run_meta do
  let source := (← getEnv).toKernelEnv
  let .ok installed := Lean4Lean.addDecl source structureDecl
    | throwError "fresh projection structure was rejected"
  if installed.find? (mkCasesOnName `L4LProjectionFresh) |>.isSome then
    throwError "inductive installation unexpectedly added `.casesOn`"
  let .error _ := Lean4Lean.addDecl installed projectionDecl
    | throwError "projection without `.casesOn` was accepted without a certificate"

end Lean4Lean.Tests.ProjectionWithoutCasesOn
