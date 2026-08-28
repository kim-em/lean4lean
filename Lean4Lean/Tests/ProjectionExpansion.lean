import Lean4Lean.Theory.Meta
import Lean.Util.FoldConsts

namespace Lean4Lean.Tests.ProjectionExpansion

open Lean Meta

/-- A parameterized structure makes constants introduced through implicit
projection arguments observable independently of the projected expression. -/
structure Wrap (alpha : Type u) where
  value : alpha
  tag : Bool

/- `Meta.expandProj` does not preserve the constant support of its input.
It introduces both the structure eliminator and constants recovered from the
type of a local projected value.  This is the executable counterexample to a
global `TrProj` constant-preservation law. -/
run_meta do
  let wrapNat := mkApp (mkConst ``Wrap [.zero]) (mkConst ``Nat)
  withLocalDeclD `wrapped wrapNat fun wrapped => do
    unless wrapped.getUsedConstants.isEmpty do
      throwError "a free variable unexpectedly contains constants"
    let expanded ← Lean4Lean.Meta.expandProj ``Wrap 0 wrapped
    let constants := expanded.getUsedConstants
    let casesOn := mkCasesOnName ``Wrap
    unless constants.contains casesOn do
      throwError "projection expansion did not introduce {casesOn}"
    unless constants.contains ``Nat do
      throwError "projection expansion did not recover the implicit Nat parameter"

end Lean4Lean.Tests.ProjectionExpansion
