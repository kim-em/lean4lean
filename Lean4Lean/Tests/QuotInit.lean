import Lean4Lean.Environment

/-! Quotient initialization.

The executable's `init_quot`, run after adding `Init.Prelude`'s `Eq` to an
empty environment, installs `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`
as Lean's kernel does, exactly (binder names and binder annotations
included; in particular the major premise of `Quot.ind` is an explicit
binder, see `divergences.md`), and a second `init_quot` is a no-op.

The comparison of these types with the closed forms of
`Environment.addQuot_eq` (`Lean4Lean/Verify/Environment/Quot.lean`) and
with the abstract constants installed by `VEnv.addQuot` returns with the
verification of `Verify/Environment` (wave 1B). -/

namespace Lean4Lean.Tests.QuotInit

open Lean Meta

deriving instance BEq for QuotKind

def check (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

run_meta do
  let env ← getEnv
  let some (.inductInfo I) := env.find? ``Eq | throwError "no Eq"
  let some (.ctorInfo C) := env.find? ``Eq.refl | throwError "no Eq.refl"
  let refl : Constructor := { name := ``Eq.refl, type := C.type }
  let eqDecl := Declaration.inductDecl I.levelParams I.numParams
    [{ name := ``Eq, type := I.type, ctors := [refl] }] I.isUnsafe
  let empty ← mkEmptyEnvironment
  let kenv ← match Lean4Lean.addDecl empty.toKernelEnv eqDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected Eq: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  check (!kenv.quotInit) "quotient module unexpectedly initialized"
  let kenv ← match Lean4Lean.addDecl kenv .quotDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected init_quot: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  check kenv.quotInit "init_quot did not set quotInit"
  for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    let some (.quotInfo ci) := kenv.find? n | throwError "Lean4Lean did not install {n}"
    let some (.quotInfo ci₀) := env.find? n | throwError "missing {n}"
    -- Exact comparison, binder info included.
    check (ci.levelParams == ci₀.levelParams && ci.type.equal ci₀.type && ci.kind == ci₀.kind)
      s!"{n}: Lean4Lean and Lean's kernel disagree"
  -- A second `init_quot` is a no-op.
  match Lean4Lean.addDecl kenv .quotDecl (check := true) with
  | .error e => throwError "repeated init_quot rejected: {e.toMessageData {}}"
  | .ok kenv' => check (kenv'.find? ``Quot.lift |>.isSome) "repeated init_quot lost Quot.lift"

end Lean4Lean.Tests.QuotInit
