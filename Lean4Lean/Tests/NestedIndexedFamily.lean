import Lean4Lean.Environment

/-!
Records a divergence from the C++ kernel (see `divergences.md`,
`Lean4Lean.validateNestedAuxiliaries`): a nested occurrence of an *indexed*
family is accepted by the C++ kernel and rejected by lean4lean.

Nested lowering stores each nested occurrence `I Ds` applied to the parameters
only, so for a family with indices the stored term is a type family, not a type.
The C++ kernel only type-checks it; lean4lean additionally requires it to be a
sort (`ensureSort`), because the verification closes it into a forall over the
parameters. If this test starts failing because lean4lean accepts the
declaration, remove the corresponding `divergences.md` entry.
-/

namespace Lean4Lean.Tests.NestedIndexedFamily

open Lean

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

/-- `inductive VTree | node : Vec VTree 2 → VTree` -/
def vtreeDecl : Declaration :=
  .inductDecl [] 0
    [{ name := `VTree
       type := .sort 1
       ctors := [{
         name := `VTree.node
         type := .forallE `xs
           (mkApp2 (mkConst ``Vec) (mkConst `VTree) (mkNatLit 2))
           (mkConst `VTree) .default }] }]
    false

run_meta do
  let kenv := (← getEnv).toKernelEnv
  match Lean.Kernel.Environment.addDecl kenv {} vtreeDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "the C++ kernel rejected the nested indexed family: \
      {← (e.toMessageData {}).toString}"
  match Lean4Lean.addDecl kenv vtreeDecl with
  | .ok _ =>
    throwError "lean4lean now accepts the nested indexed family; \
      update divergences.md and this test"
  | .error _ => pure ()

end Lean4Lean.Tests.NestedIndexedFamily
