import Lean4Lean.Environment

/-!
Front-end declaration checks that are not covered by `Lean4Lean.Tests.KernelHardening`.

The mutual-block level parameter and duplicate name checks live there, since v4.33.0-rc2
made the kernel reject both (lean4#14608).
-/

namespace Lean4Lean.Tests.Environment

open Lean

run_meta
  let env ← Lean.getEnv
  let some (.defnInfo natAdd) := env.toKernelEnv.find? ``Nat.add
    | throwError "Nat.add is not a definition"
  let partialNatAdd := { natAdd with safety := DefinitionSafety.partial }
  match (Primitive.checkDef partialNatAdd).run env.toKernelEnv
      (lparams := partialNatAdd.levelParams) with
  | .error _ => pure ()
  | .ok true => throwError "a partial definition was accepted as a primitive"
  | .ok false => throwError "a partial definition was reported as a non-primitive"

end Lean4Lean.Tests.Environment
