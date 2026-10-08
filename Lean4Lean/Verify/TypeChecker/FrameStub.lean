import Lean4Lean.Verify.TypeChecker.FrameDefs

/-!
# Stub of the checker frame lemma

Temporary: the frame lemma is being proved in `Verify/TypeChecker/Frame.lean` on a sibling branch.
This file states it with `sorry` so that its consumer (`Verify/TypeChecker/GhostTelescope.lean`)
can be developed against it. Delete this file and import `Frame.lean` instead once it lands.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

theorem Methods.withFuel_framed (G : FVarId → Prop) : ∀ n, (Methods.withFuel n).Framed G := by
  sorry

end Lean4Lean.TypeChecker
