import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Environment.Extension

/-! # Canonical `Eq` in the safety-indexed models

The invariant that the prelude's `Eq` declaration establishes (`QuotReadyEnvs`);
`Prelude/Eq.lean` proves it for that declaration. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Abstract `Eq` with its canonical type is available in every safety-indexed model
(`QuotReady` at every safety level). This is the invariant needed after the prelude's `Eq`
declaration and before quotient initialization. -/
def QuotReadyEnvs (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).QuotReady

end VerifyInductive
end Lean4Lean
