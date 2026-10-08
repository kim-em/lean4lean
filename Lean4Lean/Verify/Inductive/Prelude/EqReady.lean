import Lean4Lean.Verify.Inductive.Install.Environments
import Lean4Lean.Verify.Environment.Extension

/-! # Canonical `Eq` in the safety-indexed models

The invariants that the prelude's `Eq` declaration establishes (`CanonicalEqEnvs`) and that
hold on either side of it (`EqReadyOrAbsent`); `Prelude/Eq.lean` proves them for that
declaration. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Abstract `Eq` with its canonical type is available in every safety-indexed model
(`QuotReady` at every safety level). This is the invariant needed after the prelude's `Eq`
declaration and before quotient initialization. -/
def CanonicalEqEnvs (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).QuotReady

/-- Either `Eq` is absent from the kernel environment (before the prelude's `Eq`
declaration), or every safety-indexed model contains abstract `Eq` with its canonical type
(`CanonicalEqEnvs`). This disjunction holds both before and after the `Eq` declaration. -/
def EqReadyOrAbsent (env : Environment) (ves : VEnvs) : Prop :=
  env.constants.find? ``Eq = none ∨ CanonicalEqEnvs ves

theorem EqReadyOrAbsent.ofCanonical
    (H : CanonicalEqEnvs ves) : EqReadyOrAbsent env ves :=
  Or.inr H

theorem CanonicalEqEnvs.mono
    (H : CanonicalEqEnvs ves)
    (hle : ∀ safety, ves.venv safety ≤ target.venv safety) :
    CanonicalEqEnvs target := by
  intro safety
  exact (hle safety).constants (H safety)

end VerifyInductive
end Lean4Lean
