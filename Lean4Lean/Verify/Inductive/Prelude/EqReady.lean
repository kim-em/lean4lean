import Lean4Lean.Verify.Inductive.Run.Formation
import Lean4Lean.Verify.Environment.Extension

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Canonical equality is available in every safety-indexed abstract model.
This is the persistent invariant needed after Lean's bootstrap `Eq`
declaration and before quotient initialization. -/
def CanonicalEqEnvs (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).QuotReady

/-- Before the bootstrap `Eq` declaration, equality is absent from the
production environment. Afterwards, every safety-indexed abstract observer
must contain its canonical interpretation.  This disjunction is the
persistent boundary invariant across both phases of kernel bootstrap. -/
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
