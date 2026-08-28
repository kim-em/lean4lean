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

/-- Extend a safe block without asking the executable-to-abstract boundary to
re-prove canonicality of `Eq`.  The persistent invariant supplies canonical
equality in the safe model used to check the block. -/
theorem BlockCertificate.extendSafeOfCanonicalEq
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  exact H.extendSafe wf hdecl hcompile horigins hclosed hconstructorOwners
    hconstructorSemantics

/-- Safe inductive installation preserves canonical equality at all observer
safety levels. -/
theorem BlockCertificate.extendSafeOfQuotReady
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hEq : CanonicalEqEnvs ves)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases H.extendSafeOfCanonicalEq wf hdecl hcompile horigins
      hclosed hconstructorOwners hconstructorSemantics with ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

/-- An unsafe hidden inductive installation also preserves canonical equality
at all observer safety levels. -/
theorem BlockCertificate.extendUnsafeOfHiddenOfQuotReady
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WF prodEnv)
    (hEq : CanonicalEqEnvs ves)
    (hdecl : decl.WF (ves.venv .unsafe))
    (hcompile : decl.CompilesTo (ves.venv .unsafe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (outVEnv.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases H.extendUnsafeOfHidden wf hdecl hcompile horigins hunsafe
      hclosed hconstructorOwners hconstructorSemantics with
    ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

end VerifyInductive
end Lean4Lean
