import Lean4Lean.Verify.Inductive.Recursor.Metadata

/-! # The rule coverage of the recursor installation (named stub, owner Rules)

The frozen interface `RecursorCheck.trRecs` records PR #43's `TrRecursor`, whose rule clause
translates every kernel rule's reduct. The reducts are the generated equations' right-hand
sides (`TrRecursorRule`), which the rule phase proves from the recursor internals (the source
branch's `Rules/**`). To build a `RecursorCheck` the recursor phase needs that coverage before
a `RecursorCheck` exists, so it is stated here over the installation. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- WAVE 2 STUB (Rules): each installed kernel recursor's rules are, in order, the generated
equations of the constructors its owner owns (the source branch's `RecursorCheck.trRules`,
`Rules/RuleTranslations.lean`, stated over the installation). -/
theorem RecursorInstallation.rulesCoveredStub (H : RecursorInstallation R outEnv) :
    List.Forall₂ (fun (owner : Fin H.generationSignature.families.size)
        (e : ConstantInfo × VConstVal) =>
      ∃ rval, e.1 = .recInfo rval ∧
        List.Forall₂ (InductiveSignature.TrRecursorRule H.generationInstance H.outVEnv
          rval.levelParams) (H.generationSignature.ownedConstructors owner) rval.rules)
      (List.finRange H.generationSignature.families.size) H.entries := by
  have := H; sorry

end VerifyInductive
end Lean4Lean
