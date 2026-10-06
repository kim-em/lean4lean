import Lean4Lean.Verify.Inductive.RuleTranslationAssembly
import Lean4Lean.Verify.Inductive.RuleTranslation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The completed recursor phase determines the joint generation and concrete
metadata witness. No rule, telescope, or equation witness is chosen by the
caller. Source nonemptiness is needed only when forming the installation
certificate. -/
theorem CompletedRecursorPhasesResult.canonicalCompletedRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    Nonempty (CompletedRuleTranslationResult H) :=
  H.completedRuleTranslation_of H.ruleRhsTranslations

end VerifyInductive

end Lean4Lean
