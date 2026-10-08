import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.ConstructorBoundary

/-! # Certified case eliminators of a nested declaration

The source declaration of a validated nested run registers its case eliminator before its
projections and restored recursors (`VInductBlock.install`). Its schema is the case part of the
nested compilation: the normalized signature of the lowered declaration with the nested
restoration (`CaseSchema.ofCompilation source s auxiliaries`). This file certifies it from the
validated run alone, without the final assembly shape (which already carries the eliminators). -/

namespace Lean4Lean.VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- **The case eliminators of a validated nested run's source declaration are certified**, in
the source environment and in every larger environment in which the names fresh in the
production source environment are fresh. -/
theorem NestedValidatedRunResult.caseEliminators
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (Hformation : NestedFormationAssembly (ves.venv (if isUnsafe then .unsafe else .safe))
      sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl) :
    ∃ es : List (Name × InductiveSignature.CaseSchema),
      VInductBlock.EliminatorsWF (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (sourceDecl.caseBlock es) ∧
      ∀ env', ves.venv (if isUnsafe then .unsafe else .safe) ≤ env' →
        (∀ n, sourceProdEnv.constants.find? n = none → env'.constants n = none) →
        VInductBlock.EliminatorsReplay env' sourceDecl (sourceDecl.caseBlock es) := by
  sorry

end Lean4Lean.VerifyInductive
