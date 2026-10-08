import Lean4Lean.Verify.Inductive.Nested.AuxiliaryFinalTrace

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Exact auxiliary-restoration evidence

The operational auxiliary-restoration loop and its semantic interpretation
have the same recursive shape.  This module packages the per-step semantic
and final well-formedness evidence together, then folds that package over the
exact `StateForMTrace`.  Keeping the two traces synchronized here prevents a
final-assembly proof from choosing unrelated auxiliary recursors or rules.
-/

/-- Semantic and final-WF evidence for one exact auxiliary restoration step.
The abstract recursor and rule batch are selected by `semantics`; the two WF
fields are therefore indexed by those same values. -/
structure RestoredAuxiliaryStepFinalEvidence
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType)
    (safety : DefinitionSafety) (trEnv recursorEnv ruleEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv)
    (priorRecursors : List VConstVal) where
  semantics : RestoredAuxiliaryStepShape decl block main safety trEnv
    Hstep priorRecursors
  recursorWF : semantics.recursor.toVConstant.WF recursorEnv
  rulesWF : ∀ rule ∈ semantics.rules, rule.WF ruleEnv

end VerifyInductive
end Lean4Lean
