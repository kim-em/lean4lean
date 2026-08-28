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
  semantics : RestoredAuxiliaryStepSemantics decl block main safety trEnv
    Hstep priorRecursors
  recursorWF : semantics.recursor.toVConstant.WF recursorEnv
  rulesWF : ∀ rule ∈ semantics.rules, rule.WF ruleEnv

/-- Fold exact pointwise auxiliary evidence over the executable restoration
trace.  The semantic and final-WF traces share every step witness and expose
one common final recursor/rule pair. -/
theorem StateForMTrace.auxiliaryFinalEvidence
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv recursorEnv ruleEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (Hsteps : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      (priorRecursors : List VConstVal),
      Nonempty (RestoredAuxiliaryStepFinalEvidence decl block main safety
        trEnv recursorEnv ruleEnv Hstep priorRecursors))
    (priorRecursors : List VConstVal) (priorRules : List VDefEq) :
    ∃ finalRecursors finalRules,
      ∃ Hsemantic : RestoredAuxiliarySemanticTrace decl block main safety
        trEnv Htrace priorRecursors priorRules finalRecursors finalRules,
        RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
          ruleEnv Hsemantic priorRecursors priorRules finalRecursors
            finalRules := by
  induction Htrace generalizing priorRecursors priorRules with
  | nil =>
      exact ⟨priorRecursors, priorRules, .nil _ _ _, .nil _ _ _⟩
  | @cons head source middle tail target Hstep Htail ih =>
      rcases Hsteps head source middle Hstep priorRecursors with
        ⟨Hhead⟩
      let nextRecursors := priorRecursors ++ [Hhead.semantics.recursor]
      let nextRules := priorRules ++ Hhead.semantics.rules
      rcases ih (nextRecursors) (nextRules) with
        ⟨finalRecursors, finalRules, Hrest, Hfinal⟩
      let Hsemantic : RestoredAuxiliarySemanticTrace decl block main safety
          trEnv (.cons Hstep Htail) priorRecursors priorRules finalRecursors
            finalRules :=
        .cons Hstep Htail Hhead.semantics Hrest
      exact ⟨finalRecursors, finalRules, Hsemantic,
        .cons Hstep Htail Hhead.semantics Hrest Hhead.recursorWF
          Hhead.rulesWF Hfinal⟩

/-- Empty-prefix specialization used by final nested assembly. -/
theorem StateForMTrace.auxiliaryFinalEvidenceEmpty
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv recursorEnv ruleEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    (Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (Hsteps : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      (priorRecursors : List VConstVal),
      Nonempty (RestoredAuxiliaryStepFinalEvidence decl block main safety
        trEnv recursorEnv ruleEnv Hstep priorRecursors)) :
    ∃ auxiliaryRecursors auxiliaryRules,
      ∃ Hsemantic : RestoredAuxiliarySemanticTrace decl block main safety
        trEnv Htrace [] [] auxiliaryRecursors auxiliaryRules,
        RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
          ruleEnv Hsemantic [] [] auxiliaryRecursors auxiliaryRules := by
  exact Htrace.auxiliaryFinalEvidence Hsteps [] []

/-- Result-facing specialization: the final auxiliary lists, both semantic
traces, and their executable cardinality all come from the exact restoration
suffix stored in `H`. -/
theorem RestoredNestedDeclarationsResult.auxiliaryFinalEvidence
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv recursorEnv ruleEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {types : List InductiveType}
    {auxRecNames : List Name} {out : Unit × Environment}
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (Hsteps : ∀ oldRecName stepSource stepTarget
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName stepSource stepTarget)
      (priorRecursors : List VConstVal),
      Nonempty (RestoredAuxiliaryStepFinalEvidence decl block main safety
        trEnv recursorEnv ruleEnv Hstep priorRecursors)) :
    ∃ auxiliaryRecursors auxiliaryRules,
      ∃ Hsemantic : RestoredAuxiliarySemanticTrace decl block main safety
        trEnv H.auxiliaries [] [] auxiliaryRecursors auxiliaryRules,
        RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
            ruleEnv Hsemantic [] [] auxiliaryRecursors auxiliaryRules ∧
          auxiliaryRecursors.length = auxRecNames.length := by
  rcases H.auxiliaries.auxiliaryFinalEvidenceEmpty Hsteps with
    ⟨auxiliaryRecursors, auxiliaryRules, Hsemantic, Hwf⟩
  exact ⟨auxiliaryRecursors, auxiliaryRules, Hsemantic, Hwf, by
    simpa using Hsemantic.recursorsLength⟩

end VerifyInductive
end Lean4Lean
