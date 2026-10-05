import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.CompilationLemmas

/-! The legacy nested-compilation counterexample must have no finite
canonical derivation, regardless of its proposed source or provenance.
-/

namespace Lean4Lean.Tests.InductiveEquationRejection

/-- Exactly the equation admitted by the saved legacy counterexample. -/
def badRule : VDefEq where
  uvars := 0
  lhs := .sort .zero
  rhs := .forallE (.sort .zero) (.sort .zero)
  type := .sort (.succ .zero)

/-- This excludes the bad equation in any position of any candidate block,
not merely one chosen signature or one chosen auxiliary expansion. -/
theorem legacyEquationRejected {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (h : badRule ∈ block.rules) :
    ¬ CompiledInductive env source block :=
  CompiledInductive.reject_sort_lhs h rfl

/-- Adding otherwise valid generated equations before or after the bad rule
cannot make the resulting block a finite compilation. -/
theorem legacyEquationRejectedAmongRules {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} {before after : List VDefEq}
    (h : block.rules = before ++ badRule :: after) :
    ¬ CompiledInductive env source block := by
  apply legacyEquationRejected
  simp [h]

/-- The active installation interface also rejects the legacy equation:
ordinary and nested branches both supply the same finite derivation. -/
theorem activeCompilationRejectsLegacyEquation {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (h : badRule ∈ block.rules) :
    ¬ source.CompilesTo env block := by
  intro H
  exact legacyEquationRejected h H.compiled

/-- Rejection is independent of the bad rule's position in the active block. -/
theorem activeCompilationRejectsLegacyEquationAmongRules
    {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    {before after : List VDefEq} (h : block.rules = before ++ badRule :: after) :
    ¬ source.CompilesTo env block := by
  apply activeCompilationRejectsLegacyEquation
  simp [h]

#print axioms legacyEquationRejected
#print axioms legacyEquationRejectedAmongRules
#print axioms activeCompilationRejectsLegacyEquation
#print axioms activeCompilationRejectsLegacyEquationAmongRules

end Lean4Lean.Tests.InductiveEquationRejection
