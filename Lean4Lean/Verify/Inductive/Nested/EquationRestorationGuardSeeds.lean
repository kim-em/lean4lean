import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedFreshness
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRhs
import Lean4Lean.Verify.Inductive.Constructor.Positivity

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Producer-facing guardedness seeds for one exact restored equation.
Ordered name alignment comes from the primary/auxiliary restoration traces;
freshness comes from checking the new recursor names before installing them.
The context field is the independently translated opening scope, not a
predicate over arbitrary expressions. -/
structure RestoredRuleGuardSeeds
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldRule newRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldRule newRule}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldRule newRule Hrule sourceEnv targetEnv Us)
    (sourceRecursors targetRecursors : List Name) : Prop where
  recursorNames : RestoredRecursorNames auxRec sourceRecursors targetRecursors
  newNamesFresh : ∀ name ∈
    targetOnlyRecursors sourceRecursors targetRecursors,
    sourceEnv.constants name = none
  sourceContextFree : VLCtx.NoIndConsts
    (targetOnlyRecursors sourceRecursors targetRecursors)
    (abstractForallContext [] Hrhs.sourceScope)

/-- Exact translation of the opened old equation body converts the
producer's new-name freshness into the structural freshness seed needed by
guarded restoration. -/
theorem RestoredRuleGuardSeeds.sourceBodyFresh
    (H : RestoredRuleGuardSeeds Hrhs sourceRecursors targetRecursors)
    (hproj : ProjectionConstPreservation) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      Hrhs.sourceBody := by
  exact checkPositivityStep.TrExprS.noFreshConsts H.newNamesFresh
    H.sourceContextFree (fun Hproj hfree => hproj _ Hproj hfree)
    Hrhs.body.sourceTranslation

end VerifyInductive
end Lean4Lean
