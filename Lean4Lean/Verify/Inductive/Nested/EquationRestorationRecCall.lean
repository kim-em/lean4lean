import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFieldApps
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuarded
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorNames

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Exact componentwise restoration of a generated recursor application
assembles the special guarded-recCall branch.  Target recursor membership is
derived from the ordered executable name map; target major-field shape is
derived structurally from finite hit provenance; target argument guardedness
is derived pointwise from their restoration certificates. -/
theorem GuardedExprRestoration.recursorCallOfComponents
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (Hnames : RestoredRecursorNames auxRec sourceRecursors targetRecursors)
    (hsourceMem : sourceRecursor ∈ sourceRecursors)
    (hsourceMajor : sourceMajor.IsFieldApp fieldVars depth)
    (Hwhole : VExprRestoration plan.Relates
      (VExpr.mkApps (.const sourceRecursor levels)
        (sourceInit ++ [sourceMajor]))
      (VExpr.mkApps
        (.const (auxRec.getD sourceRecursor sourceRecursor) levels)
        (targetInit ++ [targetMajor])))
    (Hmajor : VExprRestoration plan.Relates sourceMajor targetMajor)
    (Hargs : List.Forall₂
      (GuardedExprRestoration plan.Relates sourceRecursors
        targetRecursors fieldVars depth)
      (sourceInit ++ [sourceMajor]) (targetInit ++ [targetMajor])) :
    GuardedExprRestoration plan.Relates sourceRecursors targetRecursors
      fieldVars depth
      (VExpr.mkApps (.const sourceRecursor levels)
        (sourceInit ++ [sourceMajor]))
      (VExpr.mkApps
        (.const (auxRec.getD sourceRecursor sourceRecursor) levels)
        (targetInit ++ [targetMajor])) := by
  apply GuardedExprRestoration.recCall sourceRecursor
    (auxRec.getD sourceRecursor sourceRecursor) levels levels sourceInit
      targetInit sourceMajor targetMajor
  · exact hsourceMem
  · exact Hnames.getD_mem hsourceMem
  · exact hsourceMajor
  · exact Hatomic.isFieldApp Hmajor hsourceMajor
  · exact Hwhole
  · intro target htarget
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hargs target htarget with
      ⟨source, _hsource, Hrestored⟩
    exact Hrestored.targetGuarded

/-- Direct target-guardedness consequence for the exact restored recursor
application. -/
theorem VExpr.GuardedIota.restoredRecursorCall
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (Hnames : RestoredRecursorNames auxRec sourceRecursors targetRecursors)
    (hsourceMem : sourceRecursor ∈ sourceRecursors)
    (hsourceMajor : sourceMajor.IsFieldApp fieldVars depth)
    (Hwhole : VExprRestoration plan.Relates
      (VExpr.mkApps (.const sourceRecursor levels)
        (sourceInit ++ [sourceMajor]))
      (VExpr.mkApps
        (.const (auxRec.getD sourceRecursor sourceRecursor) levels)
        (targetInit ++ [targetMajor])))
    (Hmajor : VExprRestoration plan.Relates sourceMajor targetMajor)
    (Hargs : List.Forall₂
      (GuardedExprRestoration plan.Relates sourceRecursors
        targetRecursors fieldVars depth)
      (sourceInit ++ [sourceMajor]) (targetInit ++ [targetMajor])) :
    (VExpr.mkApps
      (.const (auxRec.getD sourceRecursor sourceRecursor) levels)
      (targetInit ++ [targetMajor])).GuardedIota
        targetRecursors fieldVars depth :=
  (GuardedExprRestoration.recursorCallOfComponents Hatomic Hnames
    hsourceMem hsourceMajor Hwhole Hmajor Hargs).targetGuarded

end VerifyInductive
end Lean4Lean
