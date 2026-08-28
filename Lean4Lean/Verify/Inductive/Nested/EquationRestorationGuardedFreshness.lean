import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorNames

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Target recursor names which were not already guarded source recursors.
Only these names need an independent source-syntax freshness argument;
shared primary recursors are already excluded by source guardedness. -/
def targetOnlyRecursors
    (sourceRecursors targetRecursors : List Name) : List Name :=
  targetRecursors.filter fun name => !sourceRecursors.contains name

/-- The exact additional freshness seed needed when structurally restoring a
guarded expression.  It is intentionally local to the source expression and
only mentions genuinely new target recursor names. -/
def AvoidsTargetOnlyRecursors
    (sourceRecursors targetRecursors : List Name) (source : VExpr) : Prop :=
  source.containsAnyConst
    (targetOnlyRecursors sourceRecursors targetRecursors) = false

theorem AvoidsTargetOnlyRecursors.app_left
    {fn arg : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.app fn arg)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors fn := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).1

theorem AvoidsTargetOnlyRecursors.app_right
    {fn arg : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.app fn arg)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors arg := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).2

theorem AvoidsTargetOnlyRecursors.lam_domain
    {domain body : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.lam domain body)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors domain := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).1

theorem AvoidsTargetOnlyRecursors.lam_body
    {domain body : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.lam domain body)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors body := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).2

theorem AvoidsTargetOnlyRecursors.forall_domain
    {domain body : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.forallE domain body)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors domain := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).1

theorem AvoidsTargetOnlyRecursors.forall_body
    {domain body : VExpr} {sourceRecursors targetRecursors : List Name}
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (.forallE domain body)) :
    AvoidsTargetOnlyRecursors sourceRecursors targetRecursors body := by
  simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using
    (Bool.or_eq_false_iff.mp H).2

/-- Source guardedness excludes shared recursor names; target-only freshness
excludes newly installed names.  Together they justify the unchanged
constant case of structural guardedness restoration. -/
theorem AvoidsTargetOnlyRecursors.const_not_mem_target
    {sourceRecursors targetRecursors : List Name}
    {name : Name} {levels : List VLevel}
    (H : AvoidsTargetOnlyRecursors
      sourceRecursors targetRecursors (VExpr.const name levels))
    (hsource : name ∉ sourceRecursors) :
    name ∉ targetRecursors := by
  intro htarget
  have htargetOnly : name ∈
      targetOnlyRecursors sourceRecursors targetRecursors := by
    simpa [targetOnlyRecursors, htarget] using hsource
  have hnotTargetOnly : name ∉
      targetOnlyRecursors sourceRecursors targetRecursors := by
    simpa [AvoidsTargetOnlyRecursors, VExpr.containsAnyConst] using H
  exact hnotTargetOnly htargetOnly

end VerifyInductive
end Lean4Lean
