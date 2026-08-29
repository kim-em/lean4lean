import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSpines
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedOrdinary

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Recursor-freeness of an application includes every exact spine
argument. -/
theorem VExpr.containsAnyConst_mkApps_false_inv
    (hfree : (VExpr.mkApps fn args).containsAnyConst names = false) :
    fn.containsAnyConst names = false ∧
      ∀ arg ∈ args, arg.containsAnyConst names = false := by
  induction args generalizing fn with
  | nil => exact ⟨hfree, by simp⟩
  | cons arg args ih =>
      have H := ih (fn := .app fn arg) hfree
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
      exact ⟨H.1.1, by
        intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | htail
        · exact H.1.2
        · exact H.2 candidate htail⟩

/-- Target-only freshness of an application likewise descends to every
spine argument. -/
theorem AvoidsTargetOnlyRecursors.mkApps_args
    (H : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      (VExpr.mkApps fn args)) :
    ∀ arg ∈ args,
      AvoidsTargetOnlyRecursors sourceRecursors targetRecursors arg := by
  exact (VExpr.containsAnyConst_mkApps_false_inv H).2

/-- Exact field/result split of a restored generated minor application. -/
theorem NestedRestorationPlan.AtomicProvenance.minorSpineAlignment
    (Hatomic : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates
      (VExpr.mkApps (.bvar minorVar) (sourceFields ++ sourceResults)) target) :
    ∃ targetFields targetResults,
      target = VExpr.mkApps (.bvar minorVar)
        (targetFields ++ targetResults) ∧
      List.Forall₂ (VExprRestoration plan.Relates)
        sourceFields targetFields ∧
      List.Forall₂ (VExprRestoration plan.Relates)
        sourceResults targetResults := by
  rcases Hatomic.bvarMkAppsAlignment Hrest with
    ⟨targetArgs, htarget, Haligned⟩
  rcases checkPositivityStep.List.Forall₂.split_left Haligned with
    ⟨targetFields, targetResults, rfl, Hfields, Hresults⟩
  exact ⟨targetFields, targetResults, htarget, Hfields, Hresults⟩

/-- Pointwise structural restoration of independently recursor-free fields
automatically supplies their complete guarded-restoration alignment. -/
theorem GuardedExprRestoration.fieldsOfRecursorFree
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (hkeys : NestedRestorationPlan.RecursorKeysCovered
      auxRec sourceRecursors)
    (Haligned : List.Forall₂ (VExprRestoration plan.Relates)
      sourceFields targetFields)
    (hsourceFree : ∀ field ∈ sourceFields,
      field.containsAnyConst sourceRecursors = false)
    (hfresh : ∀ field ∈ sourceFields,
      AvoidsTargetOnlyRecursors sourceRecursors targetRecursors field) :
    List.Forall₂
      (GuardedExprRestoration plan.Relates sourceRecursors
        targetRecursors fieldVars depth)
      sourceFields targetFields := by
  induction Haligned with
  | nil => exact .nil
  | @cons source target sources targets Hhead Htail ih =>
      apply List.Forall₂.cons
      · exact GuardedExprRestoration.ofRecursorFree Hatomic hkeys
          Hhead (hsourceFree source (by simp)) (hfresh source (by simp))
      · exact ih
          (fun field hfield => hsourceFree field (by simp [hfield]))
          (fun field hfield => hfresh field (by simp [hfield]))

end VerifyInductive
end Lean4Lean
