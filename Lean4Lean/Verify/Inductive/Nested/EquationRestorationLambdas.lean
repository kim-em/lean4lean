import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFieldApps
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedOrdinary

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A finite production plan cannot stop at an expression whose application
head is not a constant. -/
theorem NestedRestorationPlan.AtomicProvenance.not_relates_of_not_const
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (hhead : ∀ name levels,
      source.getAppFnArgs.1 ≠ .const name levels) :
    ¬ plan.Relates source target := by
  rintro ⟨node, hnode, hsource, _htarget⟩
  rcases H.nodeSourceConstHead node hnode with
    ⟨name, levels, hconst⟩
  apply hhead name levels
  rwa [← hsource]

/-- Exact structural extraction of an independently generated lambda prefix.
The target has the same number and order of lambda domains, each related by
the finite restoration plan, followed by the exact restored body. -/
theorem NestedRestorationPlan.AtomicProvenance.wrapLamsAlignment
    (Hatomic : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates
      (VExpr.wrapLams sourceDomains sourceBody) target) :
    ∃ targetDomains targetBody,
      target = VExpr.wrapLams targetDomains targetBody ∧
      List.Forall₂ (VExprRestoration plan.Relates)
        sourceDomains targetDomains ∧
      VExprRestoration plan.Relates sourceBody targetBody := by
  induction sourceDomains generalizing target with
  | nil =>
      exact ⟨[], target, rfl, .nil, Hrest⟩
  | cons sourceDomain sourceDomains ih =>
      change VExprRestoration plan.Relates
        (.lam sourceDomain (VExpr.wrapLams sourceDomains sourceBody))
        target at Hrest
      cases Hrest with
      | hit hhit =>
          exact False.elim (Hatomic.not_relates_of_not_const (by
            intro name levels
            simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go]) hhit)
      | leaf =>
          exact ⟨sourceDomain :: sourceDomains, sourceBody, rfl,
            .cons .leaf (VExprRestorationList.leaf sourceDomains), .leaf⟩
      | lam hdomain hbody =>
          rcases ih hbody with
            ⟨targetDomains, targetBody, htarget, Hdomains, Hbody⟩
          subst htarget
          exact ⟨_ :: targetDomains, targetBody, rfl,
            .cons hdomain Hdomains, Hbody⟩
      | projection sourceExpansion => cases sourceExpansion

/-- Componentwise restoration of a generated lambda telescope assembles a
guarded restoration of the whole telescope.  The independently generated
domains contain no source recursors; target-only freshness and finite atomic
provenance therefore discharge every domain structurally. -/
theorem GuardedExprRestoration.wrapLamsOfComponents
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (hkeys : NestedRestorationPlan.RecursorKeysCovered
      auxRec sourceRecursors)
    (Hdomains : List.Forall₂ (VExprRestoration plan.Relates)
      sourceDomains targetDomains)
    (hsourceFree : ∀ domain ∈ sourceDomains,
      domain.containsAnyConst sourceRecursors = false)
    (hfresh : ∀ domain ∈ sourceDomains,
      AvoidsTargetOnlyRecursors sourceRecursors targetRecursors domain)
    (Hbody : GuardedExprRestoration plan.Relates sourceRecursors
      targetRecursors fieldVars (depth + sourceDomains.length)
      sourceBody targetBody) :
    GuardedExprRestoration plan.Relates sourceRecursors targetRecursors
      fieldVars depth (VExpr.wrapLams sourceDomains sourceBody)
        (VExpr.wrapLams targetDomains targetBody) := by
  induction Hdomains generalizing depth with
  | nil => simpa [VExpr.wrapLams] using Hbody
  | @cons sourceDomain targetDomain sourceDomains targetDomains
      Hdomain Hdomains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons]
      apply GuardedExprRestoration.lam
      · exact GuardedExprRestoration.ofRecursorFree Hatomic hkeys
          Hdomain (hsourceFree sourceDomain (by simp))
            (hfresh sourceDomain (by simp))
      · apply ih
        · intro domain hdomain
          exact hsourceFree domain (by simp [hdomain])
        · intro domain hdomain
          exact hfresh domain (by simp [hdomain])
        · simpa [Nat.add_assoc, Nat.add_comm 1 sourceDomains.length]
            using Hbody

end VerifyInductive
end Lean4Lean
