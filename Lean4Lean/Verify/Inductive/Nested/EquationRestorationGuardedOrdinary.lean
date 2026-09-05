import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRecursorFree
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuarded

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Every source fragment containing no old recursor calls receives its full
structural guarded-restoration certificate automatically.  This is stronger
than target recursor-freeness: it supplies the exact component relation used
to assemble enclosing generated recursor calls. -/
theorem GuardedExprRestoration.ofRecursorFree
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (hkeys : NestedRestorationPlan.RecursorKeysCovered
      auxRec sourceRecursors)
    (Hrest : VExprRestoration plan.Relates source target)
    (hsourceFree : source.containsAnyConst sourceRecursors = false)
    (hfresh : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      source) :
    GuardedExprRestoration plan.Relates sourceRecursors targetRecursors
      fieldVars depth source target := by
  induction Hrest generalizing depth with
  | @hit source target hhit =>
      apply GuardedExprRestoration.hit hhit
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse hsourceFree
      · exact Hatomic.guardedHitTarget hkeys hhit
          (VExpr.GuardedIota.ofContainsAnyConstFalse hsourceFree)
  | leaf =>
      exact .leaf (VExpr.GuardedIota.ofContainsAnyConstFalse
        (hfresh.targetFree hsourceFree))
  | bvar => exact .bvar
  | sort => exact .sort
  | @const name levels =>
      have hsourceNot : name ∉ sourceRecursors := by
        simpa [VExpr.containsAnyConst] using hsourceFree
      have htargetNot : name ∉ targetRecursors :=
        hfresh.const_not_mem_target hsourceNot
      exact .const hsourceNot htargetNot
  | app hfn harg ihfn iharg =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .app
        (ihfn hsourceFree.1 hfresh.app_left)
        (iharg hsourceFree.2 hfresh.app_right)
  | proj hmajor ihmajor =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      unfold AvoidsTargetOnlyRecursors at hfresh
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hfresh
      exact .proj
        (ihmajor hsourceFree.2 (by
          unfold AvoidsTargetOnlyRecursors
          exact hfresh.2))
  | lam hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .lam
        (ihdomain hsourceFree.1 hfresh.lam_domain)
        (ihbody hsourceFree.2 hfresh.lam_body)
  | forallE hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .forallE
        (ihdomain hsourceFree.1 hfresh.forall_domain)
        (ihbody hsourceFree.2 hfresh.forall_body)

end VerifyInductive
end Lean4Lean
