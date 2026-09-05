import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardSeeds

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Structural restoration preserves recursor-freeness for every ordinary
equation fragment.  Atomic family/constructor hits use their independently
generated freeness proof; an atomic recursor rename is impossible because
its source key belongs to the old guarded set.  Unchanged constants use only
the exact target-only freshness seed. -/
theorem NestedRestorationPlan.AtomicProvenance.restorationRecursorFree
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (hkeys : NestedRestorationPlan.RecursorKeysCovered
      auxRec sourceRecursors)
    (Hrest : VExprRestoration plan.Relates source target)
    (hsourceFree : source.containsAnyConst sourceRecursors = false)
    (hfresh : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
      source) :
    target.SourceConstFree targetRecursors := by
  induction Hrest with
  | @hit source target hhit =>
      rcases plan.exists_node_of_restoreNode_eq_some hhit with
        ⟨node, hnode, hnodeSource, hnodeTarget⟩
      have Hbehavior := Hatomic.behaviors node hnode
      rcases Hbehavior.classification with
        ⟨oldName, newName, levels, _hrecursor, hfind,
          hsource, _htarget⟩ |
        ⟨_nonrecursor, htargetFree⟩
      · have holdMem : oldName ∈ sourceRecursors :=
          hkeys oldName newName hfind
        have hsourceEq : source = .const oldName levels :=
          hnodeSource.symm.trans hsource
        rw [hsourceEq] at hsourceFree
        simp [VExpr.containsAnyConst, holdMem] at hsourceFree
      · rwa [hnodeTarget] at htargetFree
  | leaf =>
      exact VExpr.SourceConstFree.ofContainsAnyConst
        (hfresh.targetFree hsourceFree)
  | bvar => exact .bvar _
  | sort => exact .sort _
  | @const name levels =>
      have hsourceNot : name ∉ sourceRecursors := by
        simpa [VExpr.containsAnyConst] using hsourceFree
      have htargetNot : name ∉ targetRecursors :=
        hfresh.const_not_mem_target hsourceNot
      exact .const name levels htargetNot
  | app hfn harg ihfn iharg =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .app (ihfn hsourceFree.1 hfresh.app_left)
        (iharg hsourceFree.2 hfresh.app_right)
  | @proj sourceMajor targetMajor typeName index hmajor ihmajor =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      have hmajorFresh : AvoidsTargetOnlyRecursors sourceRecursors targetRecursors
          sourceMajor := by
        unfold AvoidsTargetOnlyRecursors at hfresh ⊢
        simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hfresh
        exact hfresh.2
      exact .proj typeName index (ihmajor hsourceFree.2 hmajorFresh)
  | lam hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .lam (ihdomain hsourceFree.1 hfresh.lam_domain)
        (ihbody hsourceFree.2 hfresh.lam_body)
  | forallE hdomain hbody ihdomain ihbody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hsourceFree
      exact .forallE (ihdomain hsourceFree.1 hfresh.forall_domain)
        (ihbody hsourceFree.2 hfresh.forall_body)

end VerifyInductive
end Lean4Lean
