import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFieldApps

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Structural restoration of a bound-variable-headed application exposes
an exact ordered pointwise restoration of its argument spine.  Finite hit
provenance rules out stopping at any prefix of the spine. -/
theorem NestedRestorationPlan.AtomicProvenance.bvarSpineAlignment
    (Hatomic : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates source target)
    (hspine : source.getAppFnArgs = (.bvar index, sourceArgs)) :
    ∃ targetArgs,
      target.getAppFnArgs = (.bvar index, targetArgs) ∧
      List.Forall₂ (VExprRestoration plan.Relates)
        sourceArgs targetArgs := by
  induction Hrest generalizing index sourceArgs with
  | @hit source target hhit =>
      have hhead : source.bvarHead? = some index := by
        unfold VExpr.bvarHead?
        rw [hspine]
      exact False.elim (Hatomic.not_relates_of_bvarHead hhead hhit)
  | leaf =>
      exact ⟨sourceArgs, hspine, VExprRestorationList.leaf sourceArgs⟩
  | @bvar i =>
      simp [VExpr.getAppFnArgs] at hspine
      rcases hspine with ⟨rfl, rfl⟩
      exact ⟨[], rfl, .nil⟩
  | @sort level =>
      change (VExpr.sort level, []) = (.bvar index, sourceArgs) at hspine
      cases hspine
  | @const name levels =>
      change (VExpr.const name levels, []) =
        (.bvar index, sourceArgs) at hspine
      cases hspine
  | @app sourceFn sourceArg targetFn targetArg hfn harg ihfn iharg =>
      cases hsourceFn : sourceFn.getAppFnArgs with
      | mk sourceHead priorSourceArgs =>
        simp only [VExpr.getAppFnArgs_app, hsourceFn] at hspine
        have hhead := congrArg Prod.fst hspine
        have hargs := congrArg Prod.snd hspine
        simp only [Prod.fst] at hhead
        simp only [Prod.snd] at hargs
        subst sourceHead
        rcases ihfn (index := index) (sourceArgs := priorSourceArgs)
            hsourceFn with ⟨priorTargetArgs, htargetFn, Haligned⟩
        refine ⟨priorTargetArgs ++ [targetArg], ?_, ?_⟩
        · simp only [VExpr.getAppFnArgs_app, htargetFn]
        · rw [← hargs]
          exact Lean4Lean.VerifyInductive.List.Forall₂.append' Haligned
            (.cons harg .nil)
  | @proj sourceMajor targetMajor typeName fieldIndex hmajor ihmajor =>
      change (VExpr.proj typeName fieldIndex sourceMajor, []) =
        (.bvar index, sourceArgs) at hspine
      cases hspine
  | @lam sourceDomain targetDomain sourceBody targetBody hdomain hbody
      ihdomain ihbody =>
      change (VExpr.lam sourceDomain sourceBody, []) =
        (.bvar index, sourceArgs) at hspine
      cases hspine
  | @forallE sourceDomain targetDomain sourceBody targetBody hdomain hbody
      ihdomain ihbody =>
      change (VExpr.forallE sourceDomain sourceBody, []) =
        (.bvar index, sourceArgs) at hspine
      cases hspine

/-- `mkApps` specialization used by generated minor applications. -/
theorem NestedRestorationPlan.AtomicProvenance.bvarMkAppsAlignment
    (Hatomic : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates
      (VExpr.mkApps (.bvar index) sourceArgs) target) :
    ∃ targetArgs,
      target = VExpr.mkApps (.bvar index) targetArgs ∧
      List.Forall₂ (VExprRestoration plan.Relates)
        sourceArgs targetArgs := by
  rcases Hatomic.bvarSpineAlignment Hrest
      (VExpr.getAppFnArgs_mkApps_bvar index sourceArgs) with
    ⟨targetArgs, htargetSpine, Haligned⟩
  have hrebuild := VExpr.mkApps_getAppFnArgs target
  rw [htargetSpine] at hrebuild
  exact ⟨targetArgs, hrebuild.symm, Haligned⟩

end VerifyInductive
end Lean4Lean
