import Lean4Lean.Theory.VExpr.TelescopeLemmas
import Lean4Lean.Theory.VDecl

/-! Lambda-wrapped constant spines.

Syntactic facts about `wrapLams doms (mkApps (const n ls) args)`, the form of the left-hand
side of a stored computation rule: it is not a constant when it has an argument
(`VExpr.wrapLams_mkApps_snoc_ne_const`) and its head is recovered by stripping the binders
(`VExpr.stripLams_wrapLams_mkApps_head`). No typing. -/

namespace Lean4Lean

theorem VExpr.wrapLams_mkApps_snoc_ne_const {ds as : List VExpr} {f a : VExpr} :
    VExpr.wrapLams ds (VExpr.mkApps f (as ++ [a])) ≠ .const n ls := by
  cases ds with
  | cons => simp [VExpr.wrapLams]
  | nil =>
    simp only [VExpr.wrapLams, List.foldr_nil, VExpr.mkApps, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    nofun

/-- The head of a lambda-wrapped constant spine. -/
theorem VExpr.stripLams_wrapLams_mkApps_head {ds args : List VExpr} :
    (VExpr.wrapLams ds (VExpr.mkApps (.const n ls) args)).stripLams.getAppFnArgs.1 =
      .const n ls := by
  rw [VExpr.stripLams_wrapLams]
  cases args with
  | nil => rfl
  | cons a as =>
    rw [show VExpr.mkApps (.const n ls) (a :: as) = VExpr.mkApps (.app (.const n ls) a) as
      from rfl]
    have : ∀ (f : VExpr) (as : List VExpr),
        (VExpr.mkApps (.app f a) as).stripLams = VExpr.mkApps (.app f a) as := by
      intro f as
      induction as generalizing f a with
      | nil => rfl
      | cons b bs ih => exact ih _ _
    rw [this, VExpr.getAppFnArgs, VExpr.getAppFnArgs_go_mkApps]
    rfl

end Lean4Lean
