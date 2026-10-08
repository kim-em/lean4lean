import Lean4Lean.Verify.Inductive.CompletedEquationLhs

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Applying a complete telescope to as many arguments as it has domains
undoes a weakening of the residual by those binders.  The domain values may
be dependent; they disappear from the conclusion because the weakened
residual does not depend on any of the newly inserted variables. -/
theorem VExpr.applyForallType_wrapForalls_liftN
    (domains args : List VExpr) (result : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains (result.liftN domains.length 0)) args =
      result := by
  induction args generalizing domains result with
  | nil =>
      have hdomains : domains = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst domains
      simp [VExpr.applyForallType, VExpr.wrapForalls]
  | cons arg args ih =>
      cases domains with
      | nil => simp at hlength
      | cons domain domains =>
          have htail : args.length = domains.length := by
            simpa using Nat.succ.inj hlength
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (result.liftN (domains.length + 1) 0)).inst arg) args = result
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [VExpr.inst_liftN_lo]
          simpa only [VExpr.instForallDomains_length] using
            ih (VExpr.instForallDomains domains arg 0) result (by
              simpa using htail)

end VerifyInductive
end Lean4Lean
