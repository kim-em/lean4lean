import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner

open Lean hiding Environment Exception
open Kernel

/-- The graph of the executable projection-result computation at one exact
checker context and state.  This is proof data obtained from evaluation, not a
caller-supplied projection resolver. -/
structure ProjectionResultTrace
    (methods : Methods) (c : VContext) (s : VState)
    (typeName : Name) (index : Nat) (struct structType : Expr)
    (result : ProjectionResult) where
  finalState : State
  run : inferProjResult typeName index struct structType
      methods c.toContext s.toState = .ok (result, finalState)

namespace ProjectionResultTrace

theorem family_single
    (H : ProjectionResultTrace methods c s typeName index struct structType result) :
    result.expansion.familyInfo.ctors =
      [result.expansion.constructorName] :=
  result.expansion.familySingle

/-- One executable projection-result run has only one result.  In particular,
the inferred type and every retained expansion component are literally equal;
no type-theoretic injectivity or projection compatibility hypothesis is used. -/
theorem result_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult = rightResult := by
  cases left with
  | mk leftState leftRun =>
    cases right with
    | mk rightState rightRun =>
      rw [leftRun] at rightRun
      cases rightRun
      rfl

theorem type_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult.type = rightResult.type :=
  congrArg ProjectionResult.type (left.result_eq right)

theorem expansion_eq
    (left : ProjectionResultTrace methods c s typeName index struct structType leftResult)
    (right : ProjectionResultTrace methods c s typeName index struct structType rightResult) :
    leftResult.expansion = rightResult.expansion :=
  congrArg ProjectionResult.expansion (left.result_eq right)

end ProjectionResultTrace

end Lean4Lean.TypeChecker.Inner
