import Lean4Lean.Verify.Inductive.ConsumedTelescope
import Lean4Lean.Verify.Inductive.Recursor.ConsumeAlpha

namespace Lean4Lean
open Lean hiding Environment Exception

theorem Expr.abstract1_consumeForallTypes (source : Expr) (fv : FVarId) (k : Nat := 0) :
    (Expr.consumeForallTypes annOk source).abstract1 fv k =
      Expr.consumeForallTypes annOk (source.abstract1 fv k) := by
  induction source generalizing k <;>
    simp [Expr.consumeForallTypes, Expr.abstract1,
      TypeChecker.Expr.abstract1_consumeTypeAnnotationsVerified, *]
  split <;> rfl

theorem Expr.abstractN_consumeForallTypes (source : Expr) (xs : List FVarId) (k : Nat := 0) :
    (Expr.consumeForallTypes annOk source).abstractN xs k =
      Expr.consumeForallTypes annOk (source.abstractN xs k) := by
  induction source generalizing k <;>
    simp [Expr.consumeForallTypes, Expr.abstractN,
      TypeChecker.Expr.abstractN_consumeTypeAnnotationsVerified, *]
  split <;> rfl

theorem Expr.abstractList_consumeForallTypes (source : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (Expr.consumeForallTypes annOk source).abstractList fvars k =
      Expr.consumeForallTypes annOk (source.abstractList fvars k) := by
  induction fvars generalizing source with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList, Expr.abstract1_consumeForallTypes, ih]

end Lean4Lean
