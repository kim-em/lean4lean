import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.TypeAnnotations

namespace Lean4Lean

open Lean hiding Environment Exception

namespace TypeChecker

/-- Closing one free variable commutes with the structural annotation
consumer. -/
theorem Expr.abstract1_consumeTypeAnnotationsVerified
    (e : Expr) (fv : FVarId) (k : Nat := 0) :
    e.consumeTypeAnnotationsVerified.abstract1 fv k =
      (e.abstract1 fv k).consumeTypeAnnotationsVerified := by
  fun_induction Expr.consumeTypeAnnotationsVerified e generalizing k
  case case1 name levels type value h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.abstract1, h] using ih k
  case case2 name levels type value h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.abstract1, h]
  case case3 name levels type h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.abstract1, h] using ih k
  case case4 name levels type h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.abstract1, h]
  case case5 e htwo hone =>
    cases e <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstract1]
    case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
    case app fn arg =>
      cases fn <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstract1]
      case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
      case app head middle =>
        cases head <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstract1]
        case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]

/-- Closing a free-variable spine commutes with removal of the outer type
annotations recognized by the executable checker. -/
theorem Expr.abstractList_consumeTypeAnnotations
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    e.consumeTypeAnnotationsVerified.abstractList fvars k =
      (e.abstractList fvars k).consumeTypeAnnotationsVerified := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Expr.abstractList,
        Expr.abstract1_consumeTypeAnnotationsVerified]
      exact ih (e.abstract1 fv k)

end TypeChecker

namespace VerifyInductive

/-- The annotation-consumer alpha contract follows from its existing
executable equation; it is not an additional checker assumption. -/
theorem consumeTypeAnnotationsAlphaCompat :
    ConsumeTypeAnnotationsAlphaCompat := by
  intro leftBinders rightBinders leftDomain rightDomain Halpha
  unfold TypeChecker.ExprAlphaUnder at Halpha ⊢
  rw [TypeChecker.Expr.abstractList_consumeTypeAnnotations,
    TypeChecker.Expr.abstractList_consumeTypeAnnotations, Halpha]

end VerifyInductive
end Lean4Lean
