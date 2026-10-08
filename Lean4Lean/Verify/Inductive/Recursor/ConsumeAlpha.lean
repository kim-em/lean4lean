import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.TypeAnnotations

namespace Lean4Lean

open Lean hiding Environment Exception

namespace TypeChecker

/-- Closing one free variable commutes with the structural annotation
consumer. -/
theorem Expr.abstract1_consumeTypeAnnotationsVerified
    (e : Expr) (fv : FVarId) (k : Nat := 0) :
    (e.consumeTypeAnnotationsVerified annOk).abstract1 fv k =
      ((e.abstract1 fv k).consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e generalizing k
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

/-- Exact-model closing of a free-variable list commutes with the structural
annotation consumer. -/
theorem Expr.abstractN_consumeTypeAnnotationsVerified
    (e : Expr) (xs : List FVarId) (k : Nat := 0) :
    (e.consumeTypeAnnotationsVerified annOk).abstractN xs k =
      ((e.abstractN xs k).consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e generalizing k
  case case1 name levels type value h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.abstractN, h] using ih k
  case case2 name levels type value h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.abstractN, h]
  case case3 name levels type h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.abstractN, h] using ih k
  case case4 name levels type h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.abstractN, h]
  case case5 e htwo hone =>
    cases e <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstractN]
    case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
    case app fn arg =>
      cases fn <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstractN]
      case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
      case app head middle =>
        cases head <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.abstractN]
        case fvar => split <;> simp_all [Expr.consumeTypeAnnotationsVerified]

end TypeChecker

namespace VerifyInductive

end VerifyInductive
end Lean4Lean
