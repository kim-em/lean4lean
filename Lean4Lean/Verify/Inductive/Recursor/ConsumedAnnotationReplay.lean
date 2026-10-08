import Lean4Lean.Verify.Inductive.ConsumedTranslation
namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem consumeTranslatedTypeAnnotations_liftN (source : Expr) (target : VExpr) :
    consumeTranslatedTypeAnnotations annOk source (target.liftN n k) =
      (consumeTranslatedTypeAnnotations annOk source target).liftN n k := by
  fun_induction Expr.consumeTypeAnnotationsVerified annOk source generalizing target
  case case1 name sourceLevels first second hannotation ih =>
    cases target <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.liftN]
    case app fn arg =>
      cases fn <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.liftN]
      case app head first' =>
        cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.liftN, ih]
  case case3 name sourceLevels arg hannotation ih =>
    cases target <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.liftN]
    case app head arg' =>
      cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.liftN, ih]
  all_goals simp [consumeTranslatedTypeAnnotations, *]

theorem consumeTranslatedTypeAnnotations_abstract1 (source : Expr) (target : VExpr) :
    consumeTranslatedTypeAnnotations annOk (source.abstract1 fv depth) target =
      consumeTranslatedTypeAnnotations annOk source target := by
  fun_induction Expr.consumeTypeAnnotationsVerified annOk source generalizing target depth
  case case1 name sourceLevels first second hannotation ih =>
    cases target <;> simp [Expr.abstract1, consumeTranslatedTypeAnnotations, hannotation]
    case app fn arg =>
      cases fn <;> try simp [consumeTranslatedTypeAnnotations, hannotation]
      case app head first' =>
        cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, ih]
  case case3 name sourceLevels arg hannotation ih =>
    cases target <;> simp [Expr.abstract1, consumeTranslatedTypeAnnotations, hannotation]
    case app head arg' =>
      cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, ih]
  case case5 source hbinary hunary =>
    cases source <;> simp_all [Expr.abstract1, consumeTranslatedTypeAnnotations]
    case fvar name =>
      split <;> simp [consumeTranslatedTypeAnnotations]
    case app fn arg =>
      cases fn <;> simp_all [Expr.abstract1, consumeTranslatedTypeAnnotations]
      case fvar name => split <;> simp [consumeTranslatedTypeAnnotations]
      case app head first =>
        cases head <;> simp_all [Expr.abstract1, consumeTranslatedTypeAnnotations]
        case fvar name => split <;> simp [consumeTranslatedTypeAnnotations]
  all_goals simp [Expr.abstract1, consumeTranslatedTypeAnnotations, *]

end Lean4Lean
