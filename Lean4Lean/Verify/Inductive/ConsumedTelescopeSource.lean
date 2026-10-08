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

theorem Expr.consumeForallTypes_fvarsIn {source : Expr} (H : source.FVarsIn P) :
    (Expr.consumeForallTypes annOk source).FVarsIn P := by
  induction source with
  | forallE _ _ _ _ _ ih =>
    exact ⟨VerifyInductive.Expr.consumeTypeAnnotationsVerified_fvarsIn H.1, ih H.2⟩
  | _ => exact H

theorem Expr.instantiate1'_fvar_consumeTypeAnnotationsVerified
    (source : Expr) (fv : FVarId) (k : Nat := 0) :
    (source.consumeTypeAnnotationsVerified annOk).instantiate1' (.fvar fv) k =
      ((source.instantiate1' (.fvar fv) k).consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ source generalizing k
  case case1 name levels type value h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1', h] using ih k
  case case2 name levels type value h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1', h]
  case case3 name levels type h ih =>
    simpa [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1', h] using ih k
  case case4 name levels type h =>
    simp [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1', h]
  case case5 source htwo hone =>
    cases source <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1']
    case bvar =>
      split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
      split <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.liftLooseBVars']
    case app fn arg =>
      cases fn <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1']
      case bvar =>
        split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
        split <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.liftLooseBVars']
      case app head middle =>
        cases head <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.instantiate1']
        case bvar =>
          split <;> simp_all [Expr.consumeTypeAnnotationsVerified]
          split <;> simp_all [Expr.consumeTypeAnnotationsVerified, Expr.liftLooseBVars']

theorem Expr.instantiate1'_fvar_consumeForallTypes (source : Expr) (fv : FVarId) (k : Nat := 0) :
    (Expr.consumeForallTypes annOk source).instantiate1' (.fvar fv) k =
      Expr.consumeForallTypes annOk (source.instantiate1' (.fvar fv) k) := by
  induction source generalizing k <;>
    simp [Expr.consumeForallTypes, Expr.instantiate1', Expr.instantiate1'_fvar_consumeTypeAnnotationsVerified, *]
  split <;> try simp [Expr.consumeForallTypes]
  split <;> simp [Expr.consumeForallTypes, Expr.liftLooseBVars']

theorem Expr.instantiate1_fvar_consumeForallTypes (source : Expr) (fv : FVarId) :
    (Expr.consumeForallTypes annOk source).instantiate1 (.fvar fv) =
      Expr.consumeForallTypes annOk (source.instantiate1 (.fvar fv)) := by
  simp only [Expr.instantiate1_eq, Expr.instantiate1'_fvar_consumeForallTypes]

end Lean4Lean
