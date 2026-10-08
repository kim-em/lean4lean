import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.TypeAnnotations

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- Consume the domains of a displayed source telescope. This is the closed
syntax produced by reopening its binders with consumed local declaration types. -/
def Expr.consumeForallTypes (ok : Name → Bool) : Expr → Expr
  | .forallE name domain body bi =>
    .forallE name (domain.consumeTypeAnnotationsVerified ok) (Expr.consumeForallTypes ok body) bi
  | source => source

/-- Replay domain consumption in the original checking environment. Changes
to an earlier binder transport later strict translations by context equality;
the resulting telescope does not require any subsequently installed constant. -/
theorem TrExprS.consumeForallTypes_of_wrappers
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv safety env venv)
    (Hwrappers : TypeAnnotationWrappers env annOk)
    (hΔ : Δ.WF venv Us.length)
    (H : TrExprS venv Us Δ source target)
    (Htype : venv.IsType Us.length Δ.toCtx target) :
    ∃ consumed,
      TrExprS venv Us Δ (Expr.consumeForallTypes annOk source) consumed ∧
      venv.IsType Us.length Δ.toCtx consumed ∧
      venv.IsDefEqU Us.length Δ.toCtx target consumed := by
  induction source generalizing Δ target with
  | forallE name domain body bi _ ih =>
    cases H with
    | @forallE domainTarget bodyTarget _ _ _ _ _ HdomType HbodyType Hdom Hbody =>
      let consumedDomain := Lean4Lean.consumeTranslatedTypeAnnotations annOk domain domainTarget
      obtain ⟨HconsumedType, HdomEq⟩ :=
        consumeTranslatedTypeAnnotations_semantic_of_wrappers Hchecking Hwrappers hΔ Hdom HdomType
      have HdomEqTyped := HdomEq.of_l Hchecking.wf hΔ.toCtx HdomType.choose_spec
      have Hctx : VLCtx.IsDefEq venv Us.length
          ((none, .vlam domainTarget) :: Δ) ((none, .vlam consumedDomain) :: Δ) :=
        .cons (.refl Hchecking.wf hΔ) nofun (.vlam HdomEqTyped)
      obtain ⟨bodyConverted, HbodyConverted⟩ := Hbody.defeqDFC Hchecking.wf Hctx
      have HbodyEq := Hbody.uniq Hchecking.wf Hctx HbodyConverted
      have HbodyConvertedType := (HbodyType.defeqU_l Hchecking.wf
        Hctx.wf.toCtx HbodyEq).defeqDFC Hchecking.wf.ordered Hctx.defeqCtx
      obtain ⟨bodyConsumed, HbodyConsumed, HbodyConsumedType, HbodyConsumedEq⟩ :=
        ih (Hctx.symm Hchecking.wf.ordered).wf HbodyConverted HbodyConvertedType
      have HbodyFinalEq := HbodyEq.trans Hchecking.wf Hctx.wf.toCtx
        (HbodyConsumedEq.defeqDFC Hchecking.wf.ordered
          (Hctx.defeqCtx.symm Hchecking.wf.ordered))
      exact ⟨.forallE consumedDomain bodyConsumed,
        .forallE HconsumedType HbodyConsumedType Hdom.consumeTranslatedTypeAnnotations HbodyConsumed,
        .forallE HconsumedType HbodyConsumedType,
        _, .forallEDF HdomEqTyped
          (HbodyFinalEq.of_l Hchecking.wf Hctx.wf.toCtx HbodyType.choose_spec)⟩
  | _ => exact ⟨target, H, Htype, _, Htype.choose_spec⟩

end Lean4Lean

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
