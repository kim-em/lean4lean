import Lean4Lean.Verify.Inductive.TypeAnnotations

/-! Exact abstract targets for executable annotation consumption. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- Follow the actual source annotation spine in an already chosen
translation. Source shape matters: metadata is erased by translation but
does not expose an annotation to the executable consumption function. -/
def consumeTranslatedTypeAnnotations : Expr → VExpr → VExpr
  | .app (.app (.const name _) first) _, target =>
    if name == ``optParam || name == ``autoParam then
      match target with
      | .app (.app (.const _ _) first') _ => consumeTranslatedTypeAnnotations first first'
      | _ => target
    else target
  | .app (.const name _) arg, target =>
    if name == ``outParam || name == ``semiOutParam then
      match target with
      | .app (.const _ _) arg' => consumeTranslatedTypeAnnotations arg arg'
      | _ => target
    else target
  | _, target => target

/-- Universe rewriting preserves the selected consumed subexpression. -/
theorem consumeTranslatedTypeAnnotations_instL (source : Expr) (target : VExpr) :
    consumeTranslatedTypeAnnotations source (target.instL levels) =
      (consumeTranslatedTypeAnnotations source target).instL levels := by
  fun_induction Expr.consumeTypeAnnotationsVerified source generalizing target
  case case1 name sourceLevels first second hannotation ih =>
    cases target <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.instL]
    case app fn arg =>
      cases fn <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.instL]
      case app head first' =>
        cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.instL, ih]
  case case3 name sourceLevels arg hannotation ih =>
    cases target <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.instL]
    case app head arg' =>
      cases head <;> simp [consumeTranslatedTypeAnnotations, hannotation, VExpr.instL, ih]
  all_goals simp [consumeTranslatedTypeAnnotations, *]

/-- Consumption reuses subtranslations of the selected source target;
it does not choose a fresh projection representation. -/
theorem TrExprS.consumeTranslatedTypeAnnotations
    (H : TrExprS env Us Δ source target) :
    TrExprS env Us Δ source.consumeTypeAnnotationsVerified
      (Lean4Lean.consumeTranslatedTypeAnnotations source target) := by
  fun_induction Expr.consumeTypeAnnotationsVerified source generalizing target
  case case1 name levels first second hannotation ih =>
    cases H with
    | app _ _ hfn _ =>
      cases hfn with
      | app _ _ hhead hfirst =>
        cases hhead
        simpa only [Lean4Lean.consumeTranslatedTypeAnnotations, hannotation, ↓reduceIte] using ih hfirst
  case case3 name levels arg hannotation ih =>
    cases H with
    | app _ _ hhead harg =>
      cases hhead
      simpa only [Lean4Lean.consumeTranslatedTypeAnnotations, hannotation, ↓reduceIte] using ih harg
  all_goals simpa [Lean4Lean.consumeTranslatedTypeAnnotations, *] using H

/-- The fixed consumed target has the same type as the original domain.
The wrapper semantics supplies equality; translation uniqueness only aligns
its proof witness with the target already fixed by the source traversal. -/
theorem consumeTranslatedTypeAnnotations_semantic_of_wrappers
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv safety env venv)
    (Hwrappers : TypeAnnotationWrappers env)
    (hΔ : Δ.WF venv Us.length)
    (htr : TrExprS venv Us Δ source target)
    (htype : venv.IsType Us.length Δ.toCtx target) :
    venv.IsType Us.length Δ.toCtx (consumeTranslatedTypeAnnotations source target) ∧
    venv.IsDefEqU Us.length Δ.toCtx target (consumeTranslatedTypeAnnotations source target) := by
  obtain ⟨consumed, hconsumed, hconsumedType, level, heq⟩ :=
    consumeTypeAnnotationsSemantic_of_wrappers Hchecking Hwrappers hΔ htr htype
  have halign := hconsumed.uniq Hchecking.wf
    (.refl Hchecking.wf hΔ) htr.consumeTranslatedTypeAnnotations
  exact ⟨hconsumedType.defeqU_l Hchecking.wf hΔ.toCtx halign,
    (show venv.IsDefEqU Us.length Δ.toCtx target consumed from ⟨.sort level, heq⟩).trans
      Hchecking.wf hΔ.toCtx halign⟩


theorem consumeTranslatedTypeAnnotations_semantic
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hΔ : Δ.WF venv Us.length)
    (htr : TrExprS venv Us Δ source target)
    (htype : venv.IsType Us.length Δ.toCtx target) :
    venv.IsType Us.length Δ.toCtx (consumeTranslatedTypeAnnotations source target) ∧
    venv.IsDefEqU Us.length Δ.toCtx target (consumeTranslatedTypeAnnotations source target) :=
  consumeTranslatedTypeAnnotations_semantic_of_wrappers Hchecking.tr Hchecking.typeAnnotationWrappers hΔ htr htype

end Lean4Lean
