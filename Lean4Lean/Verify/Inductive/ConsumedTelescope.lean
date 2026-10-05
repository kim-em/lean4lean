import Lean4Lean.Verify.Inductive.ConsumedTranslation

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- Consume the domains of a displayed source telescope. This is the closed
syntax produced by reopening its binders with consumed local declaration types. -/
def Expr.consumeForallTypes : Expr → Expr
  | .forallE name domain body bi =>
    .forallE name domain.consumeTypeAnnotationsVerified (Expr.consumeForallTypes body) bi
  | source => source

/-- Replay domain consumption in the original checking environment. Changes
to an earlier binder transport later strict translations by context equality;
the resulting telescope does not require any subsequently installed constant. -/
theorem TrExprS.consumeForallTypes_of_wrappers
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv safety env venv)
    (Hwrappers : TypeAnnotationWrappers env)
    (hΔ : Δ.WF venv Us.length)
    (H : TrExprS venv Us Δ source target)
    (Htype : venv.IsType Us.length Δ.toCtx target) :
    ∃ consumed,
      TrExprS venv Us Δ (Expr.consumeForallTypes source) consumed ∧
      venv.IsType Us.length Δ.toCtx consumed ∧
      venv.IsDefEqU Us.length Δ.toCtx target consumed := by
  induction source generalizing Δ target with
  | forallE name domain body bi _ ih =>
    cases H with
    | @forallE domainTarget bodyTarget _ _ _ _ _ HdomType HbodyType Hdom Hbody =>
      let consumedDomain := Lean4Lean.consumeTranslatedTypeAnnotations domain domainTarget
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


theorem TrExprS.consumeForallTypes
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Δ : VLCtx}
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hΔ : Δ.WF venv Us.length)
    (H : TrExprS venv Us Δ source target)
    (Htype : venv.IsType Us.length Δ.toCtx target) :
    ∃ consumed,
      TrExprS venv Us Δ (Expr.consumeForallTypes source) consumed ∧
      venv.IsType Us.length Δ.toCtx consumed ∧
      venv.IsDefEqU Us.length Δ.toCtx target consumed :=
  H.consumeForallTypes_of_wrappers Hchecking.tr Hchecking.typeAnnotationWrappers hΔ Htype

end Lean4Lean
