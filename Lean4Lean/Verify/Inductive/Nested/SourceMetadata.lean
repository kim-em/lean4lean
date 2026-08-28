import Lean4Lean.Verify.Inductive.Nested.Opening

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Universe instantiation preserves an identical concrete forall-domain
prefix. -/
theorem _root_.Lean.Expr.SameForallDomains.instantiateLevelParams
    (H : Expr.SameForallDomains n left right)
    (params : List Name) (levels : List Level) :
    Expr.SameForallDomains n
      (left.instantiateLevelParams params levels)
      (right.instantiateLevelParams params levels) := by
  induction H with
  | nil => exact .nil
  | cons H ih =>
    simpa [Expr.instantiateLevelParams_eq,
      Expr.instantiateLevelParamsCore'] using Expr.SameForallDomains.cons ih

/-- Translating two concrete telescopes with the same forall domains (but
possibly different binder annotations) produces definitionally equal
abstract binder contexts. -/
theorem _root_.Lean.Expr.SameForallDomains.translatedContexts
    (H : Expr.SameForallDomains n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left leftTarget)
    (Hright : TrExprS env Us rightCtx right rightTarget) :
    ∃ leftDomains leftResidual rightDomains rightResidual,
      leftDomains.length = n ∧
      rightDomains.length = n ∧
      leftTarget = VExpr.wrapForalls leftDomains leftResidual ∧
      rightTarget = VExpr.wrapForalls rightDomains rightResidual ∧
      VEnv.IsDefEqCtx env Us.length []
        (leftDomains.reverse ++ leftCtx.toCtx)
        (rightDomains.reverse ++ rightCtx.toCtx) := by
  induction H generalizing leftCtx rightCtx leftTarget rightTarget with
  | nil =>
    exact ⟨[], leftTarget, [], rightTarget, rfl, rfl, rfl, rfl, by
      simpa using hctx.defeqCtx⟩
  | @cons n left right name dom leftBi rightBi H ih =>
    cases Hleft with
    | @forallE leftDom leftBody _ _ _ _ _ HleftDomType HleftBodyType
        HleftDom HleftBody =>
      cases Hright with
      | @forallE rightDom rightBody _ _ _ _ _ HrightDomType
          HrightBodyType HrightDom HrightBody =>
        have hdomU := HleftDom.uniq henv hctx HrightDom
        rcases HleftDomType with ⟨_leftLevel, HleftDomType⟩
        have hdom := hdomU.of_l henv hctx.wf.toCtx HleftDomType
        have hctx' : VLCtx.IsDefEq env Us.length
            ((none, .vlam leftDom) :: leftCtx)
            ((none, .vlam rightDom) :: rightCtx) :=
          .cons hctx nofun (.vlam hdom)
        rcases ih hctx' HleftBody HrightBody with
          ⟨leftTail, leftResidual, rightTail, rightResidual,
            hleftLength, hrightLength, hleftTarget, hrightTarget,
            hcontexts⟩
        refine ⟨leftDom :: leftTail, leftResidual,
          rightDom :: rightTail, rightResidual, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hleftLength]
        · simp [hrightLength]
        · simp [VExpr.wrapForalls, hleftTarget]
        · simp [VExpr.wrapForalls, hrightTarget]
        · simpa [List.reverse_cons, List.append_assoc,
            VLCtx.toCtx] using hcontexts

/-- Exact-domain form of `SameForallDomains.translatedContexts`. -/
theorem _root_.Lean.Expr.SameForallDomains.translatedContextsExact
    (H : Expr.SameForallDomains n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left
      (VExpr.wrapForalls leftDomains leftResidual))
    (Hright : TrExprS env Us rightCtx right
      (VExpr.wrapForalls rightDomains rightResidual))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n) :
    VEnv.IsDefEqCtx env Us.length []
      (leftDomains.reverse ++ leftCtx.toCtx)
      (rightDomains.reverse ++ rightCtx.toCtx) := by
  rcases H.translatedContexts henv hctx Hleft Hright with
    ⟨actualLeftDomains, actualLeftResidual,
      actualRightDomains, actualRightResidual,
      hactualLeftLength, hactualRightLength,
      hleftTarget, hrightTarget, Hcontexts⟩
  have hleftDomains : leftDomains = actualLeftDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hleftLength hactualLeftLength (by simpa using hleftTarget)
  have hrightDomains : rightDomains = actualRightDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hrightLength hactualRightLength (by simpa using hrightTarget)
  subst actualLeftDomains
  subst actualRightDomains
  exact Hcontexts

end VerifyInductive
end Lean4Lean
