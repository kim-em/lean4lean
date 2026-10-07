import Lean4Lean.Verify.Inductive.Header.LoopType

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopType

/-- Closing a dependency-selected source context reconstructs a literal
source forall telescope and its abstract target simultaneously.  Each
retained free variable is abstracted at the point where its original source
domain is reintroduced; the semantic target is therefore the context's
oldest-to-newest domain list wrapped around the translated residual. -/
theorem FVarNarrowSources.closeSourceTranslation
    (H : FVarNarrowSources env Us scope)
    (hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body bodyTarget)
    (HbodyType : env.IsType Us.length scope.toCtx bodyTarget) :
    TrExprS env Us [] (H.closeSource body)
        (VExpr.wrapForalls scope.toCtx.reverse bodyTarget) ∧
      env.IsType Us.length []
        (VExpr.wrapForalls scope.toCtx.reverse bodyTarget) := by
  induction H generalizing body bodyTarget with
  | nil =>
    change TrExprS env Us [] body bodyTarget ∧
      env.IsType Us.length [] bodyTarget
    exact ⟨Hbody, HbodyType⟩
  | @cons scope target fv deps tail name binderInfo domain Hdomain IH =>
    have htail : scope.WF env Us.length := hscope.1
    have HtargetType : env.IsType Us.length scope.toCtx target := hscope.2.2
    let W : VLCtx.Abstract scope fv (.vlam target) 0 0
        ((some (fv, deps), .vlam target) :: scope)
        ((none, .vlam target) :: scope) := .zero
    have HbodyAbstract : TrExprS env Us
        ((none, .vlam target) :: scope) (body.abstract1 fv) bodyTarget :=
      Hbody.abstract W
    have Hforall : TrExprS env Us scope
        (.forallE name domain (body.abstract1 fv) binderInfo)
        (.forallE target bodyTarget) :=
      .forallE HtargetType HbodyType Hdomain HbodyAbstract
    have HforallType : env.IsType Us.length scope.toCtx
        (.forallE target bodyTarget) :=
      .forallE HtargetType HbodyType
    have IH' := IH htail Hforall HforallType
    have hbodyClosed : Closed body := by
      have h := Hbody.closed
      simpa [VLCtx.bvars, tail.noBV] using h
    have h1 : body.abstractN [fv] = body.abstract1 fv :=
      Expr.abstractN_singleton hbodyClosed.looseBVarRange_le
    simpa [h1, FVarNarrowSources.closeSource, VLCtx.toCtx,
      List.reverse_cons, VExpr.wrapForalls_append,
      VExpr.wrapForalls] using IH'

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
