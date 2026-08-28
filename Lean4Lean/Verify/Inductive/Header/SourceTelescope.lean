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
    simpa [FVarNarrowSources.closeSource, VLCtx.toCtx,
      List.reverse_cons, VExpr.wrapForalls_append,
      VExpr.wrapForalls] using IH'

/-- Restrict one concrete runtime translation both to the independently
reconstructed source scope and to the normalized semantic header scope.
The two scopes select exactly the same free variables, while the semantic
scope is definitionally aligned with the canonical parameter/index
telescope.  This avoids assuming that either independently reconstructed
scope is syntactically identical to the other. -/
theorem NormalizedHeaderSourceTelescope.restrictSourceAndSemantic
    (H : NormalizedHeaderSourceTelescope env Us commonParams
      nparams nindices)
    (henv : env.WF)
    (sourceExpr : Expr)
    (htr : TrExprS env Us H.runtime sourceExpr runtimeTarget)
    (hclosed : Closed sourceExpr 0)
    (hfvars : FVarsIn (· ∈ H.sourceScope.fvars) sourceExpr) :
    (∃ sourceTarget,
      TrExprS env Us H.sourceScope sourceExpr sourceTarget) ∧
    ∃ semanticScope semanticTarget,
      H.sourceScope.fvars = semanticScope.fvars ∧
      TrExprS env Us semanticScope sourceExpr semanticTarget ∧
      VEnv.IsDefEqCtx env Us.length []
        (H.indices.reverse ++ H.ownParams.reverse) semanticScope.toCtx := by
  have Hsource := H.source.restrict henv htr hclosed hfvars
  refine ⟨Hsource, ?_⟩
  cases H.alignment with
  | full sourceFVars semanticContext =>
    exact ⟨H.runtime, runtimeTarget, sourceFVars, htr, semanticContext⟩
  | narrow semanticScope sourceFVars semantic semanticContext =>
    have hfvarsSemantic : FVarsIn (· ∈ semanticScope.fvars) sourceExpr :=
      hfvars.mono fun fv hfv => by
        rw [← sourceFVars]
        exact hfv
    rcases semantic.restrict henv htr hclosed hfvarsSemantic with
      ⟨semanticTarget, Hsemantic⟩
    have Hcontext : VEnv.IsDefEqCtx env Us.length []
        (H.indices.reverse ++ H.ownParams.reverse) semanticScope.toCtx := by
      have Hrefl := VEnv.IsDefEqCtx.refl (semantic.scopeWF henv).toCtx
      simpa [semanticContext] using Hrefl
    exact ⟨semanticScope, semanticTarget, sourceFVars, Hsemantic, Hcontext⟩

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
