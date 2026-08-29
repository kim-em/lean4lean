import Lean4Lean.Verify.Inductive.Nested.Mapping

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Interpret a stateful production expression mapping as the independent
structural abstract expansion relation. Successful replacements are the only
non-structural cases supplied by callers. Projection support is recovered
from the two environment-indexed certified translations themselves. -/
theorem NestedExprMapping.abstractExpansion
    (H : NestedExprMapping prodEnv lctx params As result input state out)
    (Hctx : TrExprS.IsUniqueCtx sourceCtx targetCtx)
    (Hhit : ∀ {input state output nextState finalState depth
        sourceTarget targetTarget sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      TrExprS.IsUniqueCtx sourceCtx targetCtx →
      TrExprS venv lparams sourceCtx input sourceTarget →
      TrExprS venv lparams targetCtx output targetTarget →
      leaf depth sourceTarget targetTarget)
    (Hlet : ∀ {name type value body nondep state type' typeState value'
        valueState body' outState depth sourceTarget targetTarget}
        {sourceCtx targetCtx : VLCtx},
      NestedReplacement prodEnv lctx params As
        (.letE name type value body nondep) state (none, state) →
      NestedExprMapping prodEnv lctx params As result type state
        (type', typeState) →
      NestedExprMapping prodEnv lctx params As result value typeState
        (value', valueState) →
      NestedExprMapping prodEnv lctx params As result body valueState
        (body', outState) →
      TrExprS.IsUniqueCtx sourceCtx targetCtx →
      TrExprS venv lparams sourceCtx (.letE name type value body nondep)
        sourceTarget →
      TrExprS venv lparams targetCtx
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep) targetTarget →
      VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget)
    (Hsource : TrExprS venv lparams sourceCtx input sourceTarget)
    (Htarget : TrExprS venv lparams targetCtx out.1 targetTarget) :
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget := by
  induction H generalizing sourceCtx targetCtx sourceTarget targetTarget depth with
  | hit Hnode =>
    exact .hit (Hhit Hnode Hctx Hsource Htarget)
  | bvar | fvar | mvar | sort | const | lit =>
    have heq : sourceTarget = targetTarget :=
      Hsource.unique' Hctx (by trivial) Htarget
    subst targetTarget
    exact VExpr.NestedExprExpansion.refl leaf depth sourceTarget
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have Htarget' : TrExprS venv lparams targetCtx (.app fn' arg')
        targetTarget := by
      simpa [Expr.updateApp!] using Htarget
    cases Hsource with
    | app _ _ HsourceFn HsourceArg =>
      cases Htarget' with
      | app _ _ HtargetFn HtargetArg =>
        exact .app (ihFn Hctx HsourceFn HtargetFn)
          (ihArg Hctx HsourceArg HtargetArg)
  | @lam name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS venv lparams targetCtx
        (.lam name dom' body' bi) targetTarget := by
      simpa [Expr.updateLambdaE!] using Htarget
    cases Hsource with
    | lam _ HsourceDom HsourceBody =>
      cases Htarget' with
      | lam _ HtargetDom HtargetBody =>
        exact .lam (ihDom Hctx HsourceDom HtargetDom)
          (ihBody (Hctx.cons .vlam) HsourceBody HtargetBody)
  | @forallE name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS venv lparams targetCtx
        (.forallE name dom' body' bi) targetTarget := by
      simpa [Expr.updateForallE!] using Htarget
    cases Hsource with
    | forallE _ _ HsourceDom HsourceBody =>
      cases Htarget' with
      | forallE _ _ HtargetDom HtargetBody =>
        exact .forallE (ihDom Hctx HsourceDom HtargetDom)
          (ihBody (Hctx.cons .vlam) HsourceBody HtargetBody)
  | @letE name type value body nondep state type' typeState value' valueState
      body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have Htarget' : TrExprS venv lparams targetCtx
        (.letE name type' value' body' nondep) targetTarget := by
      simpa [Expr.updateLet!] using Htarget
    exact Hlet Hnode Htype Hvalue Hbody Hctx Hsource Htarget'
  | @mdata data body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS venv lparams targetCtx (.mdata data body')
        targetTarget := by
      simpa [Expr.updateMData!] using Htarget
    cases Hsource with
    | mdata HsourceBody =>
      cases Htarget' with
      | mdata HtargetBody => exact ihBody Hctx HsourceBody HtargetBody
  | @proj structName index body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS venv lparams targetCtx
        (.proj structName index body') targetTarget := by
      simpa [Expr.updateProj!] using Htarget
    cases Hsource with
    | proj HsourceBody HsourceProj =>
      cases Htarget' with
      | proj HtargetBody HtargetProj =>
        exact .projection HsourceProj.supportExpansion
          HtargetProj.supportExpansion
          (ihBody Hctx HsourceBody HtargetBody)

end VerifyInductive
end Lean4Lean
