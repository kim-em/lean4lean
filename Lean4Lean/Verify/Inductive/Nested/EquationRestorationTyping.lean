import Lean4Lean.Verify.Inductive.Nested.EquationRestorationNodeSemantics

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Type-directed structural interpretation of one exact finite restoration
plan.  Only actual plan hits and unchanged atomic nodes carry endpoint typing
derivations. Application and binder typings must be assembled recursively,
so a whole restored RHS cannot be admitted as an opaque atomic premise. -/
inductive TypedExprRestoration
    (plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext)
    (Hplan : NestedRestorationPlan.Semantics plan restoredRecursors) :
    (sourceCtx targetCtx : List VExpr) →
    VExpr → VExpr → VExpr → VExpr → Prop
  | hit (node) (hnode : node ∈ plan.nodes)
      (Hnode : NestedRestoredNodeSemantics node restoredRecursors) :
      TypedExprRestoration plan Hplan sourceContext.toCtx targetContext.toCtx
        node.source node.target Hnode.sourceType Hnode.targetType
  | bvar (hnone : plan.restoreNode (.bvar index) = none)
      (hsource : sourceEnv.HasType Us.length sourceCtx (.bvar index) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx (.bvar index) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.bvar index) (.bvar index) sourceType targetType
  | sort (hnone : plan.restoreNode (.sort level) = none)
      (hsource : sourceEnv.HasType Us.length sourceCtx
        (.sort level) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx
        (.sort level) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.sort level) (.sort level) sourceType targetType
  | const (hnone : plan.restoreNode (.const name levels) = none)
      (hsource : sourceEnv.HasType Us.length sourceCtx
        (.const name levels) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx
        (.const name levels) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.const name levels) (.const name levels) sourceType targetType
  | app
      (hnone : plan.restoreNode (.app sourceFn sourceArg) = none)
      (hfn : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceFn targetFn (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody))
      (harg : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceArg targetArg sourceDomain targetDomain) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.app sourceFn sourceArg) (.app targetFn targetArg)
        (sourceBody.inst sourceArg) (targetBody.inst targetArg)
  | lam
      (hnone : plan.restoreNode (.lam sourceDomain sourceBody) = none)
      (hdomain : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceDomain targetDomain (.sort sourceLevel) (.sort targetLevel))
      (hbody : TypedExprRestoration plan Hplan
        (sourceDomain :: sourceCtx) (targetDomain :: targetCtx)
        sourceBody targetBody sourceBodyType targetBodyType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
        (.forallE sourceDomain sourceBodyType)
        (.forallE targetDomain targetBodyType)
  | forallE
      (hnone : plan.restoreNode (.forallE sourceDomain sourceBody) = none)
      (hdomain : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceDomain targetDomain (.sort sourceLevel) (.sort targetLevel))
      (hbody : TypedExprRestoration plan Hplan
        (sourceDomain :: sourceCtx) (targetDomain :: targetCtx)
        sourceBody targetBody (.sort sourceBodyLevel) (.sort targetBodyLevel)) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)
        (.sort (.imax sourceLevel sourceBodyLevel))
        (.sort (.imax targetLevel targetBodyLevel))

variable {result : Lean4Lean.ElimNestedInductive.Result}
  {prodEnv : Environment} {params : Array Expr} {auxRec : NameMap Name}
  {sourceEnv targetEnv : VEnv} {Us : List Name}
  {sourceContext targetContext : VLCtx}
  {restoredRecursors : List Name}
  {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
    targetEnv Us sourceContext targetContext}
  {Hplan : NestedRestorationPlan.Semantics plan restoredRecursors}
  {sourceCtx targetCtx : List VExpr}
  {source target sourceType targetType : VExpr}

/-- Source endpoint typing is recovered compositionally from the structural
certificate. -/
theorem TypedExprRestoration.sourceTyping
    (H : TypedExprRestoration plan Hplan sourceCtx targetCtx
      source target sourceType targetType) :
    sourceEnv.HasType Us.length sourceCtx source sourceType := by
  induction H with
  | hit node _ Hnode => exact Hnode.sourceTyping
  | bvar _ hsource _ | sort _ hsource _ | const _ hsource _ => exact hsource
  | app _ _ _ ihfn iharg => exact .appDF ihfn iharg
  | lam _ _ _ ihdomain ihbody => exact .lamDF ihdomain ihbody
  | forallE _ _ _ ihdomain ihbody => exact .forallEDF ihdomain ihbody

/-- Target endpoint typing is recovered compositionally from the structural
certificate. -/
theorem TypedExprRestoration.targetTyping
    (H : TypedExprRestoration plan Hplan sourceCtx targetCtx
      source target sourceType targetType) :
    targetEnv.HasType Us.length targetCtx target targetType := by
  induction H with
  | hit node _ Hnode => exact Hnode.targetTyping
  | bvar _ _ htarget | sort _ _ htarget | const _ _ htarget => exact htarget
  | app _ _ _ ihfn iharg => exact .appDF ihfn iharg
  | lam _ _ _ ihdomain ihbody => exact .lamDF ihdomain ihbody
  | forallE _ _ _ ihdomain ihbody => exact .forallEDF ihdomain ihbody

end VerifyInductive
end Lean4Lean
