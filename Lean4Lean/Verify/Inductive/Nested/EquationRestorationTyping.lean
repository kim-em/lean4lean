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
  | leaf
      (hsource : sourceEnv.HasType Us.length sourceCtx source sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx source targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        source source sourceType targetType
  | bvar
      (hsource : sourceEnv.HasType Us.length sourceCtx (.bvar index) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx (.bvar index) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.bvar index) (.bvar index) sourceType targetType
  | sort
      (hsource : sourceEnv.HasType Us.length sourceCtx
        (.sort level) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx
        (.sort level) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.sort level) (.sort level) sourceType targetType
  | const
      (hsource : sourceEnv.HasType Us.length sourceCtx
        (.const name levels) sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx
        (.const name levels) targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.const name levels) (.const name levels) sourceType targetType
  | app
      (hfn : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceFn targetFn (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody))
      (harg : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceArg targetArg sourceDomain targetDomain) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.app sourceFn sourceArg) (.app targetFn targetArg)
        (sourceBody.inst sourceArg) (targetBody.inst targetArg)
  | lam
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
      (hdomain : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceDomain targetDomain (.sort sourceLevel) (.sort targetLevel))
      (hbody : TypedExprRestoration plan Hplan
        (sourceDomain :: sourceCtx) (targetDomain :: targetCtx)
        sourceBody targetBody (.sort sourceBodyLevel) (.sort targetBodyLevel)) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)
        (.sort (.imax sourceLevel sourceBodyLevel))
        (.sort (.imax targetLevel targetBodyLevel))
  | projection
      (sourceExpansion : VExpr.ProjectionSupportExpansion
        sourceMajor sourceTarget)
      (targetExpansion : VExpr.ProjectionSupportExpansion
        targetMajor targetTarget)
      (hmajor : TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceMajor targetMajor sourceMajorType targetMajorType)
      (hsource : sourceEnv.HasType Us.length sourceCtx
        sourceTarget sourceType)
      (htarget : targetEnv.HasType Us.length targetCtx
        targetTarget targetType) :
      TypedExprRestoration plan Hplan sourceCtx targetCtx
        sourceTarget targetTarget sourceType targetType

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
  | leaf hsource _ => exact hsource
  | bvar hsource _ | sort hsource _ | const hsource _ => exact hsource
  | app _ _ ihfn iharg => exact .appDF ihfn iharg
  | lam _ _ ihdomain ihbody => exact .lamDF ihdomain ihbody
  | forallE _ _ ihdomain ihbody => exact .forallEDF ihdomain ihbody
  | projection _ _ _ hsource _ _ => exact hsource

/-- Target endpoint typing is recovered compositionally from the structural
certificate. -/
theorem TypedExprRestoration.targetTyping
    (H : TypedExprRestoration plan Hplan sourceCtx targetCtx
      source target sourceType targetType) :
    targetEnv.HasType Us.length targetCtx target targetType := by
  induction H with
  | hit node _ Hnode => exact Hnode.targetTyping
  | leaf _ htarget => exact htarget
  | bvar _ htarget | sort _ htarget | const _ htarget => exact htarget
  | app _ _ ihfn iharg => exact .appDF ihfn iharg
  | lam _ _ ihdomain ihbody => exact .lamDF ihdomain ihbody
  | forallE _ _ ihdomain ihbody => exact .forallEDF ihdomain ihbody
  | projection _ _ _ _ htarget _ => exact htarget

end VerifyInductive
end Lean4Lean
