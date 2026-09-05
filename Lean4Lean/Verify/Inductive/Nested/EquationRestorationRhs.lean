import Lean4Lean.Verify.Inductive.Nested.EquationRestorationProvenance
import Lean4Lean.Verify.Inductive.Nested.Restoration

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A scope aligned with ordinary selected lambda declarations loses no
entries when projected to its abstract typing context. -/
theorem lambdaDeclarationScope_toCtx_length
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂ (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), VLocalDecl.vlam type)) fvars scope) :
    scope.toCtx.length = fvars.length := by
  induction H with
  | nil => rfl
  | cons hhead _ ih =>
      rcases hhead with ⟨deps, type, rfl⟩
      simp [VLCtx.toCtx, ih]

/-- Exact semantic restoration package for one production rule RHS.  The
inner replacement is interpreted by a finite concrete provenance plan.  The
outer parameter lambdas are not re-proved semantically: restoration reuses
their literal source prefix, so the already translated source RHS supplies
their domains and typing derivations. -/
structure RestoredRuleRhsTranslation
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (oldRule newRule : RecursorRule)
    (Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldRule newRule)
    (sourceEnv targetEnv : VEnv) (Us : List Name) where
  opening : NestedRestorationOpening result prodEnv auxRec
    oldRule.rhs newRule.rhs
  sourceScope : VLCtx
  targetScope : VLCtx
  targetDeclarations : List.Forall₂
    (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), .vlam type))
    opening.selection.fvars.reverse targetScope
  plan : NestedRestorationPlan result prodEnv opening.params auxRec
    sourceEnv targetEnv Us (abstractForallContext [] sourceScope)
      (abstractForallContext [] targetScope)
  sourceBody : VExpr
  targetBody : VExpr
  body : RestoredExprTranslation
    (result.restoreNestedNode prodEnv opening.params auxRec) plan.Relates
    sourceEnv targetEnv Us (abstractForallContext [] sourceScope)
      (abstractForallContext [] targetScope)
      (source := sourceBody) (target := targetBody) opening.replacement
  sourceRebuilt : opening.lctx.mkLambda opening.params opening.body =
    oldRule.rhs
  sourceNotForall : oldRule.rhs.isForall = false
  /-- The whole old RHS closes this exact source endpoint.  Keeping a second,
  unrelated whole-expression target here would lose the generated-equation
  guardedness and typing seed at precisely the restoration boundary. -/
  sourceTranslation : TrExprS targetEnv Us [] oldRule.rhs
    (VExpr.wrapLams targetScope.toCtx.reverse sourceBody)

/-- The literal RHS restoration has a binder-correct semantic trace without
any separately supplied node plan.  In particular, hits below higher-order
field binders retain the extended contexts in which their checked endpoint
translations were produced. -/
theorem RestoredRuleRhsTranslation.contextualTrace
    (H : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldRule newRule Hrule sourceEnv targetEnv Us) :
    ContextualExprRestoration result prodEnv H.opening.params auxRec sourceEnv
      targetEnv Us (abstractForallContext [] H.sourceScope)
        (abstractForallContext [] H.targetScope)
        (source := H.sourceBody) (target := H.targetBody)
        H.opening.replacement :=
  H.opening.replacement.contextualTrace H.body.sourceTranslation
    H.body.targetTranslation

/-- The independently interpreted restored body, closed below the unchanged
parameter prefix, translates to the corresponding restored abstract RHS.
This is the first whole-expression semantic consequence of equation
restoration; no arbitrary abstract replacement callback appears in its type.
-/
theorem RestoredRuleRhsTranslation.restoredTranslation
    (H : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldRule newRule Hrule sourceEnv targetEnv Us) :
    TrExprS targetEnv Us [] newRule.rhs
      (VExpr.wrapLams H.targetScope.toCtx.reverse H.targetBody) := by
  have htargetNodup : H.opening.selection.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr H.opening.selectionNodup
  have hselectionLength : H.opening.params.size =
      H.opening.selection.fvars.length := H.opening.selection.size
  have hscopeLength : H.targetScope.toCtx.reverse.length =
      H.opening.selection.fvars.length := by
    simpa using lambdaDeclarationScope_toCtx_length H.targetDeclarations
  have Hresidual := TrExprS.abstractFVarLambdaSuffix
    H.targetDeclarations htargetNodup H.body.targetTranslation
  have HsourceTelescope : Expr.LambdaTelescope oldRule.rhs
      H.opening.selection.fvars.length
      (H.opening.body.abstractList H.opening.selection.fvars) := by
    have Htelescope := LocalContext.mkLambda_fvars_lambdaTelescope
      (body := H.opening.body)
      H.opening.selection.declarations
    simpa only [← H.opening.selection.expressions,
      H.sourceRebuilt] using Htelescope
  have houtput : newRule.rhs =
      H.opening.lctx.mkLambda H.opening.params H.opening.restoredBody := by
    simpa [H.sourceNotForall] using H.opening.output_eq
  have HtargetTelescope : Expr.LambdaTelescope newRule.rhs
      H.opening.selection.fvars.length
      (H.opening.restoredBody.abstractList
        H.opening.selection.fvars) := by
    have Htelescope := LocalContext.mkLambda_fvars_lambdaTelescope
      (body := H.opening.restoredBody)
      H.opening.selection.declarations
    simpa only [← H.opening.selection.expressions, ← houtput] using
      Htelescope
  have Hsame : Expr.SameLambdaPrefix
      H.opening.selection.fvars.length oldRule.rhs newRule.rhs := by
    have Hprefix := H.opening.selection.sameLambdaPrefix
      H.opening.selectionNodup H.opening.body H.opening.restoredBody
    simpa only [H.sourceRebuilt, ← houtput, hselectionLength] using Hprefix
  apply Hsame.replaceTranslatedResidual HsourceTelescope HtargetTelescope
    hscopeLength H.sourceTranslation
  simpa [abstractForallContext] using Hresidual

end VerifyInductive
end Lean4Lean
