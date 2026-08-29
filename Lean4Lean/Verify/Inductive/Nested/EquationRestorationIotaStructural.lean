import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIota
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuarded
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationTyping

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Construct the pointwise restored-primary equation package from an exact
structural guarded-restoration certificate.  In particular, callers no
longer supply the desired target `GuardedIota` judgment. -/
def RestoredPrimaryIotaSemantics.ofStructuralGuarded
    {decl : VInductDecl} {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
    {Hsource : decl.NestedIotaRule sourceBlock owner ctor sourceRule}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    {Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us}
    (recursor_mem : Hsource.recursor ∈ restoredBlock.recursors)
    (sourceRecursors : List Name)
    (domains_eq : Hrhs.targetScope.toCtx.reverse = Hsource.domains)
    (rhsArgs : List VExpr)
    (rhs_spine : Hrhs.targetBody.getAppFnArgs =
      (.bvar Hsource.minorVar, rhsArgs))
    (field_args : rhsArgs.take (Hsource.ctorArgs.length - decl.nparams) =
      Hsource.ctorArgs.drop decl.nparams)
    (recursive_results :
      (rhsArgs.drop (Hsource.ctorArgs.length - decl.nparams)).length =
        Hsource.recursiveArgs.length)
    (contextWF : OnCtx Hsource.domains.reverse
      (targetEnv.IsType sourceRule.uvars))
    (lhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
      Hsource.lhsBody Hsource.typeBody)
    (rhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
      Hrhs.targetBody Hsource.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
    RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor
      sourceRule Hsource Hrhs where
  recursor_mem := recursor_mem
  domains_eq := domains_eq
  rhsArgs := rhsArgs
  rhs_spine := rhs_spine
  field_args := field_args
  recursive_results := recursive_results
  rhs_guarded := Hguard.targetGuarded
  contextWF := contextWF
  lhsTyping := lhsTyping
  rhsTyping := rhsTyping

/-- Fully structural pointwise package: both target guardedness and target
RHS typing are consequences of exact finite-plan certificates.  The target
type index is the independently specified source equation body type. -/
def RestoredPrimaryIotaSemantics.ofStructural
    {decl : VInductDecl} {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
    {Hsource : decl.NestedIotaRule sourceBlock owner ctor sourceRule}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    {Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us}
    (recursor_mem : Hsource.recursor ∈ restoredBlock.recursors)
    (sourceRecursors : List Name)
    (Hplan : NestedRestorationPlan.Semantics Hrhs.plan
      (restoredBlock.recursors.map (·.name)))
    (uvars_eq : Us.length = sourceRule.uvars)
    (domains_eq : Hrhs.targetScope.toCtx.reverse = Hsource.domains)
    (rhsArgs : List VExpr)
    (rhs_spine : Hrhs.targetBody.getAppFnArgs =
      (.bvar Hsource.minorVar, rhsArgs))
    (field_args : rhsArgs.take (Hsource.ctorArgs.length - decl.nparams) =
      Hsource.ctorArgs.drop decl.nparams)
    (recursive_results :
      (rhsArgs.drop (Hsource.ctorArgs.length - decl.nparams)).length =
        Hsource.recursiveArgs.length)
    (contextWF : OnCtx Hsource.domains.reverse
      (targetEnv.IsType sourceRule.uvars))
    (lhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
      Hsource.lhsBody Hsource.typeBody)
    (Htyping : TypedExprRestoration Hrhs.plan Hplan
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody sourceType Hsource.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
    RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor
      sourceRule Hsource Hrhs := by
  have htargetContext : Hrhs.targetScope.toCtx =
      Hsource.domains.reverse := by
    simpa using congrArg List.reverse domains_eq
  have rhsTyping : targetEnv.HasType sourceRule.uvars
      Hsource.domains.reverse Hrhs.targetBody Hsource.typeBody := by
    have h := Htyping.targetTyping
    simpa [abstractForallContext_toCtx, htargetContext, uvars_eq] using h
  exact .ofStructuralGuarded recursor_mem sourceRecursors domains_eq rhsArgs rhs_spine
    field_args recursive_results contextWF lhsTyping rhsTyping Hguard

end VerifyInductive
end Lean4Lean
