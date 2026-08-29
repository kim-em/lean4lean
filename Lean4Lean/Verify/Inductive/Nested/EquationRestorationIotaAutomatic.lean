import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFreeness
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIotaStructural

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Exact atomic provenance discharges the finite-plan semantics argument of
the structural restored-equation theorem.  The remaining two certificates
are syntax-directed over the actual restored RHS; callers cannot postulate a
semantic interpretation for an arbitrary replacement callback. -/
noncomputable def RestoredPrimaryIotaSemantics.ofAtomicStructural
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
    {sourceType : VExpr}
    (recursor_mem : Hsource.recursor ∈ restoredBlock.recursors)
    (sourceRecursors : List Name)
    (Hatomic : NestedRestorationPlan.AtomicProvenance Hrhs.plan
      sourceRecursors (restoredBlock.recursors.map (·.name)))
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext :
      (abstractForallContext [] Hrhs.sourceScope).WF sourceEnv Us.length)
    (htargetContext :
      (abstractForallContext [] Hrhs.targetScope).WF targetEnv Us.length)
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
    (Htyping : TypedExprRestoration Hrhs.plan
      (Hatomic.semantics hsourceEnv htargetEnv hsourceContext htargetContext
        )
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody sourceType Hsource.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
    RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor
      sourceRule Hsource Hrhs :=
  .ofStructural recursor_mem sourceRecursors
    (Hatomic.semantics hsourceEnv htargetEnv hsourceContext htargetContext
      )
    uvars_eq domains_eq rhsArgs rhs_spine field_args recursive_results
    contextWF lhsTyping Htyping Hguard

/-- Pointwise source nested-iota rule obtained from exact atomic provenance
and structural restoration of the actual RHS. -/
noncomputable def VInductDecl.NestedIotaRule.ofAtomicStructural
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
    {sourceType : VExpr}
    (recursor_mem : Hsource.recursor ∈ restoredBlock.recursors)
    (sourceRecursors : List Name)
    (Hatomic : NestedRestorationPlan.AtomicProvenance Hrhs.plan
      sourceRecursors (restoredBlock.recursors.map (·.name)))
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext :
      (abstractForallContext [] Hrhs.sourceScope).WF sourceEnv Us.length)
    (htargetContext :
      (abstractForallContext [] Hrhs.targetScope).WF targetEnv Us.length)
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
    (Htyping : TypedExprRestoration Hrhs.plan
      (Hatomic.semantics hsourceEnv htargetEnv hsourceContext htargetContext
        )
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody sourceType Hsource.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
    decl.NestedIotaRule restoredBlock owner ctor (Hrhs.abstractRule sourceRule) :=
  (RestoredPrimaryIotaSemantics.ofAtomicStructural recursor_mem sourceRecursors Hatomic
    hsourceEnv htargetEnv hsourceContext htargetContext uvars_eq
    domains_eq rhsArgs rhs_spine field_args recursive_results contextWF
    lhsTyping Htyping Hguard).nestedIotaRule

end VerifyInductive
end Lean4Lean
