import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRhs

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The abstract equation obtained by replacing only the RHS of a source
nested-iota equation with its independently restored body. -/
def RestoredRuleRhsTranslation.abstractRule
    (H : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us)
    (sourceRule : VDefEq) : VDefEq :=
  { sourceRule with
    rhs := VExpr.wrapLams H.targetScope.toCtx.reverse H.targetBody }

/-- Exact remaining semantic facts for turning restored RHS syntax into a
source nested-iota equation.  These are pointwise typing and guardedness
judgments, not callbacks over restoration prefixes or arbitrary expressions.
-/
structure RestoredPrimaryIotaSemantics
    (decl : VInductDecl) (sourceBlock restoredBlock : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal)
    (sourceRule : VDefEq)
    (Hsource : decl.NestedIotaRule sourceBlock owner ctor sourceRule)
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us)
    where
  recursor_mem : Hsource.recursor ∈ restoredBlock.recursors
  domains_eq : Hrhs.targetScope.toCtx.reverse = Hsource.domains
  rhsArgs : List VExpr
  rhs_spine : Hrhs.targetBody.getAppFnArgs = (.bvar Hsource.minorVar, rhsArgs)
  field_args : rhsArgs.take (Hsource.ctorArgs.length - decl.nparams) =
    Hsource.ctorArgs.drop decl.nparams
  recursive_results :
    (rhsArgs.drop (Hsource.ctorArgs.length - decl.nparams)).length =
      Hsource.recursiveArgs.length
  rhs_guarded : Hrhs.targetBody.GuardedIota
    (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
  contextWF : OnCtx Hsource.domains.reverse
    (targetEnv.IsType sourceRule.uvars)
  lhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
    Hsource.lhsBody Hsource.typeBody
  rhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
    Hrhs.targetBody Hsource.typeBody

variable {decl : VInductDecl} {sourceBlock restoredBlock : VInductBlock}
  {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
  {Hsource : decl.NestedIotaRule sourceBlock owner ctor sourceRule}
  {result : Lean4Lean.ElimNestedInductive.Result}
  {prodEnv : Environment} {auxRec : NameMap Name}
  {oldRecName newRecName : Name} {oldConcreteRule newConcreteRule : RecursorRule}
  {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
    oldConcreteRule newConcreteRule}
  {sourceEnv targetEnv : VEnv} {Us : List Name}
  {Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
    newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us}

theorem RestoredPrimaryIotaSemantics.rhsTranslation
    (H : RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor sourceRule
      Hsource Hrhs) :
    TrExprS targetEnv Us [] newConcreteRule.rhs
      (Hrhs.abstractRule sourceRule).rhs := by
  simpa [RestoredRuleRhsTranslation.abstractRule, H.domains_eq] using
    Hrhs.restoredTranslation

theorem RestoredPrimaryIotaSemantics.ruleWF
    (H : RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor sourceRule
      Hsource Hrhs) :
    (Hrhs.abstractRule sourceRule).WF targetEnv := by
  have hwf := VDefEq.wf_of_wrappedBodies H.contextWF H.lhsTyping
    H.rhsTyping
  simpa [RestoredRuleRhsTranslation.abstractRule, Hsource.lhs_wrapped,
    Hsource.type_wrapped, H.domains_eq] using hwf

/-- Pointwise restored-primary equation theorem.  All LHS, type, recursor,
owner, constructor, field-order, and arity facts are inherited from the
independently specified source nested equation; only the restored RHS facts
are replaced. -/
def RestoredPrimaryIotaSemantics.nestedIotaRule
    (H : RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor sourceRule
      Hsource Hrhs) :
    decl.NestedIotaRule restoredBlock owner ctor (Hrhs.abstractRule sourceRule) := by
  refine {
    recursor := Hsource.recursor
    recursor_mem := H.recursor_mem
    recursor_shape := Hsource.recursor_shape
    rule_uvars := Hsource.rule_uvars
    domains := Hsource.domains
    lhsBody := Hsource.lhsBody
    rhsBody := Hrhs.targetBody
    typeBody := Hsource.typeBody
    lhs_wrapped := Hsource.lhs_wrapped
    rhs_wrapped := ?_
    type_wrapped := Hsource.type_wrapped
    recursorLevels := Hsource.recursorLevels
    leadingArgs := Hsource.leadingArgs
    ctorLevels := Hsource.ctorLevels
    ctorArgs := Hsource.ctorArgs
    lhs_pattern := Hsource.lhs_pattern
    recursor_levels := Hsource.recursor_levels
    ctor_levels := Hsource.ctor_levels
    leading_arity := Hsource.leading_arity
    constructor_arity := Hsource.constructor_arity
    parameter_args := Hsource.parameter_args
    domains_arity := Hsource.domains_arity
    recursiveFields := Hsource.recursiveFields
    fieldPositions := Hsource.fieldPositions
    fieldPositions_eq := Hsource.fieldPositions_eq
    fieldPositions_ordered := Hsource.fieldPositions_ordered
    fields_at_positions := Hsource.fields_at_positions
    recursiveArgs := Hsource.recursiveArgs
    recursiveArgs_eq := Hsource.recursiveArgs_eq
    recursive_args := Hsource.recursive_args
    fieldVars := Hsource.fieldVars
    fieldVars_eq := Hsource.fieldVars_eq
    fields_in_scope := Hsource.fields_in_scope
    minorVar := Hsource.minorVar
    minor_in_scope := Hsource.minor_in_scope
    rhsArgs := H.rhsArgs
    rhs_spine := H.rhs_spine
    field_args := H.field_args
    recursive_results := H.recursive_results
    rhs_guarded := H.rhs_guarded }
  simpa [RestoredRuleRhsTranslation.abstractRule, H.domains_eq]

end VerifyInductive
end Lean4Lean
