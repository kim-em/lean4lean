import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Verify.Inductive.Nested.Replacement
import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationBatch
import Lean4Lean.Verify.Inductive.Nested.PrimaryEquations
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaOperationalSemantics
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Constructor.Positivity

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Smallest source-stage typing premise for one restored primary equation.
It is indexed by the independently specified nested-iota shape and the exact
target environment; RHS typing is intentionally absent because it is derived
from the restoration tree below. -/
structure RestoredPrimaryIotaSourceTyping
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
    (targetEnv : VEnv)
    (Hsource : decl.NestedIotaRule block owner ctor sourceRule) : Prop where
  contextWF : OnCtx Hsource.domains.reverse
    (targetEnv.IsType sourceRule.uvars)
  lhsTyping : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
    Hsource.lhsBody Hsource.typeBody

/-- Semantic interpretation of the exact executable rule-restoration list
for one primary recursor.  The abstract output list is forced to consist of
the restored RHS endpoints of these very production rules. -/
inductive RestoredPrimaryIotaRuleTrace
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (P : NestedInstalledProduction prodEnv)
    (targetVEnv : VEnv) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ {oldRules newRules},
      RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules →
      List VConstVal → List VDefEq → Prop
  | nil : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName (.nil) [] []
  | cons
      (Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
        oldRule newRule)
      (Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules)
      (abstractRule : VDefEq)
      (Hshape : decl.NestedIotaRule block owner ctor abstractRule)
      (Hwf : abstractRule.WF targetVEnv)
      (Hrest : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
        P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
      RestoredPrimaryIotaRuleTrace decl block owner result prodEnv P
        targetVEnv auxRec oldRecName newRecName (.cons Hrule Hrules) (ctor :: ctors)
        (abstractRule :: rules)

theorem RestoredPrimaryIotaRuleTrace.forall₂
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    List.Forall₂ (fun ctor rule =>
      Nonempty (decl.NestedIotaRule block owner ctor rule)) ctors rules := by
  induction H with
  | nil => exact .nil
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    exact .cons ⟨Hshape⟩ ih

theorem RestoredPrimaryIotaRuleTrace.rulesWF
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    rcases List.mem_cons.mp hrule with rfl | hrule
    · exact Hwf
    · exact ih hrule

/-- The exact abstract rule batch interpreting one restored primary recursor.
Keeping the batch existential here lets a trace fold determine the final
abstract rule list rather than asking final assembly to guess it in advance. -/
structure RestoredPrimaryIotaFamilySemantics
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    (owner : VInductiveType)
    (P : NestedInstalledProduction loweredEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  rules : List VDefEq
  trace : RestoredPrimaryIotaRuleTrace decl block owner result loweredEnv
    P targetVEnv auxRec (Lean.mkRecName indType.name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.restored.restoration.rules owner.ctors rules

/-- Mutual-family primary equation semantics, indexed simultaneously by the
canonical source-family interpretation and the exact operational restoration
trace.  Consequently family order, constructor order, and rule cardinality
are consequences rather than final-assembly assumptions. -/
inductive RestoredPrimaryIotaSemanticTrace
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv)
    {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {sourceTypes : List InductiveType}
        {sourceProdEnv targetProdEnv : Environment}
        {Htrace : StateForMTrace
          (RestoredInductiveStep result loweredEnv auxRec allIndNames)
          sourceTypes sourceProdEnv targetProdEnv}
        {owners : List VInductiveType} {recursors : List VConstVal},
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors →
      List VInductiveType → List VDefEq → Prop
  | nil {lparams safety sourceVEnv envTypes envCtors result loweredEnv auxRec
      allIndNames} (sourceProdEnv : Environment) :
      RestoredPrimaryIotaSemanticTrace decl block targetVEnv
        P
        (RestoredSourceInductiveSemanticTrace.nil
          (decl := decl) (lparams := lparams) (safety := safety)
          (sourceVEnv := sourceVEnv) (envTypes := envTypes)
          (envCtors := envCtors) (result := result) (loweredEnv := loweredEnv)
          (auxRec := auxRec) (allIndNames := allIndNames) sourceProdEnv) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : StateForMTrace
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : RestoredSourceInductiveSemanticTrace decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors)
      (Hhead : RestoredPrimaryIotaRuleTrace decl block owner result loweredEnv
        P targetVEnv auxRec (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName
        Hstep.restored.recursor.restored.restoration.rules owner.ctors
        headRules)
      (Hrules : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hrest
        owners tailRules) :
      RestoredPrimaryIotaSemanticTrace decl block targetVEnv P
        (.cons Hstep Htail Hheader Hconstructors Hrecursor Hrest)
        (owner :: owners) (headRules ++ tailRules)

/-- Fold exact per-family primary equation interpretations over the already
constructed source semantic trace.  This is the aggregate constructor used at
the executable/specification boundary; family order and final rule-list shape
come solely from the two input traces. -/
theorem RestoredSourceInductiveSemanticTrace.primaryIotaSemanticTrace
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv)
    {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {block : VInductBlock}
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (targetVEnv : VEnv)
    (Hfamilies : ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget)
      (_Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (_Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (_Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors),
      Nonempty (RestoredPrimaryIotaFamilySemantics decl block targetVEnv owner
        P Hstep)) :
    ∃ rules, RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource
      owners rules := by
  induction Hsource with
  | nil sourceProdEnv => exact ⟨[], .nil sourceProdEnv⟩
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    rcases Hfamilies _ _ _ _ Hstep Hheader Hconstructors Hrecursor with
      ⟨Hhead⟩
    rcases ih with ⟨tailRules, Hrules⟩
    exact ⟨Hhead.rules ++ tailRules,
      .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead.trace
        Hrules⟩

/-- Membership-indexed variant of `primaryIotaSemanticTrace`.  The source
trace itself supplies membership of each visited family, allowing downstream
producers to recover its unique operational family position instead of
accepting a semantic callback for arbitrary unrelated restoration steps. -/
theorem RestoredSourceInductiveSemanticTrace.primaryIotaSemanticTraceOfMem
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv)
    {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {block : VInductBlock}
    (Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (targetVEnv : VEnv)
    (Hfamilies : ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (_Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      (_Hconstructors : RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors) →
      (_Hrecursor : RestoredPrimaryRecursorSemantics decl owner safety
        Hstep.restored.recursor envCtors) →
      Nonempty (RestoredPrimaryIotaFamilySemantics decl block targetVEnv owner
        P Hstep)) :
    ∃ rules, RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource
      owners rules := by
  induction Hsource with
  | nil sourceProdEnv => exact ⟨[], .nil sourceProdEnv⟩
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    rcases Hfamilies _ _ _ _ Hstep (by simp) Hheader Hconstructors Hrecursor
      with ⟨Hhead⟩
    rcases ih (fun indType stepSource stepTarget owner Hstep hmem Hheader
        Hconstructors Hrecursor =>
      Hfamilies indType stepSource stepTarget owner Hstep (by simp [hmem])
        Hheader Hconstructors Hrecursor) with ⟨tailRules, Hrules⟩
    exact ⟨Hhead.rules ++ tailRules,
      .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead.trace
        Hrules⟩

theorem RestoredPrimaryIotaSemanticTrace.familyTrace
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules) :
    RestoredPrimaryIotaFamilyTrace decl block owners rules :=
  match H with
  | .nil _ => .nil
  | .cons _ _ _ _ _ _ Hhead Hrules =>
    .cons (by simpa using Hhead.forall₂) Hrules.familyTrace

/-- The exact restoration-indexed semantic trace is the complete primary
iota certificate required by nested compilation. -/
theorem RestoredPrimaryIotaSemanticTrace.certificate
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaListCertificate decl block rules :=
  H.familyTrace.certificate htypes

theorem RestoredPrimaryIotaSemanticTrace.build
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaBuildCertificate decl block rules :=
  (H.certificate htypes).toBuild

theorem RestoredPrimaryIotaSemanticTrace.length
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    rules.length = decl.ownedConstructors.length :=
  (H.certificate htypes).length

theorem RestoredPrimaryIotaSemanticTrace.rulesWF
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners
      rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead Hrules ih =>
    rcases List.mem_append.mp hrule with hrule | hrule
    · exact Hhead.rulesWF rule hrule
    · exact ih hrule

end VerifyInductive
end Lean4Lean
