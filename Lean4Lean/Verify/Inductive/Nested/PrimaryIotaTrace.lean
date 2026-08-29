import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationIota
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationBatch
import Lean4Lean.Verify.Inductive.Nested.PrimaryEquations
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaLhsAlignment
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaNodes
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaProducerAlignment

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

/-- Pointwise semantic evidence over the actual finite RHS-restoration plan.
This is the admissible payload stored by primary traces: target typing and
guardedness must be assembled structurally, while context/LHS typing remains
an explicit source-stage judgment. -/
structure RestoredPrimaryIotaStructuralEvidence
    {decl : VInductDecl} {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
    (Hsource : decl.NestedIotaRule sourceBlock owner ctor sourceRule)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us)
    where
  recursorMem : Hsource.recursor ∈ restoredBlock.recursors
  sourceRecursors : List Name
  nodes : NestedRestorationNodeEvidence sourceRecursors
    (restoredBlock.recursors.map (·.name)) Hrhs.plan.nodes
  sourceEnvOrdered : sourceEnv.Ordered
  targetEnvOrdered : targetEnv.Ordered
  sourceContextWF :
    (abstractForallContext [] Hrhs.sourceScope).WF sourceEnv Us.length
  targetContextWF :
    (abstractForallContext [] Hrhs.targetScope).WF targetEnv Us.length
  uvars : Us.length = sourceRule.uvars
  domains : Hrhs.targetScope.toCtx.reverse = Hsource.domains
  rhsArgs : List VExpr
  rhsSpine : Hrhs.targetBody.getAppFnArgs =
    (.bvar Hsource.minorVar, rhsArgs)
  fieldArgs : rhsArgs.take (Hsource.ctorArgs.length - decl.nparams) =
    Hsource.ctorArgs.drop decl.nparams
  recursiveResults :
    (rhsArgs.drop (Hsource.ctorArgs.length - decl.nparams)).length =
      Hsource.recursiveArgs.length
  sourceTyping : RestoredPrimaryIotaSourceTyping targetEnv Hsource
  sourceType : VExpr
  typing : TypedExprRestoration Hrhs.plan
    (nodes.atomicProvenance.semantics sourceEnvOrdered targetEnvOrdered
      sourceContextWF targetContextWF)
    (abstractForallContext [] Hrhs.sourceScope).toCtx
    (abstractForallContext [] Hrhs.targetScope).toCtx
    Hrhs.sourceBody Hrhs.targetBody sourceType Hsource.typeBody
  guarded : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
    (restoredBlock.recursors.map (·.name)) Hsource.fieldVars 0
    Hrhs.sourceBody Hrhs.targetBody

def RestoredPrimaryIotaStructuralEvidence.semantics
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
    (E : RestoredPrimaryIotaStructuralEvidence
      (restoredBlock := restoredBlock) Hsource Hrhs) :
    RestoredPrimaryIotaSemantics decl sourceBlock restoredBlock owner ctor
      sourceRule Hsource Hrhs :=
  .ofStructural E.recursorMem E.sourceRecursors
    (E.nodes.atomicProvenance.semantics E.sourceEnvOrdered E.targetEnvOrdered
      E.sourceContextWF E.targetContextWF)
    E.uvars E.domains E.rhsArgs E.rhsSpine E.fieldArgs E.recursiveResults
    E.sourceTyping.contextWF E.sourceTyping.lhsTyping E.typing E.guarded

/-- Semantic payload for one constructor at one exact entry of an executable
primary rule-restoration list. -/
structure RestoredPrimaryIotaRuleSemantics
    (decl : VInductDecl) (restoredBlock : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (P : NestedInstalledProduction prodEnv)
    (targetVEnv : VEnv) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (oldRule newRule : RecursorRule)
    (Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldRule newRule) where
  sourceBlock : VInductBlock
  sourceRule : VDefEq
  source : decl.NestedIotaRule sourceBlock owner ctor sourceRule
  sourceEnv : VEnv
  uvars : List Name
  generated : RestoredPrimaryGeneratedSource P oldRecName oldRule decl
    sourceBlock owner ctor sourceRule source uvars
  rhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
    newRecName oldRule newRule Hrule sourceEnv targetVEnv uvars
  alignment : GeneratedEquationRestorationAlignment generated.witness rhs
  lhsApplication : generated.nested.LhsApplicationCertificate targetVEnv
  evidence : RestoredPrimaryIotaStructuralEvidence
    (restoredBlock := restoredBlock) source rhs
  sourceType : evidence.sourceType =
    generated.witness.translation.typeBody

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

/-- Build the exact trace payload for one restored primary rule.  The
generated equation fixes the source nested-iota shape, while target RHS typing
and guardedness are obtained structurally from the actual restoration plan.

The LHS is reconstructed from an exact restored recursor/constructor
application certificate. The restored source environment is not in general
an extension of the abstract lowered environment in which the generated
equation was checked, so no generated typing derivation is transported. -/
noncomputable def RestoredPrimaryIotaRuleSemantics.ofGeneratedAtomicStructural
    {prodEnv : Environment} {P : NestedInstalledProduction prodEnv}
    {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < P.production.entries.length}
    {i : Nat} {hctor : i < P.indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : P.production.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {decl : VInductDecl} {sourceBlock restoredBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal}
    (S : P.production.GeneratedNestedIotaSource G decl sourceBlock owner ctor)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv}
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us)
    (recursorMem : S.source.recursor ∈ restoredBlock.recursors)
    (recursorName : oldRecName =
      Lean.mkRecName P.indTypes[generatedOwner]!.name)
    (concreteRule : oldConcreteRule =
      getElem
        (P.production.generated.entry generatedOwner howner).info.rules
        i G.alignment.sourceRule_lt)
    (Halignment : GeneratedEquationRestorationAlignment G Hrhs)
    (sourceRecursors : List Name)
    (Hnodes : NestedRestorationNodeEvidence sourceRecursors
      (restoredBlock.recursors.map (·.name)) Hrhs.plan.nodes)
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext :
      (abstractForallContext [] Hrhs.sourceScope).WF sourceEnv Us.length)
    (htargetContext :
      (abstractForallContext [] Hrhs.targetScope).WF targetEnv Us.length)
    (domains_eq : Hrhs.targetScope.toCtx.reverse = S.source.domains)
    (rhsArgs : List VExpr)
    (rhs_spine : Hrhs.targetBody.getAppFnArgs =
      (.bvar S.source.minorVar, rhsArgs))
    (field_args : rhsArgs.take (S.source.ctorArgs.length - decl.nparams) =
      S.source.ctorArgs.drop decl.nparams)
    (recursive_results :
      (rhsArgs.drop (S.source.ctorArgs.length - decl.nparams)).length =
        S.source.recursiveArgs.length)
    (HlhsAlignment : S.RestoredPrimaryLhsSpineAlignment targetEnv)
    (Htyping : TypedExprRestoration Hrhs.plan
      (Hnodes.atomicProvenance.semantics hsourceEnv htargetEnv hsourceContext
        htargetContext)
      (abstractForallContext [] Hrhs.sourceScope).toCtx
      (abstractForallContext [] Hrhs.targetScope).toCtx
      Hrhs.sourceBody Hrhs.targetBody
        G.translation.typeBody S.source.typeBody)
    (Hguard : GuardedExprRestoration Hrhs.plan.Relates sourceRecursors
      (restoredBlock.recursors.map (·.name)) S.source.fieldVars 0
      Hrhs.sourceBody Hrhs.targetBody) :
    RestoredPrimaryIotaRuleSemantics decl restoredBlock owner ctor result
      prodEnv P targetEnv auxRec oldRecName newRecName oldConcreteRule
      newConcreteRule Hrule := by
  subst oldRecName
  subst oldConcreteRule
  let Hgenerated := P.primaryGeneratedSourceAt generatedOwner howner i hctor
    G S
  let HlhsApplication := HlhsAlignment.certificate
  have HsourceTyping : RestoredPrimaryIotaSourceTyping targetEnv
      S.source := {
    contextWF := by
      have Hctx : OnCtx Hrhs.targetScope.toCtx
          (targetEnv.IsType Us.length) := by
        simpa using htargetContext.toCtx
      have hdomains : Hrhs.targetScope.toCtx =
          S.source.domains.reverse := by
        simpa using congrArg List.reverse domains_eq
      simpa only [hdomains, S.uvars] using Hctx
    lhsTyping := by
      simpa only [S.domains, S.lhsBody, S.typeBody, S.uvars] using
        HlhsApplication.targetTyping }
  refine {
    sourceBlock := sourceBlock
    sourceRule := generatedRule
    source := S.source
    generated := Hgenerated
    sourceEnv := sourceEnv
    uvars := Us
    rhs := Hrhs
    alignment := Halignment
    lhsApplication := HlhsApplication
    evidence := {
      recursorMem := recursorMem
      sourceRecursors := sourceRecursors
      nodes := Hnodes
      sourceEnvOrdered := hsourceEnv
      targetEnvOrdered := htargetEnv
      sourceContextWF := hsourceContext
      targetContextWF := htargetContext
      uvars := S.uvars
      domains := domains_eq
      rhsArgs := rhsArgs
      rhsSpine := rhs_spine
      fieldArgs := field_args
      recursiveResults := recursive_results
      sourceTyping := HsourceTyping
      sourceType := G.translation.typeBody
      typing := Htyping
      guarded := Hguard }
    sourceType := rfl }

/-- Build the primary rule trace from semantic evidence at every indexed entry
of the exact executable restoration list.  The constructor count is the only
list-level premise; restored-rule cardinality follows from `RulesRestoration`.
-/
theorem RulesRestoration.primaryIotaRuleTrace
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {P : NestedInstalledProduction prodEnv}
    {targetVEnv : VEnv} {auxRec : NameMap Name}
    {oldRecName newRecName : Name} {oldRules newRules : List RecursorRule}
    (H : RulesRestoration result prodEnv auxRec oldRecName newRecName
      oldRules newRules)
    (ctors : List VConstVal) (hlength : ctors.length = oldRules.length)
    (Hsemantic : ∀ i (hctor : i < ctors.length)
      (hold : i < oldRules.length) (hnew : i < newRules.length),
      Nonempty (RestoredPrimaryIotaRuleSemantics decl block owner ctors[i]
        result prodEnv P targetVEnv auxRec oldRecName newRecName oldRules[i]
          newRules[i] (H.entry i hold hnew))) :
    ∃ rules, RestoredPrimaryIotaRuleTrace decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName H ctors rules := by
  induction H generalizing ctors with
  | nil =>
    have : ctors = [] := List.eq_nil_of_length_eq_zero hlength
    subst ctors
    exact ⟨[], .nil⟩
  | @cons oldRule newRule oldRules newRules Hrule Hrules ih =>
    cases ctors with
    | nil => simp at hlength
    | cons ctor ctors =>
      have htailLength : ctors.length = oldRules.length := by
        simpa using hlength
      rcases Hsemantic 0 (by simp) (by simp) (by simp) with ⟨Hhead⟩
      rcases ih ctors htailLength (fun i hctor hold hnew => by
        have HS := Hsemantic (Nat.succ i) (by simpa) (by simpa) (by simpa)
        change Nonempty (RestoredPrimaryIotaRuleSemantics decl block owner
          ctors[i] result prodEnv P targetVEnv auxRec oldRecName newRecName
            oldRules[i] newRules[i] (Hrules.entry i hold hnew)) at HS
        exact HS) with
        ⟨rules, Htail⟩
      exact ⟨Hhead.rhs.abstractRule Hhead.sourceRule :: rules,
        .cons Hrule Hrules (Hhead.rhs.abstractRule Hhead.sourceRule)
          Hhead.evidence.semantics.nestedIotaRule
          Hhead.evidence.semantics.ruleWF Htail⟩

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
