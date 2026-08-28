import Lean4Lean.Verify.Inductive.Nested.EquationRestorationNodeSemantics
import Lean4Lean.Verify.Inductive.Constructor.Positivity

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Source-side constant-freeness retained for an independently generated
family or constructor restoration target.  The facts refer to the exact
production node output and its exact translation context; no abstract
replacement callback appears. -/
structure GeneratedNonrecursorHitFreeness
    (node : NestedRestoredNode result prodEnv params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (sourceRecursors restoredRecursors : List Name) : Prop where
  nonrecursor : node.provenance.IsNonrecursor
  /-- Family and constructor hits have a constant application head, so they
  cannot replace a constructor-field application headed by a bound variable. -/
  sourceNotBVarHead : node.source.bvarHead? = none
  /-- Generated family and constructor names are disjoint from every old
  recursor name.  This prevents their finite replacements from swallowing an
  enclosing generated recursive-call application before its recursor head is
  restored. -/
  sourceHeadNotRecursor : ∀ name levels,
    node.input.getAppFn = .const name levels → name ∉ sourceRecursors
  sourceAvoids : node.output.AvoidsConsts restoredRecursors
  contextFree : VLCtx.NoIndConsts restoredRecursors targetContext

/-- A family or constructor restoration hit has a constant-headed concrete
source, and exact expression translation preserves that application spine.
Thus the abstract source cannot be headed by a bound variable; this field of
`GeneratedNonrecursorHitFreeness` is executable provenance, not residual
semantic input. -/
theorem NestedRestoredNode.sourceNotBVarHeadOfNonrecursor
    (node : NestedRestoredNode result prodEnv params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (H : node.provenance.IsNonrecursor) :
    node.source.bvarHead? = none := by
  cases H with
  | family hfind hhead hhit | constructor hfind hhead hhit =>
      rcases checkPositivityStep.TrExprS.constAppSpine
          node.sourceTranslation hhead with
        ⟨levels, args, hspine, _hlevels, _hargs⟩
      unfold VExpr.bvarHead?
      rw [hspine]

/-- Translation of the independently generated target preserves its retained
source-side recursor absence.  Projection behavior is the single global
typing-spec property already used by ordinary equation verification. -/
theorem GeneratedNonrecursorHitFreeness.targetRecursorFree
    (H : GeneratedNonrecursorHitFreeness node sourceRecursors
      restoredRecursors)
    (hproj : ProjectionConstPreservation) :
    node.target.containsAnyConst restoredRecursors = false :=
  checkPositivityStep.TrExprS.noConstsOfSourceAvoids H.sourceAvoids
    H.contextFree (fun Hproj hfree => hproj _ Hproj hfree)
    node.targetTranslation

/-- An independently generated non-recursor target supplies the complete
family/constructor branch of finite-node behavior. -/
theorem GeneratedNonrecursorHitFreeness.behavior
    (H : GeneratedNonrecursorHitFreeness node sourceRecursors
      restoredRecursors)
    (hproj : ProjectionConstPreservation) :
    NestedRestoredNodeBehavior node restoredRecursors :=
  ⟨Or.inr ⟨H.nonrecursor, H.targetRecursorFree hproj⟩⟩

/-- Exact atomic provenance for every member of one finite restoration plan.
Each member is either the literal auxiliary-recursor constant rename or an
independently generated family/constructor target with source-side absence.
-/
structure NestedRestorationPlan.AtomicProvenance
    (plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext)
    (sourceRecursors restoredRecursors : List Name) : Prop where
  classify : ∀ node ∈ plan.nodes,
    (∃ oldName newName levels,
      node.provenance.IsRecursor ∧
      auxRec.find? oldName = some newName ∧
      node.input = .const oldName levels ∧
      node.output = .const newName levels) ∨
    GeneratedNonrecursorHitFreeness node sourceRecursors restoredRecursors

/-- Atomic provenance constructs branch behavior for every actual plan node.
-/
theorem NestedRestorationPlan.AtomicProvenance.behaviors
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (hproj : ProjectionConstPreservation) :
    ∀ node ∈ plan.nodes,
      NestedRestoredNodeBehavior node restoredRecursors := by
  intro node hnode
  rcases H.classify node hnode with
    ⟨oldName, newName, levels, hprovenance, hfind, hinput, houtput⟩ |
      Hnonrecursor
  · exact NestedRestoredNodeBehavior.recursor node hprovenance hfind
      hinput houtput
  · exact Hnonrecursor.behavior hproj

/-- Exact atomic provenance plus ordinary environment/context validity gives
the complete finite plan semantics, including endpoint typings. -/
theorem NestedRestorationPlan.AtomicProvenance.semantics
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {params : Array Expr} {auxRec : NameMap Name}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    {sourceContext targetContext : VLCtx}
    {sourceRecursors restoredRecursors : List Name}
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext : sourceContext.WF sourceEnv Us.length)
    (htargetContext : targetContext.WF targetEnv Us.length)
    (hproj : ProjectionConstPreservation) :
    NestedRestorationPlan.Semantics plan restoredRecursors :=
  plan.semanticsOfBehaviors hsourceEnv htargetEnv hsourceContext
    htargetContext (H.behaviors hproj)

end VerifyInductive
end Lean4Lean
