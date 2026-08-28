import Lean4Lean.Verify.Inductive.Nested.EquationRestorationProvenance
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The production hit is the recursor-renaming branch. -/
inductive NestedRestoreHitProvenance.IsRecursor :
    {result : Lean4Lean.ElimNestedInductive.Result} →
    {env : Environment} → {params : Array Expr} → {auxRec : NameMap Name} →
    {input output : Expr} →
    NestedRestoreHitProvenance result env params auxRec input output → Prop
  | intro {auxRec : NameMap Name}
      (hfind : auxRec.find? oldName = some newName) :
      IsRecursor (.recursor (levels := levels) hfind)

/-- The production hit is a family- or constructor-restoration branch. -/
inductive NestedRestoreHitProvenance.IsNonrecursor :
    {result : Lean4Lean.ElimNestedInductive.Result} →
    {env : Environment} → {params : Array Expr} → {auxRec : NameMap Name} →
    {input output : Expr} →
    NestedRestoreHitProvenance result env params auxRec input output → Prop
  | family {result : Lean4Lean.ElimNestedInductive.Result}
      {env : Environment} {params : Array Expr} {auxRec : NameMap Name}
      (hfind : result.aux2nested.find? familyName = some nested)
      (hhead : input.getAppFn = .const familyName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      IsNonrecursor (.family hfind hhead hhit)
  | constructor {result : Lean4Lean.ElimNestedInductive.Result}
      {env : Environment} {params : Array Expr} {auxRec : NameMap Name}
      (hfind : result.getNestedIfAuxCtor env constructorName =
        some (nested, auxiliaryFamily))
      (hhead : input.getAppFn = .const constructorName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      IsNonrecursor (.constructor hfind hhead hhit)

/-- Semantic behavior of one exact finite restoration-plan hit. Recursor
hits retain the precise concrete and abstract constant rename. Family and
constructor hits instead prove that their complete target is free of every
restored recursor, which is exactly the local fact needed by guarded-iota
restoration. -/
structure NestedRestoredNodeBehavior
    (node : NestedRestoredNode result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (restoredRecursors : List Name) : Prop where
  classification :
    (∃ oldName newName abstractLevels,
      node.provenance.IsRecursor ∧
      auxRec.find? oldName = some newName ∧
      node.source = .const oldName abstractLevels ∧
      node.target = .const newName abstractLevels) ∨
    (node.provenance.IsNonrecursor ∧
      node.target.containsAnyConst restoredRecursors = false)

/-- Translating the same concrete universe list on the two sides of a
recursor rename produces the same abstract universe list. -/
theorem translatedRecursorEndpoints
    (Hsource : TrExprS sourceEnv Us sourceContext
      (.const oldName levels) source)
    (Htarget : TrExprS targetEnv Us targetContext
      (.const newName levels) target) :
    ∃ abstractLevels,
      source = .const oldName abstractLevels ∧
      target = .const newName abstractLevels := by
  cases Hsource with
  | const _ hsourceLevels _ =>
      cases Htarget with
      | const _ htargetLevels _ =>
          have hlevels := Option.some.inj
            (hsourceLevels.symm.trans htargetLevels)
          subst hlevels
          exact ⟨_, rfl, rfl⟩

/-- Exact recursor provenance and the retained endpoint translations
construct the recursor branch behavior without additional semantic input. -/
theorem NestedRestoredNodeBehavior.recursor
    (node : NestedRestoredNode result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (hprovenance : node.provenance.IsRecursor)
    (hfind : auxRec.find? oldName = some newName)
    (hinput : node.input = .const oldName levels)
    (houtput : node.output = .const newName levels) :
    NestedRestoredNodeBehavior node restoredRecursors := by
  have Hsource := node.sourceTranslation
  have Htarget := node.targetTranslation
  rw [hinput] at Hsource
  rw [houtput] at Htarget
  rcases translatedRecursorEndpoints Hsource Htarget with
    ⟨abstractLevels, hsource, htarget⟩
  exact ⟨Or.inl ⟨oldName, newName, abstractLevels, hprovenance,
    hfind, hsource, htarget⟩⟩

/-- Exact semantic payload for one member of a finite restoration plan.
The two endpoint types are explicit because nested-family replacement can
change representation types; no unjustified equality between the lowered
and restored types is assumed. -/
structure NestedRestoredNodeSemantics
    (node : NestedRestoredNode result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (restoredRecursors : List Name) where
  sourceType : VExpr
  targetType : VExpr
  sourceTyping : sourceEnv.HasType Us.length sourceContext.toCtx
    node.source sourceType
  targetTyping : targetEnv.HasType Us.length targetContext.toCtx
    node.target targetType
  behavior : NestedRestoredNodeBehavior node restoredRecursors

/-- Semantics for a restoration plan are attached pointwise to its actual
finite node list.  This replaces a universally quantified callback over
arbitrary expressions with evidence only for production hits which occurred.
-/
structure NestedRestorationPlan.Semantics
    (plan : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (restoredRecursors : List Name) : Prop where
  node : ∀ candidate ∈ plan.nodes,
    Nonempty (NestedRestoredNodeSemantics candidate restoredRecursors)

/-- The exact endpoint translations already contain typing derivations.
Consequently a node behavior witness is sufficient to construct its full
semantic payload; endpoint typing is not an additional callback. -/
noncomputable def NestedRestoredNodeSemantics.ofBehavior
    (node : NestedRestoredNode result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext : sourceContext.WF sourceEnv Us.length)
    (htargetContext : targetContext.WF targetEnv Us.length)
    (behavior : NestedRestoredNodeBehavior node restoredRecursors) :
    NestedRestoredNodeSemantics node restoredRecursors := by
  let sourceWF := node.sourceTranslation.wf hsourceEnv hsourceContext
  let targetWF := node.targetTranslation.wf htargetEnv htargetContext
  let sourceType := Classical.choose sourceWF
  let targetType := Classical.choose targetWF
  have sourceTyping := Classical.choose_spec sourceWF
  have targetTyping := Classical.choose_spec targetWF
  exact { sourceType, targetType, sourceTyping, targetTyping, behavior }

/-- Branch behavior over the actual finite node list automatically supplies
complete plan semantics. -/
theorem NestedRestorationPlan.semanticsOfBehaviors
    (plan : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext)
    (hsourceEnv : sourceEnv.Ordered)
    (htargetEnv : targetEnv.Ordered)
    (hsourceContext : sourceContext.WF sourceEnv Us.length)
    (htargetContext : targetContext.WF targetEnv Us.length)
    (Hbehavior : ∀ candidate ∈ plan.nodes,
      NestedRestoredNodeBehavior candidate restoredRecursors) :
    NestedRestorationPlan.Semantics plan restoredRecursors where
  node candidate hcandidate :=
    ⟨NestedRestoredNodeSemantics.ofBehavior candidate hsourceEnv htargetEnv
      hsourceContext htargetContext
      (Hbehavior candidate hcandidate)⟩

theorem NestedRestorationPlan.Semantics.interpret
    (H : NestedRestorationPlan.Semantics plan restoredRecursors)
    (candidate) (hcandidate : candidate ∈ plan.nodes) :
    Nonempty (NestedRestoredNodeSemantics candidate restoredRecursors) :=
  H.node candidate hcandidate

end VerifyInductive
end Lean4Lean
