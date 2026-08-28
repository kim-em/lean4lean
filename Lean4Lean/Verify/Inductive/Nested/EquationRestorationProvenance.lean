import Lean4Lean.Verify.Inductive.Nested.EquationRestorationTranslation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The three production branches which can stop `restoreNestedNode` before
structural traversal.  Family and constructor cases retain the exact map
lookup which classified the hit; the callback equation fixes the complete
replacement expression. -/
inductive NestedRestoreHitProvenance
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name) :
    Expr → Expr → Prop
  | recursor (hfind : auxRec.find? oldName = some newName) :
      NestedRestoreHitProvenance result env params auxRec
        (.const oldName levels) (.const newName levels)
  | family
      (hfind : result.aux2nested.find? familyName = some nested)
      (hhead : input.getAppFn = .const familyName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      NestedRestoreHitProvenance result env params auxRec input output
  | constructor
      (hfind : result.getNestedIfAuxCtor env constructorName =
        some (nested, auxiliaryFamily))
      (hhead : input.getAppFn = .const constructorName levels)
      (hhit : result.restoreNestedNode env params auxRec input = some output) :
      NestedRestoreHitProvenance result env params auxRec input output

theorem NestedRestoreHitProvenance.concreteHit
    (H : NestedRestoreHitProvenance result env params auxRec input output) :
    result.restoreNestedNode env params auxRec input = some output := by
  cases H with
  | recursor hfind =>
      exact restoreNestedNode_recursor result env params auxRec _ _ _ hfind
  | family _ _ hhit | constructor _ _ hhit => exact hhit

/-- One semantically interpreted production hit.  Its abstract endpoints are
not inferred from executable syntax: both must translate independently in the
environments relevant before and after restoration. -/
structure NestedRestoredNode
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx) where
  input : Expr
  output : Expr
  source : VExpr
  target : VExpr
  provenance : NestedRestoreHitProvenance result env params auxRec input output
  sourceTranslation :
    TrExprS sourceEnv Us sourceContext input source
  targetTranslation :
    TrExprS targetEnv Us targetContext output target

/-- A finite semantic plan for the exact production hits in one restored
equation.  Functionality prevents the abstract replacement operation from
choosing different targets for the same independently translated source. -/
structure NestedRestorationPlan
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (params : Array Expr) (auxRec : NameMap Name)
    (sourceEnv targetEnv : VEnv) (Us : List Name)
    (sourceContext targetContext : VLCtx) where
  nodes : List (NestedRestoredNode result env params auxRec sourceEnv targetEnv
    Us sourceContext targetContext)
  functional : ∀ left ∈ nodes, ∀ right ∈ nodes,
    left.source = right.source → left.target = right.target

noncomputable def NestedRestorationPlan.selectedNode?
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (source : VExpr) :
    Option (NestedRestoredNode result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) := by
  classical
  exact if h : ∃ node ∈ H.nodes, node.source = source then
      some (Classical.choose h)
    else none

/-- The abstract callback is computed from the finite provenance plan; it is
not an independently quantified semantic function. -/
noncomputable def NestedRestorationPlan.restoreNode
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (source : VExpr) : Option VExpr :=
  (H.selectedNode? source).map (fun node => node.target)

theorem NestedRestorationPlan.restoreNode_of_mem
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (node) (hnode : node ∈ H.nodes) :
    H.restoreNode node.source = some node.target := by
  have hexists : ∃ candidate ∈ H.nodes,
      candidate.source = node.source := ⟨node, hnode, rfl⟩
  rw [NestedRestorationPlan.restoreNode,
    NestedRestorationPlan.selectedNode?]
  simp only [dif_pos hexists, Option.map_some, Option.some.injEq]
  apply H.functional (Classical.choose hexists)
    (Classical.choose_spec hexists).1 node hnode
  exact (Classical.choose_spec hexists).2

/-- Membership in a concrete provenance plan supplies the exact atomic hit
required by structural expression-restoration alignment. -/
theorem NestedRestorationPlan.interpret
    (H : NestedRestorationPlan result env params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) (node) (hnode : node ∈ H.nodes) :
    RestoredNodeInterpretation
      (result.restoreNestedNode env params auxRec) H.restoreNode
      sourceEnv targetEnv Us sourceContext targetContext
      (source := node.source) (target := node.target)
      node.provenance.concreteHit where
  sourceTranslation := node.sourceTranslation
  targetTranslation := node.targetTranslation
  abstractHit := H.restoreNode_of_mem node hnode

end VerifyInductive
end Lean4Lean
