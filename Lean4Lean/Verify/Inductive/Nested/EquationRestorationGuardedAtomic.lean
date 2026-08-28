import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFreeness

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successful lookup in the finite abstract replacement plan is witnessed
by one of its exact production nodes.  This is the converse of
`NestedRestorationPlan.restoreNode_of_mem`. -/
theorem NestedRestorationPlan.exists_node_of_restoreNode_eq_some
    (plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext)
    (hhit : plan.restoreNode source = some target) :
    ∃ node ∈ plan.nodes,
      node.source = source ∧ node.target = target := by
  classical
  unfold NestedRestorationPlan.restoreNode at hhit
  unfold NestedRestorationPlan.selectedNode? at hhit
  split at hhit
  · rename_i hexists
    simp only [Option.map_some, Option.some.injEq] at hhit
    exact ⟨Classical.choose hexists, (Classical.choose_spec hexists).1,
      (Classical.choose_spec hexists).2, hhit⟩
  · simp at hhit

/-- Every auxiliary-recursor rename key belongs to the source guardedness
set.  This exact finite-domain property is supplied by the generated
recursor block and `mkAuxRecNameMap`; it is deliberately weaker than a
global injectivity or total-renaming assumption. -/
def NestedRestorationPlan.RecursorKeysCovered
    (auxRec : NameMap Name) (sourceRecursors : List Name) : Prop :=
  ∀ oldName newName, auxRec.find? oldName = some newName →
    oldName ∈ sourceRecursors

/-- An atomic production hit on an expression already guarded by the old
recursor set cannot be the literal recursor-constant rename: guardedness
would say that old recursor is absent while the finite-map domain says it is
one of the source recursors.  Hence the hit is a family/constructor
replacement, whose independently generated target is recursor-free. -/
theorem NestedRestorationPlan.AtomicProvenance.guardedHitTarget
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (H : plan.AtomicProvenance sourceRecursors targetRecursors)
    (hkeys : NestedRestorationPlan.RecursorKeysCovered auxRec sourceRecursors)
    (hproj : ProjectionConstPreservation)
    (hhit : plan.restoreNode source = some target)
    (hguarded : source.GuardedIota sourceRecursors fieldVars depth) :
    target.GuardedIota targetRecursors fieldVars depth := by
  rcases plan.exists_node_of_restoreNode_eq_some hhit with
    ⟨node, hnode, hsource, htarget⟩
  have Hbehavior := H.behaviors hproj node hnode
  rcases Hbehavior.classification with
    ⟨oldName, newName, levels, _hrecursor, hfind,
      hnodeSource, _hnodeTarget⟩ |
    ⟨_nonrecursor, hfree⟩
  · have holdMem : oldName ∈ sourceRecursors := hkeys oldName newName hfind
    have hsourceEq : source = .const oldName levels :=
      hsource.symm.trans hnodeSource
    rw [hsourceEq] at hguarded
    have hnot : oldName ∉ sourceRecursors := by
      generalize heq : (.const oldName levels : VExpr) = guardedExpr at hguarded
      cases hguarded <;>
        simp_all [VExpr.mkApps_append, VExpr.mkApps]
    exact False.elim (hnot holdMem)
  · apply VExpr.GuardedIota.ofContainsAnyConstFalse
    rwa [htarget] at hfree

end VerifyInductive
end Lean4Lean
