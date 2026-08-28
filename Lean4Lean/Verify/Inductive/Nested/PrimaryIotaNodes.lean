import Lean4Lean.Verify.Inductive.Nested.EquationRestorationFreeness

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Finite evidence over the literal node list of one restoration plan.
Every production hit is classified in list order, so later plan semantics do
not depend on a universally quantified classification callback. -/
inductive NestedRestorationNodeEvidence
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {params : Array Expr} {auxRec : NameMap Name}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    {sourceContext targetContext : VLCtx}
    (sourceRecursors restoredRecursors : List Name) :
    List (NestedRestoredNode result prodEnv params auxRec sourceEnv targetEnv
      Us sourceContext targetContext) → Prop
  | nil : NestedRestorationNodeEvidence sourceRecursors restoredRecursors []
  | recursor
      (hprovenance : node.provenance.IsRecursor)
      (hfind : auxRec.find? oldName = some newName)
      (hinput : node.input = .const oldName levels)
      (houtput : node.output = .const newName levels)
      (Hrest : NestedRestorationNodeEvidence sourceRecursors
        restoredRecursors nodes) :
      NestedRestorationNodeEvidence sourceRecursors restoredRecursors
        (node :: nodes)
  | nonrecursor
      (Hnode : GeneratedNonrecursorHitFreeness node sourceRecursors
        restoredRecursors)
      (Hrest : NestedRestorationNodeEvidence sourceRecursors
        restoredRecursors nodes) :
      NestedRestorationNodeEvidence sourceRecursors restoredRecursors
        (node :: nodes)

theorem NestedRestorationNodeEvidence.classify
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {params : Array Expr} {auxRec : NameMap Name}
    {sourceEnv targetEnv : VEnv} {Us : List Name}
    {sourceContext targetContext : VLCtx}
    {sourceRecursors restoredRecursors : List Name}
    {nodes : List (NestedRestoredNode result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext)}
    (H : NestedRestorationNodeEvidence sourceRecursors restoredRecursors
      nodes) :
    ∀ node ∈ nodes,
      (∃ oldName newName levels,
        node.provenance.IsRecursor ∧
        auxRec.find? oldName = some newName ∧
        node.input = .const oldName levels ∧
        node.output = .const newName levels) ∨
      GeneratedNonrecursorHitFreeness node sourceRecursors
        restoredRecursors := by
  intro candidate hcandidate
  induction H with
  | nil => simp at hcandidate
  | recursor hprovenance hfind hinput houtput Hrest ih =>
      rcases List.mem_cons.mp hcandidate with rfl | htail
      · exact Or.inl ⟨_, _, _, hprovenance, hfind,
          hinput, houtput⟩
      · exact ih htail
  | nonrecursor Hnode Hrest ih =>
      rcases List.mem_cons.mp hcandidate with rfl | htail
      · exact Or.inr Hnode
      · exact ih htail

/-- The literal node fold entails the atomic-provenance interface used by
the structural typing and guardedness developments. -/
theorem NestedRestorationNodeEvidence.atomicProvenance
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    (H : NestedRestorationNodeEvidence sourceRecursors restoredRecursors
      plan.nodes) :
    plan.AtomicProvenance sourceRecursors restoredRecursors where
  classify := H.classify

end VerifyInductive
end Lean4Lean
