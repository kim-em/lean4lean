import Lean4Lean.Verify.Inductive.Nested.EquationRestorationGuardedAtomic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

@[simp] theorem VExpr.bvarHead?_app (fn arg : VExpr) :
    (VExpr.app fn arg).bvarHead? = fn.bvarHead? := by
  unfold VExpr.bvarHead?
  rw [VExpr.getAppFnArgs_app]

/-- Every finite restoration hit has a constant-headed abstract source.
For recursor hits this follows from exact endpoint translation; for generated
family/constructor hits it is retained at their provenance boundary. -/
theorem NestedRestorationPlan.AtomicProvenance.nodeSourceNotBVarHead
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors) :
    ∀ node ∈ plan.nodes, node.source.bvarHead? = none := by
  intro node hnode
  rcases H.classify node hnode with
    ⟨oldName, newName, levels, _hrecursor, _hfind, hinput, houtput⟩ |
      Hnonrecursor
  · have Hsource := node.sourceTranslation
    have Htarget := node.targetTranslation
    rw [hinput] at Hsource
    rw [houtput] at Htarget
    rcases translatedRecursorEndpoints Hsource.toTrExprS Htarget.toTrExprS with
      ⟨abstractLevels, hsource, _htarget⟩
    rw [hsource]
    rfl
  · exact Hnonrecursor.sourceNotBVarHead

/-- Every finite production hit retains a constant-headed abstract source.
This stronger form is what excludes atomic stopping at generated lambda and
forall prefixes while extracting recursive-result components. -/
theorem NestedRestorationPlan.AtomicProvenance.nodeSourceConstHead
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors) :
    ∀ node ∈ plan.nodes, ∃ name levels,
      node.source.getAppFnArgs.1 = .const name levels := by
  intro node hnode
  rcases H.classify node hnode with
    ⟨oldName, newName, levels, _hrecursor, _hfind, hinput, houtput⟩ |
      Hnonrecursor
  · have Hsource := node.sourceTranslation
    have Htarget := node.targetTranslation
    rw [hinput] at Hsource
    rw [houtput] at Htarget
    rcases translatedRecursorEndpoints Hsource.toTrExprS Htarget.toTrExprS with
      ⟨abstractLevels, hsource, _htarget⟩
    exact ⟨oldName, abstractLevels, by rw [hsource]; rfl⟩
  · cases Hnonrecursor.nonrecursor with
    | family hfind hhead hhit | constructor hfind hhead hhit =>
        rcases checkPositivityStep.TrExprS.constAppSpine
            node.sourceTranslation.toTrExprS hhead with
          ⟨levels, args, hspine, _hlevels, _hargs⟩
        exact ⟨_, levels, congrArg Prod.fst hspine⟩

/-- A non-recursor finite node cannot have an old recursor as its abstract
application head. -/
theorem NestedRestorationPlan.AtomicProvenance.nonrecursorHeadNotSource
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hnonrecursor : GeneratedNonrecursorHitFreeness node sourceRecursors
      restoredRecursors) (hsource : node.source.getAppFnArgs.1 =
        .const sourceRecursor levels)
    (hmem : sourceRecursor ∈ sourceRecursors) : False := by
  cases Hnonrecursor.nonrecursor with
  | family hfind hconcreteHead hhit =>
      rcases checkPositivityStep.TrExprS.constAppSpine
          node.sourceTranslation.toTrExprS hconcreteHead with
        ⟨abstractLevels, args, habstractHead, _hlevels, _hargs⟩
      have hnames := VExpr.const.inj
        ((congrArg Prod.fst habstractHead).symm.trans hsource) |>.1
      apply Hnonrecursor.sourceHeadNotRecursor _ _ hconcreteHead
      rwa [hnames]
  | constructor hfind hconcreteHead hhit =>
      rcases checkPositivityStep.TrExprS.constAppSpine
          node.sourceTranslation.toTrExprS hconcreteHead with
        ⟨abstractLevels, args, habstractHead, _hlevels, _hargs⟩
      have hnames := VExpr.const.inj
        ((congrArg Prod.fst habstractHead).symm.trans hsource) |>.1
      apply Hnonrecursor.sourceHeadNotRecursor _ _ hconcreteHead
      rwa [hnames]

/-- A finite plan cannot stop structurally at a bound-variable-headed
application. -/
theorem NestedRestorationPlan.AtomicProvenance.not_relates_of_bvarHead
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (hhead : source.bvarHead? = some field) :
    ¬ plan.Relates source target := by
  rintro ⟨node, hnode, hsource, _htarget⟩
  have hnone := H.nodeSourceNotBVarHead node hnode
  rw [hsource] at hnone
  rw [hhead] at hnone
  cases hnone

/-- Structural restoration preserves the bound-variable application head.
Atomic stopping is excluded by the exact finite provenance plan; restoration
inside application arguments is irrelevant to the head. -/
theorem NestedRestorationPlan.AtomicProvenance.bvarHead_eq_some
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates source target)
    (hhead : source.bvarHead? = some field) :
    target.bvarHead? = some field := by
  induction Hrest with
  | hit hhit =>
      exact False.elim (H.not_relates_of_bvarHead hhead hhit)
  | leaf => exact hhead
  | bvar => exact hhead
  | sort | const | lam | forallE =>
      change none = some field at hhead
      cases hhead
  | app _ _ ihfn _ =>
      rw [VExpr.bvarHead?_app] at hhead ⊢
      exact ihfn hhead
  | projection _ _ sourceNotBVarHead _ _ =>
      rw [sourceNotBVarHead] at hhead
      cases hhead

/-- In particular, a designated constructor-field application remains a
field application at the same binder depth after restoration. -/
theorem NestedRestorationPlan.AtomicProvenance.isFieldApp
    (H : NestedRestorationPlan.AtomicProvenance plan sourceRecursors
      restoredRecursors)
    (Hrest : VExprRestoration plan.Relates source target)
    (hfield : source.IsFieldApp fieldVars depth) :
    target.IsFieldApp fieldVars depth := by
  rcases hfield with ⟨field, hfieldMem, args, hspine⟩
  have hsourceHead : source.bvarHead? = some (field + depth) := by
    unfold VExpr.bvarHead?
    rw [hspine]
  have htargetHead := H.bvarHead_eq_some Hrest hsourceHead
  rcases VExpr.bvarHead?_eq_some htargetHead with
    ⟨targetArgs, htargetSpine⟩
  exact ⟨field, hfieldMem, targetArgs, htargetSpine⟩

end VerifyInductive
end Lean4Lean
