import Lean4Lean.Verify.Inductive.Nested.EquationRestorationLambdas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The executable/abstract alignment of a generated recursor application
restores exactly its recursor head and traverses its arguments pointwise.
Family and constructor nodes cannot stop at an application prefix because
their retained source head is disjoint from the old recursor names.  At the
literal head, the executable `restoreNestedNode` trace decides whether the
finite map renames the constant or leaves it unchanged. -/
theorem NestedRestorationPlan.AtomicProvenance.recursorSpineAlignment
    {plan : NestedRestorationPlan result prodEnv params auxRec sourceEnv
      targetEnv Us sourceContext targetContext}
    {input output : Expr} {source target : VExpr}
    {Hreplace : ExprReplacement
      (result.restoreNestedNode prodEnv params auxRec) input output}
    {Hrest : VExprRestoration plan.restoreNode source target}
    (Hatomic : plan.AtomicProvenance sourceRecursors targetRecursors)
    (Halign : ExprRestorationAlignment
      (result.restoreNestedNode prodEnv params auxRec) plan.restoreNode
      Hreplace Hrest)
    (hspine : source.getAppFnArgs =
      (.const sourceRecursor levels, sourceArgs))
    (hsourceMem : sourceRecursor ∈ sourceRecursors) :
    ∃ targetArgs,
      target = VExpr.mkApps
        (.const (auxRec.getD sourceRecursor sourceRecursor) levels)
        targetArgs ∧
      List.Forall₂ (VExprRestoration plan.restoreNode)
        sourceArgs targetArgs := by
  induction Halign generalizing sourceRecursor levels sourceArgs with
  | @hit hitSource hitTarget nodeSourceEnv nodeTargetEnv nodeUs
      nodeSourceContext nodeTargetContext hitInput hitOutput Hhit Hinterp =>
      rcases plan.exists_node_of_restoreNode_eq_some Hinterp.abstractHit with
        ⟨node, hnode, hnodeSource, hnodeTarget⟩
      rcases Hatomic.classify node hnode with
        ⟨oldName, newName, concreteLevels, _hrecursor, hfind,
          hinput, houtput⟩ |
          Hnonrecursor
      · have Hsource := node.sourceTranslation
        have Htarget := node.targetTranslation
        rw [hinput] at Hsource
        rw [houtput] at Htarget
        rcases translatedRecursorEndpoints Hsource Htarget with
          ⟨abstractLevels, hsource, htarget⟩
        have hsource' : hitSource = VExpr.const oldName abstractLevels :=
          hnodeSource.symm.trans hsource
        rw [hsource'] at hspine
        simp only [VExpr.getAppFnArgs_const, Prod.mk.injEq] at hspine
        rcases hspine with ⟨hhead, hargs⟩
        have hname := (VExpr.const.inj hhead).1
        have hlevels := (VExpr.const.inj hhead).2
        subst sourceRecursor
        subst levels
        subst sourceArgs
        have hgetD : auxRec.getD oldName oldName = newName := by
          change Std.TreeMap.getD
            (show Std.TreeMap Name Name Name.quickCmp from auxRec)
              oldName oldName = newName
          change (show Std.TreeMap Name Name Name.quickCmp from auxRec)[oldName]? =
            some newName at hfind
          rw [Std.TreeMap.getD_eq_getD_getElem?, hfind]
          rfl
        refine ⟨[], ?_, .nil⟩
        change hitTarget = VExpr.const (auxRec.getD oldName oldName)
          abstractLevels
        simpa only [hgetD] using hnodeTarget.symm.trans htarget
      · have hnodeHead : node.source.getAppFnArgs.1 =
            .const sourceRecursor levels := by
          rw [hnodeSource]
          exact congrArg Prod.fst hspine
        exact False.elim
          (Hatomic.nonrecursorHeadNotSource Hnonrecursor hnodeHead
            hsourceMem)
  | @const concreteName concreteLevels abstractLevels hconcrete habstract =>
      simp only [VExpr.getAppFnArgs_const, Prod.mk.injEq] at hspine
      rcases hspine with ⟨hhead, hargs⟩
      have hname := (VExpr.const.inj hhead).1
      have hlevels := (VExpr.const.inj hhead).2
      subst sourceRecursor
      subst levels
      subst sourceArgs
      have hfind : auxRec.find? concreteName = none := by
        cases hlookup : auxRec.find? concreteName with
        | none => rfl
        | some restoredName =>
            simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
              hlookup] at hconcrete
      have hgetD : auxRec.getD concreteName concreteName = concreteName := by
        change Std.TreeMap.getD
          (show Std.TreeMap Name Name Name.quickCmp from auxRec)
            concreteName concreteName = concreteName
        change (show Std.TreeMap Name Name Name.quickCmp from auxRec)[concreteName]? =
          none at hfind
        rw [Std.TreeMap.getD_eq_getD_getElem?, hfind]
        rfl
      exact ⟨[], by simp [hgetD, VExpr.mkApps], .nil⟩
  | @app fn arg sourceFn sourceArg concreteTargetFn concreteFn targetFn
      abstractFn concreteTargetArg concreteArg targetArg abstractArg
      hconcrete habstract hfn harg ihfn iharg =>
      simp only [VExpr.getAppFnArgs_app] at hspine
      have hhead := congrArg Prod.fst hspine
      have hargs := congrArg Prod.snd hspine
      simp only [Prod.fst] at hhead
      simp only [Prod.snd] at hargs
      have hfnSpine : sourceFn.getAppFnArgs =
          (.const sourceRecursor levels, sourceFn.getAppFnArgs.2) := by
        apply Prod.ext
        · exact hhead
        · rfl
      rcases ihfn (sourceRecursor := sourceRecursor)
          (levels := levels) (sourceArgs := sourceFn.getAppFnArgs.2)
          hfnSpine hsourceMem with
        ⟨priorTargetArgs, htargetFn, Haligned⟩
      refine ⟨priorTargetArgs ++ [targetArg], ?_, ?_⟩
      · rw [htargetFn]
        simpa [VExpr.mkApps] using
          (VExpr.mkApps_append
            (VExpr.const (auxRec.getD sourceRecursor sourceRecursor) levels)
            priorTargetArgs [targetArg]).symm
      · rw [← hargs]
        exact Lean4Lean.VerifyInductive.List.Forall₂.append' Haligned
          (.cons abstractArg .nil)
  | @bvar index hconcrete habstract =>
      change (VExpr.bvar index, []) =
        (.const sourceRecursor levels, sourceArgs) at hspine
      cases hspine
  | @sort concreteLevel abstractLevel hconcrete habstract =>
      change (VExpr.sort abstractLevel, []) =
        (.const sourceRecursor levels, sourceArgs) at hspine
      cases hspine
  | @lam name domain body bi sourceDomain sourceBody concreteTargetDomain
      concreteDomain targetDomain abstractDomain concreteTargetBody
      concreteBody targetBody abstractBody hconcrete habstract hdomain hbody
      ihdomain ihbody =>
      change (VExpr.lam sourceDomain sourceBody, []) =
        (.const sourceRecursor levels, sourceArgs) at hspine
      cases hspine
  | @forallE name domain body bi sourceDomain sourceBody
      concreteTargetDomain concreteDomain targetDomain abstractDomain
      concreteTargetBody concreteBody targetBody abstractBody hconcrete
      habstract hdomain hbody ihdomain ihbody =>
      change (VExpr.forallE sourceDomain sourceBody, []) =
        (.const sourceRecursor levels, sourceArgs) at hspine
      cases hspine

end VerifyInductive
end Lean4Lean
