import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiLevels
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiNeutral
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSortTransfer

/-! Native Pi assigned-type comparison uses exact domain/body comparison
calls in their actual generic frames, including the fresh neutral binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
  {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
  {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
  {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
  {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
  {rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
  {lu : u.WF U} {lv : v.WF U} {ru : u'.WF U} {rv : v'.WF U}
  (leftLocation : Located leftRoot (.pi lu lv (.ref leftDomain) leftBody))
  (rightLocation : Located rightRoot (.pi ru rv (.ref rightDomain) rightBody))
  (leftInitial : ContextDerivation leftEnv U leftRootSource)
  (rightInitial : ContextDerivation rightEnv U rightRootSource)
  (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
  (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
  (leftAnnotation : annotation = A.lift' leftMap)
  (rightAnnotation : annotation = C.lift' rightMap)
  (leftExpression : displayedBody = B.lift' leftMap.cons)
  (rightExpression : displayedBody = D.lift' rightMap.cons)
  (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
  (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)

theorem OriginalRichDisplayFrame.nativePiCoherence
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftFrame : OriginalRichDisplayFrame env registry target
      (leftLocation.piDisplayAs leftInitial leftInsertion leftAnnotation leftExpression)
      common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target
      (rightLocation.piDisplayAs rightInitial rightInsertion rightAnnotation rightExpression)
      common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed)
    (domainC :
      richSchedule .assignedComparison
        ((leftFrame.piDomain leftLocation leftInitial leftInsertion leftAnnotation leftExpression).cost lf +
         (rightFrame.piDomain rightLocation rightInitial rightInsertion rightAnnotation rightExpression).cost rf) <
      richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalRichDisplayCoherence
        (leftFrame.piDomain leftLocation leftInitial leftInsertion leftAnnotation leftExpression)
        (rightFrame.piDomain rightLocation rightInitial rightInsertion rightAnnotation rightExpression))
    (bodyC : ∀ (annotationType : env.IsType U target (annotation.subst common)),
      let leftChild := leftFrame.piNeutral leftLocation leftInitial leftInsertion leftAnnotation leftExpression
        henv leftBelow formed annotationType
      let rightChild := rightFrame.piNeutral rightLocation rightInitial rightInsertion rightAnnotation rightExpression
        henv rightBelow formed annotationType
      richSchedule .assignedComparison (leftChild.cost lf + rightChild.cost rf) <
        richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalRichDisplayCoherence leftChild rightChild) :
    OriginalRichDisplayCoherence leftFrame rightFrame := by
  have domainBound :
      (leftFrame.piDomain leftLocation leftInitial leftInsertion leftAnnotation leftExpression).cost lf +
      (rightFrame.piDomain rightLocation rightInitial rightInsertion rightAnnotation rightExpression).cost rf <
      leftFrame.cost lf + rightFrame.cost rf := by
    exact Nat.add_lt_add
      (binder_domain_cost (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] []
        (leftFrame.frame.dependencyEnvironment lf))
      (binder_domain_cost (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] []
        (rightFrame.frame.dependencyEnvironment rf))
  have domains := domainC (richSchedule_strict domainBound _ _)
  have domainLevels : u ≈ u' := domains.sortLevels formed rfl rfl
  have annotationType : env.IsType U target (annotation.subst common) := by
    rw [leftAnnotation, subst_lift']
    exact ⟨_, (leftDomain.sound.defeq.mono leftBelow).subst henv leftFrame.substitutions.left formed⟩
  have bodyBound :
      (leftFrame.piNeutral leftLocation leftInitial leftInsertion leftAnnotation leftExpression
        henv leftBelow formed annotationType).cost lf +
      (rightFrame.piNeutral rightLocation rightInitial rightInsertion rightAnnotation rightExpression
        henv rightBelow formed annotationType).cost rf <
      leftFrame.cost lf + rightFrame.cost rf := by
    simp only [OriginalRichDisplayFrame.cost, Located.piBodyDisplayAs,
      OriginalRichDisplayFrame.piNeutral_environment]
    exact Nat.add_lt_add (binder_body_cost (by simp) _) (binder_body_cost (by simp) _)
  have bodies := bodyC annotationType (richSchedule_strict bodyBound _ _)
  have bodyLevels : v ≈ v' := bodies.sortLevels ⟨formed, annotationType⟩ rfl rfl
  have levels := VLevel.imax_congr domainLevels bodyLevels
  exact {
    path := .single (.sortDF ⟨lu, lv⟩ ⟨ru, rv⟩ levels)
    queries := RichCodeTransfer.literalSort (leftLevel := .imax u v) (rightLevel := .imax u' v') henv hscoped formed leftClosed ⟨lu, lv⟩ ⟨ru, rv⟩ levels }

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
