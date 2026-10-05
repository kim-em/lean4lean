import Lean4Lean.Theory.Typing.AnchoredOriginalFormalPriorProjectionBudget
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureCalls

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem formalFirstProjection_captured_below_outer
    (ordered : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters 0 sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (two : info.nparams = 2) (noIndices : info.nindices = 0)
    {outer : EndpointState env U source (.proj outerName outerIndex outerMajor) outerAssigned}
    (head : ProjectionHead outer)
    (outerTwo : head.info.nparams + head.info.nindices = 2)
    (fieldRoot : EndpointRef env U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref fieldRoot)
    (located : Located fieldRoot
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref field) major closed relevance))
    (environment : List Closure) :
    (Closure.close
      ((formalFirstProjectionOriginal ordered registered levelsWF levelCount parameterCount indexCount
        selected fieldWF field major closed relevance).expose.2.dependencyOrigin ordered)
      (.bundle (.close (major.dependencyOrigin ordered) environment)
        (.close (major.familyFormationRef.reference.dependencyOrigin ordered) environment) :: environment)).cost <
    (Closure.close (outer.dependencyOrigin ordered) environment).cost := by
  let prior := EndpointState.proj registered levelsWF levelCount parameterCount indexCount selected
    fieldWF (.ref field) major closed relevance
  let formal := (formalFirstProjectionOriginal ordered registered levelsWF levelCount parameterCount indexCount
    selected fieldWF field major closed relevance).expose.2
  have formalBound := formalFirstProjectionOriginal_exposed_weight ordered registered levelsWF
    levelCount parameterCount indexCount selected fieldWF field major closed relevance two noIndices
  have formationBound := major.familyFormationRef.dependencyWeight_le ordered
  have locatedCost := located.dependency_cost_le ordered []
  have lower : (prior.dependencyOrigin ordered).weight ≤
      (Closure.close (prior.dependencyOrigin ordered) (located.dependencyEnvironment ordered [])).cost :=
    Nat.le_mul_of_pos_right _ (by omega)
  have priorBound : (prior.dependencyOrigin ordered).weight ≤ (head.field.dependencyOrigin ordered).weight := by
    rw [fieldEq]
    exact Nat.le_trans lower (by simpa only [prior, EndpointState.dependencyOrigin, Closure.cost, environmentCost, Nat.add_zero, Nat.mul_one] using locatedCost)
  have majorBound : (major.dependencyOrigin ordered).weight < (prior.dependencyOrigin ordered).weight := by
    apply Origin.rule_child
    simp [prior, EndpointState.dependencyOrigin]
  let header := selectOriginalHeader ordered (ordered.projectionConstructor registered) levelsWF
  let roots := projectionParameterDependencies ordered registered levelsWF
  have largeReserve := routedParameterDependencyReserve_two_large
    (equalities := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
    (header.original.dependencyOrigin header.ordered).weight_pos
    (field.dependencyOrigin ordered).weight_pos (major.dependencyOrigin ordered).weight_pos
  have largePrior : 32 ≤ (prior.dependencyOrigin ordered).weight := by
    dsimp only [header, roots] at largeReserve
    simp only [prior, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin,
      Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      reserveOrigin_weight, two, noIndices, Nat.add_zero, Nat.max_self] at *
    omega
  have paid := formalPriorProjection_capture_cost
    (formal.dependencyOrigin ordered) (prior.dependencyOrigin ordered)
    (major.dependencyOrigin ordered) (major.familyFormationRef.reference.dependencyOrigin ordered)
    environment formalBound formationBound priorBound
    (show (major.dependencyOrigin ordered).weight ≤
      (head.field.dependencyOrigin ordered).weight + (head.major.dependencyOrigin ordered).weight by omega)
    (show 32 ≤ (head.field.dependencyOrigin ordered).weight +
      (head.major.dependencyOrigin ordered).weight by omega)
  have reserveBelow : projectionFamilyReserve 2 (head.field.dependencyOrigin ordered).weight
      (head.major.dependencyOrigin ordered).weight <
      ((projectionNatural head).dependencyOrigin ordered).weight := by
    simp only [projectionNatural, EndpointState.dependencyOrigin, Origin.weight,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight]
    unfold projectionDependencyReserve
    rw [outerTwo]
    omega
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt paid
    (Nat.mul_lt_mul_of_pos_right reserveBelow (show 0 < 1 + environmentCost environment by omega)))
    (head.route.dependency_cost_le ordered environment)

theorem captureNode_worldBelow_of_cost
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (node : EndpointState sourceEnv U (A :: source) expression assigned)
    (outer : EndpointState sourceEnv U source outerExpression outerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase)
    (cost : (Closure.close (node.dependencyOrigin controls.ordered)
      (.bundle (.close (argument.dependencyOrigin controls.ordered) environment)
        (.close (domain.dependencyOrigin controls.ordered) environment) :: environment)).cost <
      (Closure.close (outer.dependencyOrigin controls.ordered) environment).cost) :
    WorldBelow strata.rules.length
      (originalCallWorld controls phase node (ownCaptureWorldEnvironment controls domain argument captured))
      (originalCallWorld controls parentPhase outer captured) := by
  have bundled := capturedVariable_bundle_lt (node.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (domain.dependencyOrigin controls.ordered) environment
  have bundleBelow : WorldBelow strata.rules.length (captureBundleWorld controls domain argument captured)
      (originalCallWorld controls parentPhase outer captured) := by
    apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans _ (Covered.refl _)
    exact EquationControlMeasure.scheduleDecrease
      (richSchedule_strict (Nat.lt_trans bundled cost) .expressionReindex parentPhase) _ _ _ _
  have ownerBelow := EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
    (captureBundleWorld_owner_below controls domain argument captured captured
      (Nat.le_refl _) (Covered.refl _) .expressionReindex) bundleBelow
  have domainBelow := EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
    (captureBundleWorld_domain_below controls domain argument captured captured
      (Nat.le_refl _) (Covered.refl _) .fundamental) bundleBelow
  apply Below.root
    (EquationControlMeasure.scheduleDecrease (richSchedule_strict (by
      simpa only [ownCaptureWorldEnvironment, Closure.cost, environmentCost,
        List.cons_append, List.nil_append, ← Nat.max_assoc, Nat.max_self] using cost) phase parentPhase) _ _ _ _)
  intro child member
  change child ∈ [captureBundleWorld controls domain argument captured] ++
    [originalCallWorld controls .expressionReindex argument captured] ++
    [originalCallWorld controls .fundamental (.ref domain) captured] ++
    ([originalCallWorld controls .expressionReindex argument captured] ++
      [originalCallWorld controls .fundamental (.ref domain) captured]) ++ captured.worlds at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (((rfl | rfl) | rfl) | rfl | rfl) | member
  · exact bundleBelow
  · exact ownerBelow
  · exact domainBelow
  · exact ownerBelow
  · exact domainBelow
  · exact Below.child member

theorem formalFirstProjection_worldBelow_outer
    (controls : OriginalWorldControls strata env)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters 0 sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (two : info.nparams = 2) (noIndices : info.nindices = 0)
    {outer : EndpointState env U source (.proj outerName outerIndex outerMajor) outerAssigned}
    (head : ProjectionHead outer)
    (outerTwo : head.info.nparams + head.info.nindices = 2)
    (fieldRoot : EndpointRef env U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref fieldRoot)
    (located : Located fieldRoot
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref field) major closed relevance))
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length
      (originalCallWorld controls phase
        (formalFirstProjectionOriginal controls.ordered registered levelsWF levelCount parameterCount indexCount
          selected fieldWF field major closed relevance).expose.2
        (ownCaptureWorldEnvironment controls major.familyFormationRef.reference (.ref (.right major)) captured))
      (originalCallWorld controls parentPhase outer captured) := by
  apply captureNode_worldBelow_of_cost
  exact formalFirstProjection_captured_below_outer controls.ordered registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field major closed relevance two noIndices
    head outerTwo fieldRoot fieldEq located environment

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
