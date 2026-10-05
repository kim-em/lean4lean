import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFields

/-! Raw prior-projection equality from the actual independent major originals.
Empty assigned comparisons obtain only the genuine family conversion paths;
the projection equality itself uses the original source formation and guard. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private major_below field_cost_lt from_left from_both from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall relabel from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem rawProjectionBridge
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    {argument : EndpointState leftEnv U leftSource (.proj name prior outerLeft.sourceMajor) A}
    (inner : ProjectionHead argument)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftSubst : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubst : Ctx.SubstEq env U target τ τ rightSource)
    (displayed : displayedLeft.subst σ = displayedRight.subst τ)
    (first : TypeConversion env U target
      ((mkApps (.const name inner.levels) (inner.parameters ++ inner.indices)).subst σ)
      ((mkApps (.const name outerLeft.levels) (outerLeft.parameters ++ outerLeft.indices)).subst σ))
    (middle : TypeConversion env U target
      ((mkApps (.const name outerLeft.levels) (outerLeft.parameters ++ outerLeft.indices)).subst σ)
      ((mkApps (.const name outerRight.levels) (outerRight.parameters ++ outerRight.indices)).subst τ)) :
    env.IsDefEq U target (.proj name prior (outerLeft.sourceMajor.subst σ))
      (.proj name prior (outerRight.sourceMajor.subst τ)) (inner.fieldType.subst σ) := by
  have innerRaw := (inner.major.forget.defeq.mono leftBelow).substDF henv leftSubst.wf formed leftSubst
  have leftRaw := (outerLeft.major.forget.defeq.mono leftBelow).substDF henv leftSubst.wf formed leftSubst
  have rightRaw := (outerRight.major.forget.defeq.mono rightBelow).substDF henv rightSubst.wf formed rightSubst
  have across := leftRaw.trans (middle.symm.cast (by simpa only [← displayed] using rightRaw.symm))
  have final := innerRaw.trans (first.symm.cast across)
  have field := (inner.field.sound.defeq.mono leftBelow).substDF henv leftSubst.wf formed leftSubst
  apply VEnv.IsDefEq.projDF (params := inner.parameters.map (·.subst σ))
    (indexArgs := inner.indices.map (·.subst σ)) (leftBelow.projections inner.registered) inner.levelsWF inner.levelCount
    (by simpa using inner.parameterCount) (by simpa using inner.indexCount)
    (inner.info.fieldType_subst_some inner.closed inner.selected) field
  · simpa only [subst_mkApps, subst_const, List.map_append] using innerRaw
  · simpa only [subst_mkApps, subst_const, List.map_append] using final
  · exact inner.closed
  · exact inner.relevance

/-- Both family paths are produced by actual proper-child C calls with empty
certificates. The statement assumes no query interpretation or family equality.
The prior argument is a genuine occurrence of the left outer field. -/
theorem ProjectionHead.priorRawBridgeWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    {argument : EndpointState leftEnv U leftSource (.proj name prior outerLeft.sourceMajor) A}
    (inner : ProjectionHead argument)
    (fieldRoot : EndpointRef leftEnv U leftSource outerLeft.fieldType (.sort outerLeft.fieldLevel))
    (fieldEq : outerLeft.field = .ref fieldRoot)
    (located : Located fieldRoot argument)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftGraph : OriginalCaptureMap (common := common) leftContext leftRaw)
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayedLeft.subst leftRaw = displayedRight.subst rightRaw)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison left leftWorld,
      originalCallWorld rightControls .assignedComparison right rightWorld])
    (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference leftGraph (.right inner.major) rfl)
      leftControls leftWorld frontier leftFrame)
    (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference rightGraph (.right outerRight.major) rfl)
      rightControls rightWorld frontier rightFrame)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    env.IsDefEq U target
      (.proj name prior (outerLeft.sourceMajor.subst (leftRaw.comp commonLeft)))
      (.proj name prior (outerRight.sourceMajor.subst (rightRaw.comp commonLeft)))
      (inner.fieldType.subst (leftRaw.comp commonLeft)) := by
  have innerWeight := (Located.projMajor (inner.route.locate located)).dependency_cost_le leftControls.ordered []
  have lowerWeight : (inner.major.dependencyOrigin leftControls.ordered).weight ≤
      (fieldRoot.dependencyOrigin leftControls.ordered).weight := by
    have lower : (inner.major.dependencyOrigin leftControls.ordered).weight ≤
        (Closure.close (inner.major.dependencyOrigin leftControls.ordered)
          ((Located.projMajor (inner.route.locate located)).dependencyEnvironment leftControls.ordered [])).cost :=
      Nat.le_mul_of_pos_right _ (by omega)
    apply Nat.le_trans lower
    simpa only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Closure.cost, environmentCost, Nat.add_zero, Nat.mul_one] using innerWeight
  have fieldCost := field_cost_lt outerLeft leftControls.ordered leftEnvironment
  rw [fieldEq] at fieldCost
  have innerBelow : WorldBelow strata.rules.length
      (originalCallWorld leftControls .assignedComparison (.ref (.right inner.major)) leftWorld)
      (originalCallWorld leftControls .assignedComparison left leftWorld) := by
    apply original_child (richSchedule_strict ?_ _ _) _ _ _ _ _
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ lowerWeight) fieldCost
  have leftMajor := major_below outerLeft leftControls leftWorld
  have rightMajor := major_below outerRight rightControls rightWorld
  have firstSmaller := from_left (other := originalCallWorld rightControls .assignedComparison right rightWorld) (calls := [
    originalCallWorld leftControls .assignedComparison (.ref (.right inner.major)) leftWorld,
    originalCallWorld leftControls .assignedComparison (.ref (.left outerLeft.major)) leftWorld]) (by
      intro call member
      rcases List.mem_cons.mp member with rfl | member
      · exact innerBelow
      · cases List.mem_singleton.mp member; exact leftMajor _ _)
  obtain ⟨firstFunded,firstPaid⟩ := inheritedCall frontier firstSmaller paid (by
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self,innerBelow⟩
    · cases List.mem_singleton.mp member
      exact ⟨_,List.mem_cons_self,leftMajor _ _⟩)
  have middleSmaller := from_both (leftMajor .assignedComparison .assignedComparison) (rightMajor .assignedComparison .assignedComparison)
  obtain ⟨middleFunded,middlePaid⟩ := inheritedCall frontier middleSmaller paid (by
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_cons_self,leftMajor _ _⟩
    · cases List.mem_singleton.mp member
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),rightMajor _ _⟩)
  let firstLeft := OriginalNestedDisplay.recordBridgeReference leftGraph (.right inner.major) rfl
  let firstRight := OriginalNestedDisplay.recordBridgeReference leftGraph (.left outerLeft.major) rfl
  let middleLeft := OriginalNestedDisplay.recordBridgeReference leftGraph (.right outerLeft.major) rfl
  let middleRight := OriginalNestedDisplay.recordBridgeReference rightGraph (.right outerRight.major) displayedEq
  let seed {expr ty : VExpr} (node : EndpointState leftEnv U leftSource expr ty) :
      RichCert leftEnv env U registry target node.typeFormation.node leftLocals
        (leftRaw.comp commonLeft) true (Profile.empty (n := 0)) [] :=
    .legacy (.seed .empty (.empty (.sort true)))
  have seedReady {expr ty : VExpr} (node : EndpointState leftEnv U leftSource expr ty) :
      ControlledStoredQuery leftControls frontier (.certificate (seed node)) := {
    annotation := .legacy _ (.seed _ _ .empty)
    within := by
      intro control _
      simp only [seed, StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨first,⟨firstData⟩⟩ := (bank _ firstFunded).assigned base caps firstLeft firstRight
    commonLeft commonRight leftControls leftControls rfl rfl leftWorld leftWorld frontier rfl firstPaid
    leftFrame leftData leftFrame (relabel leftData) (seed _) (by intro _ _ member; cases member) (seedReady _)
  obtain ⟨middle,⟨middleData⟩⟩ := (bank _ middleFunded).assigned base caps middleLeft middleRight
    commonLeft commonRight leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier rfl middlePaid
    leftFrame (relabel leftData) rightFrame (relabel rightData) (seed _)
    (by intro _ _ member; cases member) (seedReady _)
  apply rawProjectionBridge outerLeft outerRight inner henv
    leftData.generation.erase.ambientGenerated.ambient.1.below
    rightData.generation.erase.ambientGenerated.ambient.1.below formed
    leftFrame.substitutions.left rightFrame.substitutions.left
  · simpa only [subst_subst] using congrArg (VExpr.subst · commonLeft) displayedEq
  · simpa only [firstLeft,firstRight,OriginalNestedDisplay.recordBridgeReference,subst_subst] using first.path
  · simpa only [middleLeft,middleRight,OriginalNestedDisplay.recordBridgeReference,subst_subst] using middle.path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
