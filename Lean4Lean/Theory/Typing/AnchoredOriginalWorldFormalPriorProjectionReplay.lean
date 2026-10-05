import Lean4Lean.Theory.Typing.AnchoredOriginalFormalPriorProjectionFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyOwnCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open private field_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

private theorem locatedField_worldBelow
    (controls : OriginalWorldControls strata sourceEnv)
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    {node : EndpointState sourceEnv U source expression type}
    (located : Located field node)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase node captured)
      (originalCallWorld controls parentPhase outer captured) := by
  have bound := located.dependency_cost_le controls.ordered []
  have floor : (node.dependencyOrigin controls.ordered).weight ≤
      (Closure.close (node.dependencyOrigin controls.ordered)
        (located.dependencyEnvironment controls.ordered [])).cost :=
    Nat.le_mul_of_pos_right _ (by omega)
  have weight : (node.dependencyOrigin controls.ordered).weight ≤
      (head.field.dependencyOrigin controls.ordered).weight := by
    rw [fieldEq]
    exact Nat.le_trans floor (by simpa only [Closure.cost, environmentCost,
      Nat.add_zero, Nat.mul_one, EndpointState.dependencyOrigin] using bound)
  exact original_child (richSchedule_strict
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (1 + environmentCost environment) weight)
      (field_cost_lt head controls.ordered environment)) phase parentPhase) _ _ _ _ _

noncomputable def formalPriorProjectionDisplay
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
    {root : EndpointRef env U rootSource rootExpression rootType}
    (initial : ContextDerivation env U rootSource)
    (located : Located root
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref field) major closed relevance))
    (graph : OriginalCaptureMap (common := common) (located.contextDerivation initial) raw) :
    OriginalNestedDisplay U common ((VExpr.proj name 0 expression).subst raw) (fieldType.subst raw) := {
  sourceEnv := env
  source := mkApps (.const name levels) (parameters ++ indices) :: source
  sourceExpression := .proj name 0 (.bvar 0)
  sourceType := fieldType.lift
  context := .cons (located.contextDerivation initial) major.familyFormationRef.reference
  node := (formalFirstProjectionOriginal ordered registered levelsWF levelCount parameterCount indexCount
    selected fieldWF field major closed relevance).expose.2
  provenance := .ofLocation (root := .right (formalFirstProjectionOriginal ordered registered levelsWF
    levelCount parameterCount indexCount selected fieldWF field major closed relevance))
    (.expose .here) (.cons (located.contextDerivation initial) major.familyFormationRef.reference)
  raw := raw.cons (expression.subst raw)
  graph := .capture graph major.familyFormationRef.reference graph (.ref (.right major))
    (.ofLocation (.projMajor located) initial)
  expression_eq := rfl
  type_eq := lift_subst_cons.symm }

noncomputable def formalPriorMajorProvenance
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
    (initial : ContextDerivation env U source) :
    EndpointProvenance (.cons initial major.familyFormationRef.reference)
      (.ref (.right (formalMajorVariableOriginal ordered major))) :=
  .ofLocation (root := .right (formalFirstProjectionOriginal ordered registered levelsWF
    levelCount parameterCount indexCount selected fieldWF field major closed relevance))
    (.projMajor (.expose .here)) (.cons initial major.familyFormationRef.reference)

theorem captureAndReplayPriorProjectionWorld
    {ambient : VEnv} {strata : EquationStratification ambient}
    {P : VEnv → Prop} {base : OriginalCaptureBase ambient U registry target} {caps : CaptureCaps}
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
    (initial : ContextDerivation env U source)
    (located : Located fieldRoot
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref field) major closed relevance))
    (graph : OriginalCaptureMap (common := common) (located.contextDerivation initial) raw)
    (frame : OriginalCaptureRealization graph ambient registry target locals commonLeft commonRight available)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length)) (other : World strata.rules.length)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.ofOccurrence initial located graph)
      controls baseline frontier frame)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (query : RichObs env ambient U registry target
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref field) major closed relevance) locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (henv : ambient.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (ambient.IsType U))
    (bank : WorldBoundedCallBank ambient U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    let destination := formalPriorProjectionDisplay controls.ordered registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed relevance initial located graph
    let reserve := ownCaptureWorldEnvironment controls major.familyFormationRef.reference
      (.ref (.right major)) data.generation.environment
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps destination commonLeft commonRight profile
        (environmentCost reserve.closures),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls reserve frontier reply) := by
  let destination := formalPriorProjectionDisplay controls.ordered registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed relevance initial located graph
  let reserve := ownCaptureWorldEnvironment controls major.familyFormationRef.reference
    (.ref (.right major)) data.generation.environment
  let variableNode := EndpointState.ref (.right (formalMajorVariableOriginal controls.ordered major))
  let variableProvenance := formalPriorMajorProvenance controls.ordered registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed relevance
    (located.contextDerivation initial)
  obtain ⟨empty, ⟨emptyData⟩⟩ := emptyOwnCaptureWorld initial (.ref (.right major)) (.projMajor located)
    major.familyFormationRef.reference controls frame data.generation frontier data.controlled
    data.replayable data.compatible data.hereditary variableNode variableProvenance henv hscoped formed
  let formalData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := destination) controls reserve frontier empty.answer.reply.realization := {
    generation := emptyData.generation
    replayable := emptyData.replayable
    controlled := emptyData.controlled
    compatible := emptyData.compatible
    closed := empty.answer.reply.closed
    capacity := empty.bounded controls.ordered
    covered := emptyData.covered
    hereditary := emptyData.hereditary }
  have leftBelow := originalCallWorld_retargetBelow controls outer .assignedComparison
    data.generation.environment baseline data.capacity data.covered
    (locatedField_worldBelow controls head fieldRoot fieldEq located data.generation.environment
      .expressionReindex .assignedComparison)
  have rightBelow := originalCallWorld_retargetBelow controls outer .assignedComparison
    data.generation.environment baseline data.capacity data.covered
    (formalFirstProjection_worldBelow_outer controls registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed relevance two noIndices head outerTwo fieldRoot fieldEq located
      data.generation.environment .expressionReindex .assignedComparison)
  let leftWorld := originalCallWorld controls .expressionReindex
    (OriginalNestedDisplay.ofOccurrence initial located graph).node data.generation.environment
  let rightWorld := originalCallWorld controls .expressionReindex destination.node reserve
  let parent := originalCallWorld controls .assignedComparison outer baseline
  have lower : ∀ child ∈ [leftWorld, rightWorld], WorldBelow strata.rules.length child parent := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact leftBelow
    · cases List.mem_singleton.mp member
      exact rightBelow
  obtain ⟨smaller, sponsored⟩ := inheritedCall frontier (from_right lower) paid (by
    intro child member
    exact ⟨parent, by simp [parent], lower child member⟩)
  let sourceData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.ofOccurrence initial located graph)
      controls data.generation.environment frontier frame := {
    generation := data.generation
    replayable := data.replayable
    controlled := data.controlled
    compatible := data.compatible
    closed := data.closed
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.hereditary }
  exact bank.observation _ smaller base caps (OriginalNestedDisplay.ofOccurrence initial located graph)
    destination commonLeft commonRight controls controls rfl rfl data.generation.environment reserve frontier
    rfl sponsored frame sourceData empty.answer.reply.realization formalData query resources ready

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
