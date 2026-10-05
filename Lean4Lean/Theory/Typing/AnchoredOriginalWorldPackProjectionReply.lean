import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionAssignedBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionReplyAssembly

/-! End-to-end selected reply assembly for the prior-projection/literal-sort
field branch. Major R and paired major F are real proper-original calls;
assigned comparison and both selected frames are constructed internally. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private major_below from_both from_right from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall relabel recordControlled from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem ProjectionHead.packProjectionReplyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    (leftDisplay : outerLeft.fieldType = .proj name prior leftMajor)
    (rightDisplay : outerRight.fieldType = .proj name prior rightMajor)
    (innerLeft : ProjectionHead (outerLeft.field.cast leftDisplay rfl))
    (innerRight : ProjectionHead (outerRight.field.cast rightDisplay rfl))
    (leftLiteral : innerLeft.fieldType = .sort leftLevel)
    (rightLiteral : innerRight.fieldType = .sort rightLevel)
    (levels : leftLevel ≈ rightLevel)
    (leftMajorEq : leftMajor = outerLeft.sourceMajor)
    (rightMajorEq : rightMajor = outerRight.sourceMajor)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftProvenance : EndpointProvenance leftContext left)
    (rightProvenance : EndpointProvenance rightContext right)
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
    (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals
      commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference leftGraph (.right innerLeft.major) rfl)
      leftControls leftWorld frontier leftFrame)
    (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference rightGraph (.right innerRight.major) rfl)
      rightControls rightWorld frontier rightFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (prior, request) ∈ record.fields)
    (query : RichObs leftEnv env U registry target (.ref (.right innerLeft.major))
      leftLocals (leftRaw.comp commonLeft) (.singleton (n := n+1) (.record record)) footprint)
    (resources : footprint.Available leftAvailable)
    (ready : ControlledStoredQuery leftControls frontier (.observation query))
    (sourceField : RichCert leftEnv env U registry target innerLeft.field leftLocals
      (leftRaw.comp commonLeft) true support sourceFootprint)
    (sourceResources : sourceFootprint.Available leftAvailable)
    (sourceReady : ControlledStoredQuery leftControls frontier (.certificate sourceField))
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (innerLeft.fieldType.subst (leftRaw.comp commonLeft)))
    (sorted : request.input.HasType (.sort true))
    {outerRecord : RecordData (Profile n)} {outerRequest : DataRequest (Profile n)}
    (outerNameEq : outerRecord.family.name = name)
    (outerMember : (index, outerRequest) ∈ outerRecord.fields)
    (outerMajor : RichObs leftEnv env U registry target (.ref (.right outerLeft.major))
      leftLocals (leftRaw.comp commonLeft) (.singleton (n := n+1) (.record outerRecord)) outerFootprint)
    (outerResources : outerFootprint.Available leftAvailable)
    (outerReady : ControlledStoredQuery leftControls frontier (.observation outerMajor))
    (outerTyped : outerRequest.input.HasType request.input)
    (outerAlignment : DomainChain env U registry target outerRequest.input outerRequest.domain
      (outerLeft.fieldType.subst (leftRaw.comp commonLeft)))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (ProjectionHead.worldReplyDisplay outerRight rightContext rightProvenance rightGraph)
        commonLeft commonRight outerRequest.input (environmentCost rightEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) rightControls rightWorld frontier reply) := by
  obtain ⟨fieldSelected, fieldData, fieldAnswer, ⟨fieldReady⟩⟩ :=
    ProjectionHead.packAssignedBridgeWorld outerLeft outerRight leftDisplay rightDisplay innerLeft innerRight
      leftLiteral rightLiteral levels leftMajorEq rightMajorEq leftProvenance rightProvenance
      leftGraph rightGraph displayedEq leftControls rightControls sameCutoff sameFuel
      leftWorld rightWorld frontier paid leftFrame leftData rightFrame rightData
      henv hscoped formed nameEq member query resources ready sourceField sourceResources sourceReady
      typed alignment sorted bank unary
  have leftMajorBelow := major_below outerLeft leftControls leftWorld .expressionReindex .assignedComparison
  have rightMajorBelow := major_below outerRight rightControls rightWorld .expressionReindex .assignedComparison
  obtain ⟨majorSmaller, majorPaid⟩ := inheritedCall frontier
    (from_both leftMajorBelow rightMajorBelow) paid (by
      intro call present
      rcases List.mem_cons.mp present with rfl | present
      · exact ⟨_, List.mem_cons_self, leftMajorBelow⟩
      · cases List.mem_singleton.mp present
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rightMajorBelow⟩)
  let majorDisplay := OriginalNestedDisplay.recordBridgeReference rightGraph (.right outerRight.major) displayedEq
  obtain ⟨majorSelected, ⟨majorData⟩⟩ := (bank _ majorSmaller).observation base caps
    (OriginalNestedDisplay.recordBridgeReference leftGraph (.right outerLeft.major) rfl)
    majorDisplay commonLeft commonRight leftControls rightControls sameCutoff sameFuel
    leftWorld rightWorld frontier rfl majorPaid
    leftFrame (relabel leftData) rightFrame (relabel rightData)
    outerMajor outerResources outerReady
  obtain ⟨majorFootprint, majorQuery, majorResources, ⟨majorReady⟩⟩ :=
    recordControlled henv majorSelected.answer.reply.query majorData.query
  have fundamentalBelow := major_below outerRight rightControls rightWorld .fundamental .assignedComparison
  obtain ⟨fundamentalSmaller, fundamentalPaid⟩ := inheritedCall frontier
    (from_right (calls := [originalCallWorld rightControls .fundamental
      (.ref (.right outerRight.major)) rightWorld]) (by
        intro call present
        cases List.mem_singleton.mp present
        exact fundamentalBelow)) paid (by
      intro call present
      cases List.mem_singleton.mp present
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fundamentalBelow⟩)
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated majorSelected.answer.reply.realization.frame
    majorData.generation majorData.controlled majorData.replayable majorData.compatible majorData.hereditary
  obtain ⟨majorValue, _, _⟩ := (unary _ fundamentalSmaller).computational
    (.ref (.right outerRight.major)) (.ofLocation .here rightContext)
    rightControls majorSelected.answer.reply.realization.frame majorData.generation.environment rightWorld
    frontier (majorSelected.bounded rightControls.ordered) majorData.covered rfl fundamentalPaid
    frameData majorSelected.answer.reply.closed formed majorSelected.answer.reply.realization.substitutions
    majorQuery majorResources majorReady
  let majorFrameData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := ProjectionHead.worldReplyDisplay outerRight rightContext rightProvenance rightGraph)
      rightControls rightWorld frontier majorSelected.answer.reply.realization :=
    ⟨majorData.generation, majorData.replayable, majorData.controlled, majorData.compatible,
      majorSelected.answer.reply.closed, majorSelected.bounded rightControls.ordered,
      majorData.covered, majorData.hereditary⟩
  let fieldFrameData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := ProjectionHead.worldReplyDisplay outerRight rightContext rightProvenance rightGraph)
      rightControls rightWorld frontier fieldSelected.answer.reply.realization :=
    ⟨fieldData.generation, fieldData.replayable, fieldData.controlled, fieldData.compatible,
      fieldSelected.answer.reply.closed, fieldSelected.bounded rightControls.ordered,
      fieldData.covered, fieldData.hereditary⟩
  let innerObservation := RichObs.projection innerLeft nameEq member query sourceField typed alignment
  let originalField := RichCert.ofCast leftDisplay rfl (.observe innerObservation sorted)
  have outerPaid : Sponsored frontier [originalCallWorld rightControls .fundamental right rightWorld] := by
    intro child present
    cases List.mem_singleton.mp present
    obtain ⟨sponsor, present, lower⟩ := paid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have phase : WorldBelow strata.rules.length
        (originalCallWorld rightControls .fundamental right rightWorld)
        (originalCallWorld rightControls .assignedComparison right rightWorld) :=
      original_child (richComparison_to_fundamental _) _ _ _ _ _
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans phase lower⟩
  obtain ⟨reply, data, _, _, _, _⟩ := RichObs.projectionFromSelectedWorldReplies outerLeft outerRight
    rightContext rightProvenance rightGraph rightControls rightWorld frontier outerPaid
    majorSelected.answer.reply.realization fieldSelected.answer.reply.realization
    majorFrameData fieldFrameData henv hscoped formed outerNameEq outerMember originalField
    outerTyped outerAlignment majorSelected.answer.reply.query majorData.query
    majorValue.toRichSupportedValue fieldAnswer fieldReady
  exact ⟨reply, ⟨data⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
