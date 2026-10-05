import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLiteralSort

/-! Productive prior-projection assigned comparison. The incoming inner field
code is interpreted by its actual smaller F call; the five-leg major bridge
then supplies the selected destination observer and the raw field path. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private field_cost_lt inner_major_below from_left from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private def fieldProvenance
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (provenance : EndpointProvenance context node) :
    EndpointProvenance context head.field where
  rootSource := provenance.rootSource
  rootExpression := provenance.rootExpression
  rootType := provenance.rootType
  root := provenance.root
  initial := provenance.initial
  location := .projField (head.route.locate provenance.location)
  context_eq := by
    change context = (head.route.locate provenance.location).contextDerivation provenance.initial
    rw [PrefixRoute.locate_contextDerivation]
    exact provenance.context_eq

private def castProvenance
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = next) (provenance : EndpointProvenance context node) :
    EndpointProvenance context (node.cast equal rfl) := by
  cases equal
  exact provenance

private theorem innerFieldBelow
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (outer : ProjectionHead node) (display : outer.fieldType = .proj name prior value)
    (inner : ProjectionHead (outer.field.cast display rfl))
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) :
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental inner.field captured)
      (originalCallWorld controls .assignedComparison node captured) := by
  have small := field_cost_lt inner controls.ordered environment
  simp only [EndpointState.dependencyOrigin_cast] at small
  exact original_child (richSchedule_strict
    (Nat.lt_trans small (field_cost_lt outer controls.ordered environment)) _ _) _ _ _ _ _

private def ofCastControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = next)
    {certificate : RichCert sourceEnv env U registry target (node.cast equal rfl)
      locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (RichCert.ofCast equal rfl certificate)) := by
  cases equal
  exact ready

theorem ProjectionHead.packAssignedBridgeWorld
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
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ selected : AmbientBoundedGeneratedQueryReply base caps
        (OriginalNestedDisplay.recordBridgeReference rightGraph (.right innerRight.major) rfl)
        commonLeft commonRight (.singleton (n := n+1) (.record record)) (environmentCost rightEnvironment),
      ∃ _data : WorldGeneratedQueryReplyData (P := P) rightControls rightWorld frontier selected,
      ∃ answer : RichProjectionAssignedReply outerLeft outerRight env registry target
          selected.answer.reply.locals (leftRaw.comp commonLeft) (rightRaw.comp commonLeft)
          selected.answer.reply.available request.input,
        Nonempty (ControlledStoredQuery rightControls frontier (.certificate answer.code.certificate)) := by
  obtain ⟨selected, ⟨data⟩, projected, raw⟩ := ProjectionHead.recordMajorBridgeWorld outerLeft outerRight
    leftDisplay rightDisplay innerLeft innerRight leftMajorEq rightMajorEq leftGraph rightGraph displayedEq
    leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier paid
    leftFrame leftData rightFrame rightData henv hscoped formed nameEq member query resources ready bank unary
  have fieldLower := innerFieldBelow outerLeft leftDisplay innerLeft leftControls leftWorld
  obtain ⟨fieldSmaller, fieldPaid⟩ := inheritedCall frontier
    (from_left (calls := [originalCallWorld leftControls .fundamental innerLeft.field leftWorld])
      (by intro call present; cases List.mem_singleton.mp present; exact fieldLower)) paid (by
        intro call present
        cases List.mem_singleton.mp present
        exact ⟨_, List.mem_cons_self, fieldLower⟩)
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated leftFrame.frame leftData.generation
    leftData.controlled leftData.replayable leftData.compatible leftData.hereditary
  let diagonal := leftFrame.frame.leftDiagonal
  let captured := leftFrame.frame.diagonalWorld leftControls leftData.generation.environment
  have capacity : environmentCost (diagonal.dependencyEnvironment leftControls.ordered) ≤
      environmentCost leftEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal] using leftData.capacity
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds leftWorld.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using leftData.covered
  obtain ⟨fieldAnswer, _, _⟩ := (unary _ fieldSmaller).computational innerLeft.field
    (fieldProvenance innerLeft (castProvenance leftDisplay (fieldProvenance outerLeft leftProvenance)))
    leftControls diagonal captured leftWorld frontier capacity covered rfl fieldPaid
    frameData.leftDiagonal leftData.closed formed leftFrame.substitutions.left
    (.code sourceField) sourceResources sourceReady.code
  have code : TypeRelated env U registry target (.sort leftLevel) (.sort leftLevel) support := by
    simpa only [leftLiteral, subst_sort] using
      fieldAnswer.related.code_of_sortable henv hscoped formed sourceField.formed
  have leftWF : leftLevel.WF U :=
    (innerLeft.field.cast leftLiteral rfl).sound.defeq.sort_inv_l leftControls.ordered
  have rightWF : rightLevel.WF U :=
    (innerRight.field.cast rightLiteral rfl).sound.defeq.sort_inv_l rightControls.ordered
  obtain ⟨fieldCertificate, fieldReady, fieldRelated, fieldWorlds, fieldDepth⟩ :=
    TypeRelated.literalSortControlled (node := innerRight.field) (locals := selected.answer.reply.locals)
      (τ := rightRaw.comp commonLeft) rightLiteral henv hscoped formed leftWF rightWF levels
      code sourceField.formed rightControls frontier
  have fieldPath : TypeConversion env U target (innerLeft.fieldType.subst (leftRaw.comp commonLeft))
      (innerRight.fieldType.subst (rightRaw.comp commonLeft)) := by
    simpa only [leftLiteral, rightLiteral, subst_sort] using
      (show TypeConversion env U target (.sort leftLevel) (.sort rightLevel) from
        .single (.sortDF leftWF rightWF levels))
  have fieldRelated' : TypeRelated env U registry target
      (innerLeft.fieldType.subst (leftRaw.comp commonLeft))
      (innerRight.fieldType.subst (rightRaw.comp commonLeft)) support := by
    simpa only [leftLiteral, rightLiteral, subst_sort] using fieldRelated
  let chain := alignment.trans (.step fieldPath typed sourceField.formed fieldRelated' (.refl _))
  obtain ⟨majorFootprint, majorQuery, majorAnnotation, majorResources, majorWorlds, majorDepth⟩ :=
    selected.answer.reply.query.recordObservation_worlds_depth henv data.query.annotation
  let world := data.generation.environment
  let innerProvenance := castProvenance rightDisplay (fieldProvenance outerRight rightProvenance)
  let majorSite : WorldQuerySite strata (.ref (.right innerRight.major)) selected.answer.reply.locals
      (rightRaw.comp commonLeft) := {
    context := rightContext
    provenance := {
      rootSource := innerProvenance.rootSource, rootExpression := innerProvenance.rootExpression,
      rootType := innerProvenance.rootType, root := innerProvenance.root,
      initial := innerProvenance.initial,
      location := .projMajor (innerRight.route.locate innerProvenance.location),
      context_eq := by
        change rightContext = (innerRight.route.locate innerProvenance.location).contextDerivation innerProvenance.initial
        rw [PrefixRoute.locate_contextDerivation]
        exact innerProvenance.context_eq }
    right := rightRaw.comp commonRight
    available := selected.answer.reply.available
    frame := selected.answer.reply.realization.frame
    annotation := ⟨rightControls, world⟩ }
  let fieldSite : WorldQuerySite strata innerRight.field selected.answer.reply.locals
      (rightRaw.comp commonLeft) := {
    context := rightContext
    provenance := fieldProvenance innerRight innerProvenance
    right := rightRaw.comp commonRight
    available := selected.answer.reply.available
    frame := selected.answer.reply.realization.frame
    annotation := ⟨rightControls, world⟩ }
  have sitePaid : Sponsored frontier (majorSite.worlds ++ fieldSite.worlds) := by
    have outerBound := originalCallWorld_boundedNode rightControls .assignedComparison right
      world rightWorld (selected.bounded rightControls.ordered) data.covered
    have majorLower : WorldBelow strata.rules.length
        (originalCallWorld rightControls .fundamental (.ref (.right innerRight.major)) world)
        (originalCallWorld rightControls .assignedComparison right rightWorld) :=
      BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans outerBound
        (inner_major_below outerRight rightDisplay innerRight rightControls world _ _)
    have fieldLower : WorldBelow strata.rules.length
        (originalCallWorld rightControls .fundamental innerRight.field world)
        (originalCallWorld rightControls .assignedComparison right rightWorld) :=
      BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans outerBound
        (innerFieldBelow outerRight rightDisplay innerRight rightControls world)
    intro child present
    obtain ⟨sponsor, presentSponsor, lower⟩ := paid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    change child ∈ [_] ++ [_] at present
    rcases List.mem_append.mp present with present | present
    · cases List.mem_singleton.mp present
      exact ⟨sponsor, presentSponsor, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans majorLower lower⟩
    · cases List.mem_singleton.mp present
      exact ⟨sponsor, presentSponsor, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans fieldLower lower⟩
  let observation := RichObs.projection innerRight nameEq member majorQuery fieldCertificate typed chain
  let annotation := WorldObsProvenance.projection innerRight nameEq member majorAnnotation
    fieldReady.annotation majorSite fieldSite typed chain
  let observedReady : ControlledStoredQuery rightControls frontier (.observation observation) := {
    annotation := annotation
    within := by
      intro control active
      change observation.headDepth _ ≤ _
      simp only [observation, RichObs.headDepth, majorDepth, fieldDepth, Nat.max_zero]
      exact data.query.within control active
    sponsored := by
      change Sponsored frontier (majorSite.worlds ++ fieldSite.worlds ++ majorAnnotation.worlds ++ fieldReady.annotation.worlds)
      rw [majorWorlds]
      exact (sitePaid.merge data.query.sponsored).merge fieldReady.sponsored }
  let observedCertificate := RichCert.observe observation sorted
  let observedCertificateReady : ControlledStoredQuery rightControls frontier (.certificate observedCertificate) := {
    annotation := .observe observedReady.annotation sorted
    within := by
      simpa only [observedCertificate, StoredOriginalQuery.headDepth, RichCert.headDepth] using observedReady.within
    sponsored := observedReady.sponsored }
  let certificate := RichCert.ofCast rightDisplay rfl observedCertificate
  let certificateReady := ofCastControlled rightDisplay observedCertificateReady
  have related := alignment.related henv typed fieldRelated'.left_diagonal projected
  have rawSorted : env.IsDefEq U target
      ((VExpr.proj name prior leftMajor).subst (leftRaw.comp commonLeft))
      ((VExpr.proj name prior rightMajor).subst (rightRaw.comp commonLeft)) (.sort leftLevel) := by
    simpa only [leftLiteral, subst_sort] using alignment.path.cast raw
  refine ⟨selected, data, {
    path := ?_
    code := {
      footprint := majorFootprint ++ []
      certificate := certificate
      resources := ?_
      related := ?_ } }, ⟨certificateReady⟩⟩
  · simpa only [leftDisplay, rightDisplay] using TypeConversion.single rawSorted
  · intro index need present
    exact majorResources index need (by simpa only [List.append_nil] using present)
  · simpa only [leftDisplay, rightDisplay] using related.code_of_sortable henv hscoped formed sorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
