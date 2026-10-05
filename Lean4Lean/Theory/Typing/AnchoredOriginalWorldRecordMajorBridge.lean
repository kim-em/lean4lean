import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
import Lean4Lean.Theory.Typing.AnchoredRecordTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation

/-! The record-major bridge executes its actual R and directional equality
calls at selected frames. Equality preserves the externally retained paired
generation; its interpreter uses the exact left diagonal only internally. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private major_below inner_major_below from_left from_right from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private MixedInsertion.eqBack from Lean4Lean.Theory.Typing.AnchoredRecordTrace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable def OriginalNestedDisplay.recordBridgeReference
    {sourceEnv : VEnv} {U : Nat} {source common : List VExpr} {raw : Subst}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (equal : displayed = expression.subst raw) :
    OriginalNestedDisplay U common displayed (assigned.subst raw) :=
  ⟨sourceEnv, source, expression, assigned, context, .ref reference,
    .ofLocation .here context, raw, graph, equal, rfl⟩

private theorem recordControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered)
    (query : RichGradedResult sourceEnv env U registry target node locals σ available
      (.singleton (n := n+1) (.record record)))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    ∃ footprint, ∃ output : RichObs sourceEnv env U registry target node locals σ
        (.singleton (n := n+1) (.record record)) footprint,
      footprint.Available available ∧
      Nonempty (ControlledStoredQuery (strata := strata) controls frontier (.observation output)) := by
  obtain ⟨footprint, output, annotation, resources, worlds, depth⟩ :=
    query.recordObservation_worlds_depth henv ready.annotation
  exact ⟨footprint, output, resources, ⟨{
    annotation := annotation
    within := fun control active => by
      change output.headDepth _ ≤ _
      rw [depth]
      exact ready.within control active
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [worlds]
      exact ready.sponsored }⟩⟩

private theorem equalitySelected
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier parent : List (World strata.rules.length))
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference graph (originalTypeRouteSide original forward) rfl)
      controls baseline frontier frame)
    (formed : OnCtx target (env.IsType U))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref (.left original)) baseline])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.left original)) baseline]) parent)
    (bank : WorldBoundedUnaryCallBank env U registry strata P parent)
    (query : RichObs sourceEnv env U registry target (.ref (originalTypeRouteSide original forward))
      locals (raw.comp commonLeft) profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query)) :
    ∃ answer : OriginalDirectionalEqualityResult original forward env registry target locals
        (raw.comp commonLeft) (raw.comp commonLeft) available profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame data.generation data.controlled
    data.replayable data.compatible data.hereditary
  let diagonal := frame.frame.leftDiagonal
  let captured := frame.frame.diagonalWorld controls data.generation.environment
  have capacity : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal] using data.capacity
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using data.covered
  exact (bank _ smaller).equality original forward (.ofLocation .here context)
    controls diagonal captured baseline frontier capacity covered
    (by rw [originalEqualityCallWorld])
    (by simpa only [originalEqualityCallWorld] using paid)
    frameData.leftDiagonal data.closed formed frame.substitutions.left query resources ready

private def replyFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight profile
      (environmentCost baselineEnvironment)}
    (data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply) :
    WorldCallFrameData (P := P) (base := base) (caps := caps) (display := display)
      controls baseline frontier reply.answer.reply.realization :=
  ⟨data.generation, data.replayable, data.controlled, data.compatible,
    reply.answer.reply.closed, reply.bounded controls.ordered, data.covered, data.hereditary⟩

private def relabel
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {first : EndpointRef sourceEnv U source firstExpression firstType}
    {second : EndpointRef sourceEnv U source secondExpression secondType}
    {firstEq : firstDisplay = firstExpression.subst raw}
    {secondEq : secondDisplay = secondExpression.subst raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available}
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference graph first firstEq) controls baseline frontier frame) :
    WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference graph second secondEq) controls baseline frontier frame :=
  ⟨data.generation, data.replayable, data.controlled, data.compatible,
    data.closed, data.capacity, data.covered, data.hereditary⟩

private theorem inheritedCall
    {strata : EquationStratification env}
    {calls parents : List (World strata.rules.length)}
    (frontier : List (World strata.rules.length))
    (smaller : CallBelow strata.rules.length calls parents)
    (paid : Sponsored frontier parents)
    (lower : ∀ call ∈ calls, ∃ parent ∈ parents, WorldBelow strata.rules.length call parent) :
    CallBelow strata.rules.length (frontier ++ calls) (frontier ++ parents) ∧
      Sponsored frontier calls := by
  constructor
  · clear paid lower
    induction frontier with
    | nil => exact smaller
    | cons head tail ih => exact ih.cons head
  · intro call member
    obtain ⟨parent, present, below⟩ := lower call member
    obtain ⟨sponsor, present, next⟩ := paid parent present
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans below next⟩

private theorem recordProjectionRawWorld
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (related : Related env U registry target left right assigned
      (Profile.singleton (n := n + 1) (.record record)) support)
    (member : (index, request) ∈ record.fields) :
    env.IsDefEq U target (.proj record.family.name index left)
      (.proj record.family.name index right) request.domain := by
  obtain ⟨witness⟩ := related.recordRelation henv hscoped formed target .refl (.refl formed)
  have rename : record.rename .refl = record := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  have admitted := witness.fields.map_member member
  apply MixedInsertion.eqBack henv witness.insertion
  exact admitted.2.1


/-- Execute all five original calls. Each R retains its selected generated
frame; each equality interprets the record on that frame's exact diagonal.
The strict calls are funded by the actual outer projection pair. -/
theorem ProjectionHead.recordMajorBridgeWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    (leftDisplay : outerLeft.fieldType = .proj name prior leftMajor)
    (rightDisplay : outerRight.fieldType = .proj name prior rightMajor)
    (innerLeft : ProjectionHead (outerLeft.field.cast leftDisplay rfl))
    (innerRight : ProjectionHead (outerRight.field.cast rightDisplay rfl))
    (leftMajorEq : leftMajor = outerLeft.sourceMajor)
    (rightMajorEq : rightMajor = outerRight.sourceMajor)
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
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (OriginalNestedDisplay.recordBridgeReference rightGraph (.right innerRight.major) rfl) commonLeft commonRight
        (.singleton (n := n+1) (.record record)) (environmentCost rightEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) rightControls rightWorld frontier reply) ∧
      Related env U registry target
        ((VExpr.proj name prior leftMajor).subst (leftRaw.comp commonLeft))
        ((VExpr.proj name prior rightMajor).subst (rightRaw.comp commonLeft))
        request.domain request.input request.support ∧
      env.IsDefEq U target
        ((VExpr.proj name prior leftMajor).subst (leftRaw.comp commonLeft))
        ((VExpr.proj name prior rightMajor).subst (rightRaw.comp commonLeft)) request.domain := by
  obtain ⟨firstSmaller, forwardSmaller, middleSmaller, backwardSmaller, lastSmaller⟩ :=
    projectionTemplateBridgeFunding outerLeft outerRight leftDisplay rightDisplay innerLeft innerRight
      leftControls rightControls leftWorld rightWorld
  have leftOuter := major_below outerLeft leftControls leftWorld
  have rightOuter := major_below outerRight rightControls rightWorld
  have leftInner := inner_major_below outerLeft leftDisplay innerLeft leftControls leftWorld
  have rightInner := inner_major_below outerRight rightDisplay innerRight rightControls rightWorld
  obtain ⟨firstSmaller, firstPaid⟩ := inheritedCall frontier firstSmaller paid (by
    intro call present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨_, List.mem_cons_self, leftInner _ _⟩
    · cases List.mem_singleton.mp present
      exact ⟨_, List.mem_cons_self, leftOuter _ _⟩)
  obtain ⟨forwardSmaller, forwardPaid⟩ := inheritedCall frontier forwardSmaller paid (by
    intro call present
    cases List.mem_singleton.mp present
    exact ⟨_, List.mem_cons_self, leftOuter _ _⟩)
  obtain ⟨middleSmaller, middlePaid⟩ := inheritedCall frontier middleSmaller paid (by
    intro call present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨_, List.mem_cons_self, leftOuter _ _⟩
    · cases List.mem_singleton.mp present
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rightOuter _ _⟩)
  obtain ⟨backwardSmaller, backwardPaid⟩ := inheritedCall frontier backwardSmaller paid (by
    intro call present
    cases List.mem_singleton.mp present
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rightOuter _ _⟩)
  obtain ⟨lastSmaller, lastPaid⟩ := inheritedCall frontier lastSmaller paid (by
    intro call present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rightOuter _ _⟩
    · cases List.mem_singleton.mp present
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rightInner _ _⟩)
  let firstDisplay := OriginalNestedDisplay.recordBridgeReference leftGraph (.left outerLeft.major)
    (congrArg (VExpr.subst · leftRaw) leftMajorEq)
  obtain ⟨first, ⟨firstData⟩⟩ := (bank _ firstSmaller).observation base caps
    (OriginalNestedDisplay.recordBridgeReference leftGraph (.right innerLeft.major) rfl) firstDisplay commonLeft commonRight
    leftControls leftControls rfl rfl leftWorld leftWorld frontier rfl firstPaid
    leftFrame leftData leftFrame (relabel leftData) query resources ready
  obtain ⟨_, firstQuery, firstResources, ⟨firstReady⟩⟩ :=
    recordControlled henv first.answer.reply.query firstData.query
  obtain ⟨forward, ⟨forwardReady⟩⟩ := equalitySelected leftGraph outerLeft.major true
    leftControls leftWorld frontier _ first.answer.reply.realization (relabel (replyFrame firstData))
    formed forwardPaid forwardSmaller unary firstQuery firstResources firstReady
  obtain ⟨_, forwardQuery, forwardResources, ⟨forwardQueryReady⟩⟩ :=
    recordControlled henv forward.rightQuery forwardReady
  let middleDisplay := OriginalNestedDisplay.recordBridgeReference rightGraph (.right outerRight.major) displayedEq
  obtain ⟨middle, ⟨middleData⟩⟩ := (bank _ middleSmaller).observation base caps
    (OriginalNestedDisplay.recordBridgeReference leftGraph (.right outerLeft.major) rfl) middleDisplay commonLeft commonRight
    leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier rfl middlePaid
    first.answer.reply.realization (relabel (replyFrame firstData))
    rightFrame (relabel rightData) forwardQuery forwardResources forwardQueryReady
  obtain ⟨_, middleQuery, middleResources, ⟨middleReady⟩⟩ :=
    recordControlled henv middle.answer.reply.query middleData.query
  obtain ⟨backward, ⟨backwardReady⟩⟩ := equalitySelected rightGraph outerRight.major false
    rightControls rightWorld frontier _ middle.answer.reply.realization (relabel (replyFrame middleData))
    formed backwardPaid backwardSmaller unary middleQuery middleResources middleReady
  obtain ⟨_, backwardQuery, backwardResources, ⟨backwardQueryReady⟩⟩ :=
    recordControlled henv backward.rightQuery backwardReady
  let lastDisplay := OriginalNestedDisplay.recordBridgeReference rightGraph (.left outerRight.major)
    (congrArg (VExpr.subst · rightRaw) rightMajorEq)
  obtain ⟨last, ⟨lastData⟩⟩ := (bank _ lastSmaller).observation base caps lastDisplay
    (OriginalNestedDisplay.recordBridgeReference rightGraph (.right innerRight.major) rfl) commonLeft commonRight
    rightControls rightControls rfl rfl rightWorld rightWorld frontier rfl lastPaid
    middle.answer.reply.realization (relabel (replyFrame middleData))
    middle.answer.reply.realization (relabel (replyFrame middleData))
    backwardQuery backwardResources backwardQueryReady
  have displayed : displayedLeft.subst (leftRaw.comp commonLeft) =
      displayedRight.subst (rightRaw.comp commonLeft) := by
    rw [← subst_subst, ← subst_subst, displayedEq]
  have firstRelated := forward.related.projectRecord henv hscoped formed member
  have lastRelated := backward.related.projectRecord henv hscoped formed member
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, nameEq]
    at firstRelated lastRelated
  have related := firstRelated.trans henv hscoped (by simpa only [displayed] using lastRelated)
  have firstRaw := recordProjectionRawWorld henv hscoped formed forward.related member
  have lastRaw := recordProjectionRawWorld henv hscoped formed backward.related member
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, nameEq]
    at firstRaw lastRaw
  have raw := firstRaw.trans (by simpa only [displayed] using lastRaw)
  exact ⟨last, ⟨lastData⟩, by simpa only [subst_proj, leftMajorEq, rightMajorEq] using related,
    by simpa only [subst_proj, leftMajorEq, rightMajorEq] using raw⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
