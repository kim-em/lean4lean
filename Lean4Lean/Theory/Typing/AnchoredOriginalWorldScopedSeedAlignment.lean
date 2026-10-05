import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep
import Lean4Lean.Theory.Typing.AnchoredOriginalSeedTypeHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryUnweaken
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! Finish a retained type-history replay at its actual selected declaration
frame. This consumes the computed replay result; it does not supply a route
interpreter or assume a completed header alignment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {headerAvailable : Valuation}

theorem PendingRichCapture.worldAlignmentOfReply
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {graph : OriginalCaptureMap (common := common) context raw}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (domainProvenance : EndpointProvenance context (.ref domain))
    (controls : OriginalWorldControls strata headerEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (henv : env.Ordered)
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node
      pending.ownerLocals pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (transported : AmbientBoundedParameterReply base scope.caps
      (pending.owner.assigned.subst pending.ownerLeft)
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      scope.left scope.right value.support (environmentCost baselineEnvironment))
    (data : WorldParameterReplyData (P := P) controls baseline frontier transported) :
    ∃ prior : AmbientBoundedGeneratedQueryReply base commonCaps
      (graph.parameterCellDisplay domain domainProvenance) commonLeft commonRight value.support
      (environmentCost baselineEnvironment),
    ∃ priorData : WorldGeneratedQueryReplyData (P := P) controls baseline frontier prior,
    ∃ alignment : HeaderValueAlignment pending.owner domain env registry target
      pending.ownerLocals prior.answer.reply.locals pending.ownerLeft pending.ownerRight
      (raw.comp commonLeft) pending.ownerAvailable prior.answer.reply.available pending.input,
      alignment.value = value.toRichBinderValue ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate alignment.aligned.certificate)) ∧
      priorData.query.annotation.worlds = data.query.annotation.worlds := by
  let selected : AmbientBoundedGeneratedQueryReply base scope.caps
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      scope.left scope.right value.support (environmentCost baselineEnvironment) :=
    ⟨transported.reply, transported.generation⟩
  let selectedData : WorldGeneratedQueryReplyData (P := P) controls baseline frontier selected := {
    generation := data.generation, hereditary := data.hereditary, replayable := data.replayable,
    controlled := data.controlled, compatible := data.compatible,
    query := data.query, covered := data.covered }
  obtain ⟨prior, priorData, _, _, _, queryWorlds, _baseUses, _tablesClosed⟩ :=
    WorldGeneratedQueryReplyData.unweaken scope.insertion scope.leftTail scope.rightTail
      scope.capsTail selected selectedData
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    prior.answer.reply.query.code_controlled henv controls priorData.query value.certificate.formed
  have destination : (((A.subst raw).lift' (.skipN .refl pending.depth)).subst scope.left) =
      A.subst (raw.comp commonLeft) := by
    rw [subst_lift', scope.leftTail, subst_subst]
  let alignment : HeaderValueAlignment pending.owner domain env registry target
      pending.ownerLocals prior.answer.reply.locals pending.ownerLeft pending.ownerRight
      (raw.comp commonLeft) pending.ownerAvailable prior.answer.reply.available pending.input := {
    value := value.toRichBinderValue
    aligned := {
      footprint := footprint, certificate := certificate, resources := resources
      related := by
        simpa only [OriginalNestedDisplay.weaken, OriginalCaptureMap.parameterCellDisplay,
          destination] using transported.related }
    path := by
      simpa only [OriginalNestedDisplay.weaken, OriginalCaptureMap.parameterCellDisplay,
        destination] using transported.path }
  exact ⟨prior, priorData, alignment, rfl, ⟨certificateReady⟩, queryWorlds⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
