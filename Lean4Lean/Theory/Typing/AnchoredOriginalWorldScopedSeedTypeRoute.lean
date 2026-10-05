import Lean4Lean.Theory.Typing.AnchoredOriginalSeedTypeHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryUnweaken
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply

/-! The actual owner-F answer enters its retained type history at the original
seed baseline. Selected frames may be smaller and have different resources;
the original finite route and its baseline are not rewritten to that choice. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private replyOfFrame from Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryUnweaken
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- This is the initial-reply adapter used by scoped history replay, not a
supplier of a completed alignment or an independent type comparison. -/
theorem PendingRichCapture.worldAssignedInput
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (generated : WorldGenerated strata P base scope.caps scope.left scope.right scope.graph pending.frame.raw controls)
    (replayable : generated.Replayable)
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (bound : ∀ ordered, environmentCost (pending.frame.dependencyEnvironment ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node
      pending.ownerLocals pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (valueReady : ControlledStoredQuery controls frontier (.certificate value.certificate)) :
    ∃ initial : AmbientBoundedParameterReply base scope.caps
      (pending.owner.assigned.subst pending.ownerLeft)
      (pending.assignedOwnerScopeDisplay scope.toOriginalOwnerScope) scope.left scope.right value.support
      (environmentCost baselineEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls baseline frontier initial) := by
  let query : RichGradedResult sourceEnv env U registry target pending.owner.node.typeFormation.node
      pending.ownerLocals pending.ownerLeft pending.ownerAvailable value.support := {
    rank := pending.rank, bound := Nat.le_refl _, raw := value.support
    footprint := value.footprint, observation := .code value.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := value.resources
    live := Profile.HasType.sortable_live value.certificate.formed }
  have queryReady : ControlledStoredQuery controls frontier (.observation query.observation) := {
    annotation := .code valueReady.annotation
    within := by
      intro control active
      simpa only [query, StoredOriginalQuery.headDepth, RichObs.headDepth] using valueReady.within control active
    sponsored := valueReady.sponsored }
  obtain ⟨incoming, data, _, _, _, _, _, _⟩ := replyOfFrame
    (pending.assignedOwnerScopeDisplay scope.toOriginalOwnerScope) controls baseline frontier
    pending.frame generated replayable ready compatible hereditary pending.substitutions pending.ownerClosed
    query queryReady bound covered
  have realized : (pending.owner.assigned.subst scope.raw).subst scope.left =
      pending.owner.assigned.subst pending.ownerLeft := by
    rw [subst_subst, ← generated.erase.capped.generated.realizations.1]
  let initial : AmbientBoundedParameterReply base scope.caps
      (pending.owner.assigned.subst pending.ownerLeft)
      (pending.assignedOwnerScopeDisplay scope.toOriginalOwnerScope) scope.left scope.right value.support
      (environmentCost baselineEnvironment) := {
    reply := incoming.toBoundedGeneratedQueryReply
    generation := incoming.generation
    related := by
      change TypeRelated _ _ _ _ _ ((pending.owner.assigned.subst scope.raw).subst scope.left) _
      rw [realized]
      exact value.typeCode
    path := by
      change TypeConversion _ _ _ _ ((pending.owner.assigned.subst scope.raw).subst scope.left)
      rw [realized]
      exact .refl }
  exact ⟨initial, ⟨{
    generation := data.generation, hereditary := data.hereditary, replayable := data.replayable,
    controlled := data.controlled, compatible := data.compatible,
    query := data.query, covered := data.covered }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
