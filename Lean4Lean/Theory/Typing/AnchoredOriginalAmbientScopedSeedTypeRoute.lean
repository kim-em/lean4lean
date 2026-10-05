import Lean4Lean.Theory.Typing.AnchoredOriginalScopedSeedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientRawTypeRouteReplay

/-! Replay a retained seed history using its actual positive frames and the
qualified lower induction. The selected declaration frame and alignment are
returned together, with hereditary generation on that same frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

variable {headerAvailable : Valuation}

/-- Replay the finite history against the exact certificate returned for the
retained owner. The chosen declared frame is returned together with a genuine
alignment; no literal equality of the two assigned types is required. -/
theorem PendingRichCapture.alignScopeRouteAmbient
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
    (pendingCapped : AmbientCaptureGenerated base scope.caps scope.left scope.right scope.graph pending.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (ordered : sourceEnv.Ordered)
    (baseline : List Closure)
    (frameBound : environmentCost (pending.frame.dependencyEnvironment ordered) ≤ environmentCost baseline)
    (route : RawGeneratedTypeRoute env registry target scope.left scope.right
      (pending.assignedScopeDisplayRaw scope)
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      baseline final)
    (generated : route.AmbientGenerated base scope.caps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : route.schedule < limit)
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node
      pending.ownerLocals pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input) :
    ∃ prior : AmbientBoundedGeneratedQueryReply base commonCaps
        (graph.parameterCellDisplay domain domainProvenance) commonLeft commonRight value.support
        (environmentCost final),
      ∃ answer : HeaderValueAlignment pending.owner domain env registry target
        pending.ownerLocals prior.answer.reply.locals pending.ownerLeft pending.ownerRight
        (raw.comp commonLeft) pending.ownerAvailable prior.answer.reply.available pending.input,
        answer.value = value.toRichBinderValue := by
  let query : RichGradedResult sourceEnv env U registry target pending.owner.node.typeFormation.node
      pending.ownerLocals pending.ownerLeft pending.ownerAvailable value.support := {
    rank := pending.rank, bound := Nat.le_refl _, raw := value.support
    footprint := value.footprint, observation := .code value.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := value.resources
    live := Profile.HasType.sortable_live value.certificate.formed }
  obtain ⟨incoming⟩ := AmbientBoundedGeneratedQueryReply.ofFrame
    (capacity := environmentCost baseline)
    (pending.assignedScopeDisplayRaw scope) pending.frame pendingCapped pending.substitutions
    pending.ownerClosed query (fun _ => frameBound)
  have realized : (pending.owner.assigned.subst scope.raw).subst scope.left =
      pending.owner.assigned.subst pending.ownerLeft := by
    rw [subst_subst, ← pendingCapped.capped.generated.realizations.1]
  let initial : AmbientBoundedParameterReply base scope.caps
      (pending.owner.assigned.subst pending.ownerLeft) (pending.assignedScopeDisplayRaw scope)
      scope.left scope.right value.support
      (environmentCost baseline) := {
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
  obtain ⟨transported⟩ := route.replayAmbient generated henv hscoped formed bank scheduled initial value.certificate.formed
  let selected : AmbientBoundedGeneratedQueryReply base scope.caps
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      scope.left scope.right value.support (environmentCost final) :=
    ⟨transported.reply, transported.generation⟩
  obtain ⟨prior⟩ := selected.unweaken scope.insertion scope.leftTail scope.rightTail scope.capsTail
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.answer.reply.query.code henv value.certificate.formed
  have destination : (((A.subst raw).lift' (.skipN .refl pending.depth)).subst scope.left) =
      A.subst (raw.comp commonLeft) := by
    rw [subst_lift', scope.leftTail, subst_subst]
  refine ⟨prior, {
    value := value.toRichBinderValue
    aligned := {
      footprint := footprint, certificate := certificate, resources := resources
      related := ?_ }
    path := ?_ }, rfl⟩
  · simpa only [OriginalNestedDisplay.weaken, OriginalCaptureMap.parameterCellDisplay,
      destination] using transported.related
  · simpa only [OriginalNestedDisplay.weaken, OriginalCaptureMap.parameterCellDisplay,
      destination] using transported.path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
