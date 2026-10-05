import Lean4Lean.Theory.Typing.AnchoredOriginalSeedTypeHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedScopedGroupActivation
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteReplay

/-! A retained seed's type history starts at its actual assigned formation.
No equality between its raw assigned type and the declared domain is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {headerAvailable : Valuation}

noncomputable def PendingRichCapture.assignedScopeDisplayRaw
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps pending.depth
      (pending.owner.context pending.initialContext))
    :
    OriginalNestedDisplay U scope.scope (pending.owner.assigned.subst scope.raw)
      (.sort pending.owner.node.typeFormation.level) :=
  pending.assignedOwnerScopeDisplay scope.toOriginalOwnerScope


/-- Requerying the declaration-side table does not replace the retained
baseline frame or any original route closure. -/
def OriginalSeedTypeHistory.reheader
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue}
    {scope : OriginalOwnerScope common ownerRaw commonLeft commonRight seed.depth
      (seed.owner.context seed.initialContext)}
    {graph : OriginalCaptureMap (common := common) context raw}
    {provenance : EndpointProvenance context (.ref domain)}
    {prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable}
    {sourceOrdered : sourceEnv.Ordered} {headerOrdered : headerEnv.Ordered}
    (history : OriginalSeedTypeHistory seed scope graph provenance prior sourceOrdered headerOrdered)
    (nextLocals : List Nat) (nextAvailable : Valuation) :
    OriginalSeedTypeHistory (seed.reheader nextLocals (raw.comp commonLeft) nextAvailable)
      scope graph provenance prior sourceOrdered headerOrdered :=
  ⟨history.route⟩

/-- Replay the finite history against the exact certificate returned for the
retained owner. The chosen declared frame is returned together with a genuine
alignment; no literal equality of the two assigned types is required. -/
theorem PendingRichCapture.alignScopeRoute
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
    (pendingCapped : CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph pending.frame.raw)
    (domainProvenance : EndpointProvenance context (.ref domain))
    (ordered : sourceEnv.Ordered)
    (baseline : List Closure)
    (frameBound : environmentCost (pending.frame.dependencyEnvironment ordered) ≤ environmentCost baseline)
    (route : RawGeneratedTypeRoute env registry target scope.left scope.right
      (pending.assignedScopeDisplayRaw scope)
      ((graph.parameterCellDisplay domain domainProvenance).weaken scope.insertion)
      baseline final)
    (generated : route.Generated base scope.caps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (calls : route.Calls base scope.caps limit)
    (scheduled : route.schedule < limit)
    (value : RichSupportedValue sourceEnv env U registry target pending.owner.node
      pending.ownerLocals pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input) :
    ∃ prior : BoundedGeneratedQueryReply base commonCaps
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
  obtain ⟨incoming⟩ := BoundedGeneratedQueryReply.ofFrame
    (capacity := environmentCost baseline)
    (pending.assignedScopeDisplayRaw scope) pending.frame pendingCapped pending.substitutions
    pending.ownerClosed query (fun _ => frameBound)
  have realized : (pending.owner.assigned.subst scope.raw).subst scope.left =
      pending.owner.assigned.subst pending.ownerLeft := by
    rw [subst_subst, ← pendingCapped.generated.realizations.1]
  let initial : BoundedParameterReply base scope.caps
      (pending.owner.assigned.subst pending.ownerLeft) (pending.assignedScopeDisplayRaw scope)
      scope.left scope.right value.support
      (environmentCost baseline) := {
    reply := incoming
    related := by
      change TypeRelated _ _ _ _ _ ((pending.owner.assigned.subst scope.raw).subst scope.left) _
      rw [realized]
      exact value.typeCode
    path := by
      change TypeConversion _ _ _ _ ((pending.owner.assigned.subst scope.raw).subst scope.left)
      rw [realized]
      exact .refl }
  obtain ⟨transported⟩ := route.replay generated henv hscoped formed calls scheduled initial value.certificate.formed
  obtain ⟨prior⟩ := transported.reply.unweaken scope.insertion scope.leftTail scope.rightTail scope.capsTail
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
