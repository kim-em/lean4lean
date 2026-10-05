import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! The actual retained owner query and its selected frame, independent of the native Pi replay implementation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

section
variable
  {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  {domain : EndpointRef headerEnv U headerSource A (.sort level)}
  (seed : PendingRichCapture (field := field) (major := major) domain env registry target
    headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
  (graph : OriginalCaptureMap (common := common) (seed.owner.context seed.initialContext) raw)
  (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph seed.frame.raw)

noncomputable def PendingRichCapture.seedDisplay :
    OriginalNestedDisplay U common (seed.owner.expression.subst raw) (seed.owner.assigned.subst raw) where
  sourceEnv := sourceEnv
  source := seed.owner.source
  sourceExpression := seed.owner.expression
  sourceType := seed.owner.assigned
  context := seed.owner.context seed.initialContext
  node := seed.owner.node
  provenance := seed.owner.provenance seed.initialContext
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

/-- The recursive answer becomes a pending query at the SAME original owner.
No assigned-type certificate or declaration alignment is supplied here. -/
noncomputable def PendingRichCapture.requery
    (ordered : sourceEnv.Ordered)
    (answer : BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered))) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue where
  owner := seed.owner
  ownerLocals := answer.answer.reply.locals
  ownerLeft := raw.comp commonLeft
  ownerRight := raw.comp commonRight
  ownerAvailable := answer.answer.reply.available
  ownerClosed := answer.answer.reply.closed
  initialContext := seed.initialContext
  frame := answer.answer.reply.realization.frame
  substitutions := answer.answer.reply.realization.substitutions
  frame_environment_le := fun formed => Nat.le_trans (answer.bounded formed) (seed.frame_environment_le formed)
  depth := seed.depth
  sourcePrefix := seed.sourcePrefix
  source_eq := seed.source_eq
  depth_eq := seed.depth_eq
  expression_eq := seed.expression_eq
  left_eq := by rw [← generated.generated.realizations.1]; exact seed.left_eq
  right_eq := by rw [← generated.generated.realizations.2]; exact seed.right_eq
  rank := answer.answer.reply.query.rank
  input := answer.answer.reply.query.raw
  footprint := answer.answer.reply.query.footprint
  query := answer.answer.reply.query.observation
  queryAvailable := answer.answer.reply.query.resources

theorem PendingRichCapture.requery_capped
    (ordered : sourceEnv.Ordered)
    (answer : BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered))) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight graph
      (seed.requery graph generated ordered answer).frame.raw := answer.answer.capped

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
