import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Restoring an actual original endpoint prefix keeps the generated capture
frame and its pre-answer capacity unchanged. Only source query syntax gains
its retained original route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def OriginalNestedDisplay.beforeRoute
    (display : OriginalNestedDisplay U common expression assigned)
    (node : EndpointState display.sourceEnv U display.source display.sourceExpression outerType)
    (provenance : EndpointProvenance display.context node) :
    OriginalNestedDisplay U common expression (outerType.subst display.raw) where
  sourceEnv := display.sourceEnv
  source := display.source
  sourceExpression := display.sourceExpression
  sourceType := outerType
  context := display.context
  node := node
  provenance := provenance
  raw := display.raw
  graph := display.graph
  expression_eq := display.expression_eq
  type_eq := rfl

noncomputable def RichGradedResult.prependRoute
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (query : RichGradedResult sourceEnv env U registry target last locals σ available requested) :
    RichGradedResult sourceEnv env U registry target first locals σ available requested where
  rank := query.rank
  bound := query.bound
  raw := query.raw
  footprint := query.footprint
  observation := .route route query.observation
  adapter := query.adapter
  resources := query.resources
  live := query.live

noncomputable def BoundedGeneratedQueryReply.prependRoute
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity)
    (node : EndpointState display.sourceEnv U display.source display.sourceExpression outerType)
    (provenance : EndpointProvenance display.context node)
    (route : PrefixRoute display.sourceEnv U display.source display.sourceExpression node display.node) :
    BoundedGeneratedQueryReply base commonCaps (display.beforeRoute node provenance)
      commonLeft commonRight requested capacity :=
  ⟨⟨⟨reply.answer.reply.locals, reply.answer.reply.available, reply.answer.reply.realization,
    reply.answer.reply.generated, reply.answer.reply.query.prependRoute route,
    reply.answer.reply.closed⟩, reply.answer.capped⟩, reply.bounded⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
