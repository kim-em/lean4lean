import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply

/-! Treating the whole current frame as a base freezes its exact resources.
At the identity source graph the hereditary cap is literal membership in
that base valuation. Thus query-selected reconstruction at the identity graph
returns a genuine fixed-resource query, even when its frame contains merges. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def OriginalRichFrame.captureBase
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    OriginalCaptureBase env U registry target :=
  ⟨sourceEnv, source, context, locals, σ, τ, available, frame, substitutions⟩

def OriginalCaptureBase.identityRealization
    (base : OriginalCaptureBase env U registry target) :
    OriginalCaptureRealization (.identity base.context) env registry target
      base.locals base.left base.right base.available :=
  ⟨base.frame, base.substitutions⟩

theorem OriginalCaptureBase.identityCapped
    (base : OriginalCaptureBase env U registry target) :
    CappedCaptureGenerated base base.initialCaps base.left base.right
      (.identity base.context) base.identityRealization.frame.raw :=
  .identity

def OriginalNestedDisplay.identity
    (base : OriginalCaptureBase env U registry target)
    (node : EndpointState base.sourceEnv U base.source expression assigned)
    (provenance : EndpointProvenance base.context node) :
    OriginalNestedDisplay U base.source expression assigned where
  sourceEnv := base.sourceEnv
  source := base.source
  sourceExpression := expression
  sourceType := assigned
  context := base.context
  node := node
  provenance := provenance
  raw := .id
  graph := .identity base.context
  expression_eq := subst_id.symm
  type_eq := subst_id.symm

/-- At an identity destination, all selected resources are original base
resources. This is a consequence of the cap derivation, not an extra
fixed-resource premise on the recursive answer. -/
def CappedGeneratedQueryReply.freezeBase
    {base : OriginalCaptureBase env U registry target}
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    {provenance : EndpointProvenance base.context node}
    (reply : CappedGeneratedQueryReply base base.initialCaps
      (OriginalNestedDisplay.identity base node provenance) base.left base.right requested) :
    RichGradedResult base.sourceEnv env U registry target node base.locals base.left base.available requested := by
  have same : reply.reply.locals = base.locals := reply.reply.locals_eq
  have included : ∀ index need, need ∈ reply.reply.available index → need ∈ base.available index :=
    reply.capped.availableBound
  have query := reply.reply.query.availableMono included
  have idComp : Subst.comp .id base.left = base.left := rfl
  simpa only [OriginalNestedDisplay.identity, same, idComp] using query

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
