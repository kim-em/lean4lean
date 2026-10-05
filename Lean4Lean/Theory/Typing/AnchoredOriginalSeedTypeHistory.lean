import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalOwnerScope
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! Low, query-independent type history for a retained capture seed.
No generated-frame proofs, semantic answers, or recursive callbacks occur
in the history. Its endpoint indices fix the actual original occurrences
and the actual pre-answer environments. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private noncomputable def HeaderOwner.seedProvenance
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major) (initial : ContextDerivation sourceEnv U source) :
    EndpointProvenance (owner.context initial) owner.node := by
  cases owner with
  | inl node => exact .ofLocation node.location initial
  | inr node => exact .ofLocation node.location initial

noncomputable def PendingRichCapture.assignedOwnerScopeDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight seed.depth
      (seed.owner.context seed.initialContext)) :
    OriginalNestedDisplay U scope.scope (seed.owner.assigned.subst scope.raw)
      (.sort seed.owner.node.typeFormation.level) where
  sourceEnv := sourceEnv
  source := seed.owner.source
  sourceExpression := seed.owner.assigned
  sourceType := .sort seed.owner.node.typeFormation.level
  context := seed.owner.context seed.initialContext
  node := seed.owner.node.typeFormation.node
  provenance := {
    rootSource := (seed.owner.seedProvenance seed.initialContext).rootSource
    rootExpression := (seed.owner.seedProvenance seed.initialContext).rootExpression
    rootType := (seed.owner.seedProvenance seed.initialContext).rootType
    root := (seed.owner.seedProvenance seed.initialContext).root
    initial := (seed.owner.seedProvenance seed.initialContext).initial
    location := .assignedFormation (seed.owner.seedProvenance seed.initialContext).location
    context_eq := (seed.owner.seedProvenance seed.initialContext).context_eq }
  raw := scope.raw
  graph := scope.graph
  expression_eq := rfl
  type_eq := rfl

/-- Only the common source scope changes. The declared domain's original
node, context and provenance are retained verbatim. -/
noncomputable def OriginalOwnerScope.declaredTypeDisplay
    {raw : Subst}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight depth ownerContext)
    (graph : OriginalCaptureMap (common := common) context raw)
    (provenance : EndpointProvenance context (.ref domain)) :
    OriginalNestedDisplay U scope.scope ((A.subst raw).lift' (.skipN .refl depth)) (.sort level) where
  sourceEnv := headerEnv
  source := headerSource
  sourceExpression := A
  sourceType := .sort level
  context := context
  node := .ref domain
  provenance := provenance
  raw := raw.lift_r (.skipN .refl depth)
  graph := .weaken graph scope.insertion
  expression_eq := by rw [← lift'_subst]
  type_eq := rfl

/-- Exactly one retained seed and one actual preceding declaration frame
fix the history's two closure environments. Frame selection inside the
finite route remains explicit; no alignment result is part of this packet. -/
structure OriginalSeedTypeHistory
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals (raw.comp commonLeft) headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight seed.depth
      (seed.owner.context seed.initialContext))
    (graph : OriginalCaptureMap (common := common) context raw)
    (provenance : EndpointProvenance context (.ref domain))
    (prior : OriginalCaptureRealization graph env registry target priorLocals commonLeft commonRight priorAvailable)
    (sourceOrdered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered) where
  route : RawGeneratedTypeRoute env registry target scope.left scope.right
    (seed.assignedOwnerScopeDisplay scope) (scope.declaredTypeDisplay graph provenance)
    (seed.frame.dependencyEnvironment sourceOrdered) (prior.frame.dependencyEnvironment headerOrdered)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
