import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalFrameExtension
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureSyntax

/-! Exact finite operands of generated Pi capture; no semantic replay is
needed to record the actual owner extension and destination display. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The finite capture keeps its independent original seed and every
actual owner-frame extension used to restrict the selected row's needs. -/
structure GeneratedArgumentCaptureTrace
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation sourceEnv U source}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext
      ownerLocals ownerLeft ownerRight ownerAvailable)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (input : Profile n)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) where
  seedExtension : OriginalFrameExtension ownerFrame.raw pending.frame.raw
  queryBound : n ≤ pending.rank
  queryAdapter : GeneralNormalProfileAdapter env U registry target pending.input
    (raiseProfile pending.rank queryBound input)
  inputPresent : (⟨n, input⟩ : Need) ∈ entries.needs
  owners : ∀ selected ∈ entries, selected.owner = pending.owner
  extensions : ∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw selected.frame.raw)

noncomputable def capturedPiBodyDisplay
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal) :
    OriginalNestedDisplay U common (B.subst (raw.cons (argument.subst nominalRaw))) (.sort v) where
  sourceEnv := headerEnv
  source := A :: headerSource
  sourceExpression := B
  sourceType := .sort v
  context := .cons (location.contextDerivation initial) domain
  node := body
  provenance := by
    have contextEq : (Located.piBody location).contextDerivation initial =
        .cons (location.contextDerivation initial) domain := by
      change ContextDerivation.cons (location.contextDerivation initial)
        (Classical.choose location.originalDomains.1) = _
      exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
        (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
    exact contextEq ▸ EndpointProvenance.ofLocation (.piBody location) initial
  raw := raw.cons (argument.subst nominalRaw)
  graph := .capture graph domain nominalGraph nominal provenance
  expression_eq := rfl
  type_eq := rfl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
