import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReanchor

/-! A queried whole-Pi history retains the exact requested row at its actual
selected header frame. The two reanchoring calls are the header Pi's original
formation children, bounded by the returned frame capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- No row or declared alignment is supplied: extraction traverses the actual
returned rich certificate, including its generalized adapters and code actions. -/
theorem BoundedParameterReply.nativePiRow
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation sourceEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (answer : BoundedParameterReply base commonCaps start
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi protoDomain protoBody (support : Profile n) [(key, result)]) capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi protoDomain protoBody support [(key, result)]).HasType (.sort true))
    (domainF : OriginalCodeInductionAt env registry ordered initial (.piDomain location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin ordered).weight * (1 + capacity)))
    (bodyF : OriginalCodeInductionAt env registry ordered initial (.piBody location)
      (((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin ordered).weight * (1 + capacity))) :
    Nonempty (RichPiRowCertificate env U registry target answer.reply.answer.reply.locals
      (raw.comp commonLeft) answer.reply.answer.reply.available true (.ref domain) body key result) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.query.code henv sorted
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial)
      (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  have bound : (Closure.close (.binder (domain.dependencyOrigin ordered) [body.dependencyOrigin ordered] [])
      (prior.realization.frame.leftDiagonal.dependencyEnvironment ordered)).cost ≤
      ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin ordered).weight * (1 + capacity) := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (answer.reply.bounded ordered) 1)
  have origins := certificate.piOriginsWith henv hscoped formed prior.closed
    (fun row admitted => row.reanchorGeneric initial henv below ordered domain (.piDomain location) body
      (.piBody location) bodyContext domainF bodyF prior.realization.frame.leftDiagonal bound
      prior.closed formed prior.realization.substitutions.left admitted)
    hu hv (.done _) resources
  exact certificate.piRowOfOrigins origins (List.mem_singleton_self _) (List.mem_singleton_self _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
