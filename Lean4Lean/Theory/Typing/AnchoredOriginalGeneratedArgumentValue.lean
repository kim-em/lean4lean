import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentPack

/-! The advertised key input is interpreted at its computed app-domain
support. Raw argument F supplies value semantics; exact original formation R
supplies the same support at the argument's retained assigned-type occurrence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

/-- Both original occurrences fit below the actual application, independent
of the requested profile and of the size of the computed argument observer. -/
theorem applicationArgumentFormation_schedule :
    richSchedule .expressionReindex
      ((Closure.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
       (Closure.close (argument.typeFormation.node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) <
    applicationReplayLimit initial domain body function argument result hu hv location frame ordered := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_left (argument.typeFormation_dependency_cost_le ordered _) _)
  change (domain.dependencyOrigin ordered).weight * _ + (argument.dependencyOrigin ordered).weight * _ < _
  rw [← Nat.add_mul]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  have positive := (body.dependencyOrigin ordered).weight_pos
  have covered := Nat.mul_le_mul_right (1 + (argument.dependencyOrigin ordered).weight +
    (domain.dependencyOrigin ordered).weight) positive
  simp only [Nat.one_mul] at covered
  simp only [EndpointState.dependencyOrigin, capturedApplicationOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- The outgoing value uses the requested support, never the raw argument
answer's unrelated natural support. Only two fixed original child clauses
are invoked, with their actual closure decreases. -/
theorem GeneratedApplicationPackedRequest.argumentValueExact
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (argumentF : OriginalComputationalInductionAt env registry ordered initial (.appArgument location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (formationR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationDomainDisplay (frame := frame) (substitutions := substitutions))
      (applicationArgumentFormationDisplay (frame := frame) (substitutions := substitutions))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument result hu hv location frame ordered)) :
    ∃ value : RichSupportedValue sourceEnv env U registry target argument locals σ τ available packed.request.key.input,
      value.support = packed.request.support := by
  let base := frame.captureBase substitutions
  have reserve := application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
    (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
    (frame.dependencyEnvironment ordered)
  obtain ⟨rawAnswer⟩ := argumentF target locals σ τ available frame
    (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
    closed formed substitutions packed.argumentQuery.observation packed.argumentQuery.resources
  obtain ⟨replayed⟩ := formationR base.identityRealization base.identityCapped closed
    base.identityRealization base.identityCapped closed
    (applicationArgumentFormation_schedule (frame := frame))
    (.code packed.domainCertificate) packed.domainResources
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := replayed.answer.freezeBase.code henv packed.domainCertificate.formed
  have atRaised := packed.argumentQuery.adapter.termMap henv hscoped formed
    (Profile.HasType.raise packed.argumentQuery.bound packed.inputTyped)
    (packed.domainRelated.raise henv packed.argumentQuery.bound) rawAnswer.related
  have related := lowerProfile.related packed.argumentQuery.bound henv formed atRaised
  rw [OriginalFactorCut.lower_raised] at related
  exact ⟨{
    support := packed.request.support, footprint := footprint, certificate := certificate, resources := resources
    typed := packed.inputTyped, related := related, typeCode := packed.domainRelated }, rfl⟩
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
