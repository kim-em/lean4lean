import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentValue

/-! The advertised key input is interpreted at its computed app-domain
support. Raw argument F supplies value semantics; exact original formation R
supplies the same support at the argument's retained assigned-type occurrence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

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

include substitutions

/-- The outgoing value uses the requested support, never the raw argument
answer's unrelated natural support. Only two fixed original child clauses
are invoked, with their actual closure decreases. -/
theorem GeneratedApplicationPackedRequest.argumentValueAmbient
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit) :
    ∃ value : RichSupportedValue sourceEnv env U registry target argument locals σ τ available packed.request.key.input,
      value.support = packed.request.support := by
  let base := frame.captureBase substitutions
  have reserve := application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
    (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
    (frame.dependencyEnvironment ordered)
  have smaller : (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve
  have scheduled := Nat.lt_of_lt_of_le (richSchedule_strict smaller .fundamental .fundamental) budget
  obtain ⟨rawAnswer⟩ := bank.computational ordered ambient.below initial (.appArgument location)
    target locals σ τ available frame ambient scheduled
    closed formed substitutions packed.argumentQuery.observation packed.argumentQuery.resources
  obtain ⟨replayed⟩ := bank.observation base base.initialCaps
    (applicationDomainDisplay (frame := frame) (substitutions := substitutions))
    (applicationArgumentFormationDisplay (frame := frame) (substitutions := substitutions))
    σ τ ordered ordered base.identityRealization (.identity ambient) closed
    base.identityRealization (.identity ambient) closed
    (Nat.lt_of_lt_of_le (applicationArgumentFormation_schedule (frame := frame)) budget)
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
