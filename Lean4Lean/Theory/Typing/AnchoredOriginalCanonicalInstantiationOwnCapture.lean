import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaInstantiation
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentValue
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Produce a query-owned instantiation from the operative application
capture path. The packed request retains the actual argument observer and
the domain certificate recovered from the selected captured-body frame.
The only new comparison is between that original application domain and the
argument's independent original type formation, strictly below the actual
application. The result adds no captured environment entry. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument resultNode)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

/-- Recover the assigned certificate for an actual own-capture argument.
This call uses the existing generated result-to-body request; it neither
invents an argument query from semantics nor retypes the declared domain at
the argument's unrelated original endpoint. The identity-graph reply freezes
back into exactly the original caller resources. -/
theorem GeneratedApplicationPackedRequest.canonicalInstantiation
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    {ambient : Profile packed.request.rank} {rows : List (Key packed.request.rank × Profile packed.request.rank)}
    (parent : CanonicalDeltaElimination env U registry target strata source σ (.forallE A B)
      relevant (.pi prototypeDomain prototypeBody ambient rows) parentFootprint)
    (selected : (packed.request.key, raiseProfile packed.request.rank packed.request.bound profile) ∈ rows)
    (parentResources : parentFootprint.Available available)
    (formationR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationDomainDisplay (frame := frame) (substitutions := substitutions))
      (applicationArgumentFormationDisplay (frame := frame) (substitutions := substitutions))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument resultNode hu hv location frame ordered)) :
    ∃ recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant
        (raiseProfile packed.request.rank packed.request.bound profile),
      recipe.footprint.Available available ∧
      HEq recipe.query packed.argumentQuery.observation ∧
      recipe.parent.depth = parent.depth ∧
      recipe.support = packed.request.support ∧
      ∃ reply : BoundedGeneratedQueryReply (frame.captureBase substitutions)
          (frame.captureBase substitutions).initialCaps
          (applicationArgumentFormationDisplay (frame := frame) (substitutions := substitutions))
          σ τ packed.request.support (environmentCost (frame.dependencyEnvironment ordered)),
        ∀ policy, recipe.certificate.headDepth policy ≤
          reply.answer.freezeBase.observation.headDepth policy := by
  let base := frame.captureBase substitutions
  obtain ⟨reply⟩ := formationR base.identityRealization base.identityCapped closed
    base.identityRealization base.identityCapped closed
    (applicationArgumentFormation_schedule (frame := frame))
    (.code packed.domainCertificate) packed.domainResources
  obtain ⟨supportFootprint, certificate, supportResources, certificateDepth⟩ :=
    reply.answer.freezeBase.code_headDepth henv packed.domainCertificate.formed
  let recipe : CanonicalDeltaInstantiation sourceEnv env U registry target strata argument locals σ B relevant
      (raiseProfile packed.request.rank packed.request.bound profile) := {
    prototypeDomain := prototypeDomain
    prototypeBody := prototypeBody
    ambient := ambient
    rows := rows
    key := packed.request.key
    parentFootprint := parentFootprint
    parent := parent
    selected := selected
    anchor := packed.request.anchor_eq
    queryRank := packed.argumentQuery.rank
    queryBound := packed.argumentQuery.bound
    rawInput := packed.argumentQuery.raw
    argumentFootprint := packed.argumentQuery.footprint
    query := packed.argumentQuery.observation
    adapter := packed.argumentQuery.adapter
    support := packed.request.support
    supportFootprint := supportFootprint
    certificate := certificate
    typed := packed.inputTyped }
  refine ⟨recipe, ?_, HEq.rfl, rfl, rfl, reply, certificateDepth⟩
  intro index need member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact parentResources index need member
    · exact packed.argumentQuery.resources index need member
  · exact supportResources index need member

end
end Lean4Lean.AnchoredSource.Adapted
