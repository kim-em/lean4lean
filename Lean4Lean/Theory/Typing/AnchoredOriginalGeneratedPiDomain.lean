import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterEquality
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainAlignment

/-! The later family-prefix comparison must return its selected frame.
An exact empty-row Pi query then yields the next domain in THAT frame,
including when the requested domain profile is empty. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def parameterPiDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (provenance : EndpointProvenance context (.pi hu hv (.ref domain) body)) :
    OriginalNestedDisplay U common ((VExpr.forallE A B).subst raw) (.sort (.imax u v)) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := .forallE A B
  sourceType := .sort (.imax u v)
  context := context
  node := .pi hu hv (.ref domain) body
  provenance := provenance
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

/-- Native assigned-C need not predict the declaration valuation. Its
returned Pi answer contains the exact next-domain certificate at the same
returned frame; domain extraction introduces no new recursive call. -/
theorem BoundedParameterReply.piDomain
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation rightEnv U rightSource}
    (graph : OriginalCaptureMap (common := common) context raw)
    (ru : u'.WF U) (rv : v'.WF U)
    (rightDomain : EndpointRef rightEnv U rightSource C (.sort u'))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
    (rightProvenance : EndpointProvenance context (.pi ru rv (.ref rightDomain) rightBody))
    (domainProvenance : EndpointProvenance context (.ref rightDomain))
    {leftDomain : EndpointState leftEnv U leftSource A (.sort u)}
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (lu : u.WF U) (lv : v.WF U)
    (certificate : RichCert leftEnv env U registry target leftDomain leftLocals σ true
      (support : Profile n) footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : BoundedParameterReply base commonCaps (.forallE (A.subst σ) (B.subst σ.lift))
      (parameterPiDisplay graph ru rv rightDomain rightBody rightProvenance) commonLeft commonRight
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) capacity) :
    ∃ result : BoundedParameterReply base commonCaps (A.subst σ)
        (graph.parameterCellDisplay rightDomain domainProvenance) commonLeft commonRight support capacity,
      result.reply.answer.reply.available = answer.reply.answer.reply.available ∧
      result.reply.answer.reply.locals = answer.reply.answer.reply.locals := by
  let prior := answer.reply.answer.reply
  obtain ⟨piFootprint, ⟨piCode⟩, piResources⟩ := prior.query.code henv
    (certificate.domainOnly leftBody lu lv).formed
  obtain ⟨domain⟩ := piCode.piDomain ru rv (.done _) piResources
  have bridge : TypeRelated env U registry target
      (.forallE (A.subst σ) (B.subst σ.lift))
      (.forallE (C.subst (raw.comp commonLeft)) (D.subst (raw.comp commonLeft).lift))
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) := by
    simpa only [subst_subst, subst, Subst.comp_lift] using answer.related
  have related := TypeRelated.literalPiDomain henv hscoped formed bridge
  have path := TypeRelated.literalPiDomainPath henv formed bridge
  let query : RichGradedResult rightEnv env U registry target (.ref rightDomain)
      prior.locals (raw.comp commonLeft) prior.available support := {
    rank := n, bound := Nat.le_refl _, raw := support
    footprint := domain.footprint, observation := .code domain.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := domain.resources
    live := Profile.HasType.sortable_live certificate.formed }
  exact ⟨{
    reply := {
      answer := {
        reply := {
          locals := prior.locals, available := prior.available
          realization := prior.realization, generated := prior.generated
          query := query, closed := prior.closed }
        capped := answer.reply.answer.capped }
      bounded := answer.reply.bounded }
    related := by simpa only [subst_subst] using related
    path := by simpa only [subst_subst] using path }, rfl, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
