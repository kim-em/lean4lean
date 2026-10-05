import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiObservationReindex

/-! Preserve an entire rich query when exposing its actual original Pi
head. This is needed after declaration normalization, whose retained
equality endpoint can have a nonsort assigned expression. No typing is
reconstructed: the domain, body and route are the actual original ones. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Peeling keeps all requested rows and output actions, not only the
domain-only request. The destination is the computed natural Pi endpoint. -/
theorem RichCert.atOriginalPiHead
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body))
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available) :
    ∃ required,
      Nonempty (RichCert sourceEnv env U registry target (.pi hu hv domain body)
        locals σ relevant profile required) ∧ required.Available available := by
  obtain ⟨answer⟩ := (RichObs.code query).replayOriginalPi henv hscoped formed
    (destination := .pi hu hv domain body) (domain := domain) (body := body)
    (fun domainQuery guard rows domainResources rowResources =>
      ⟨(RichCert.pi hu hv domainQuery guard rows).graded
        (fun i need member => (List.mem_append.mp member).elim
          (domainResources i need) (rowResources i need))⟩)
    hu hv route resources
  exact answer.code henv query.formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
