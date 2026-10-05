import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainExtraction

/-! A same-support domain comparison from two actual Pi formation views.
The empty-row query needs no argument, row, or inhabitant. Both source domain
certificates stay at their original occurrences. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichCert.domainOnly
    {support : Profile n}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (certificate : RichCert sourceEnv env U registry target domain locals σ true support footprint) :
    RichCert sourceEnv env U registry target (.pi hu hv domain body) locals σ true
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) footprint := by
  simpa only [List.append_nil] using RichCert.pi hu hv certificate PiGuard.literal .nil

theorem RichCodeTransfer.piDomainAlignment
    {left : EndpointState leftEnv U leftSource (.forallE A B) (.sort l)}
    {right : EndpointState rightEnv U rightSource (.forallE C D) (.sort r)}
    {leftDomain : EndpointState leftEnv U leftSource A (.sort u)}
    {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
    {rightDomain : EndpointState rightEnv U rightSource C (.sort u')}
    {rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lu : u.WF U) (lv : v.WF U) (ru : u'.WF U) (rv : v'.WF U)
    (leftRoute : PrefixRoute leftEnv U leftSource (.forallE A B) left (.pi lu lv leftDomain leftBody))
    (rightRoute : PrefixRoute rightEnv U rightSource (.forallE C D) right (.pi ru rv rightDomain rightBody))
    (coherence : RichCodeTransfer env U registry target left right
      leftLocals rightLocals σ τ leftAvailable rightAvailable)
    (certificate : RichCert leftEnv env U registry target leftDomain leftLocals σ true (support : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ _answer : RichCodeTransferResult env U registry target leftDomain rightDomain rightLocals σ τ
        rightAvailable true support,
      TypeConversion env U target (A.subst σ) (C.subst τ) := by
  obtain ⟨answer⟩ := coherence (.route leftRoute (certificate.domainOnly leftBody lu lv)) resources
  obtain ⟨domain⟩ := answer.certificate.piDomain ru rv rightRoute answer.resources
  have related := TypeRelated.literalPiDomain henv hscoped formed
    (by simpa only [subst] using answer.related)
  have path := TypeRelated.literalPiDomainPath henv formed
    (by simpa only [subst] using answer.related)
  exact ⟨⟨domain.footprint, domain.certificate, domain.resources, related⟩, path⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
