import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiHead

/-! Full queried normalization retains every Pi row for the dependent
family-prefix successor. The sorted destination is the actual natural Pi
inside the original normalization proof, never a retyped equality endpoint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private def castCertificate
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (same : expression = other) :
    RichCert sourceEnv env U registry target (node.cast same rfl) locals σ relevant profile footprint := by
  cases same
  exact certificate

/-- The two callbacks are at the same exact retained roots as the
domain-only consumer. All rows survive into the actual native Pi query. -/
theorem RichCodeTransferResult.normalizedPiAnswer
    {left : EndpointState leftEnv U leftSource expression (.sort leftLevel)}
    {header : EndpointState headerEnv U [] headerExpression (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (nonempty : 0 < info.nparams)
    (sameSource : headerExpression = packet.origin.family.type.instL levels)
    (answer : RichCodeTransferResult env U registry target left header [] σ seed (fun _ => [])
      relevant profile)
    (reindex : RichObs headerEnv env U registry target header [] seed profile answer.footprint →
      answer.footprint.Available (fun _ => []) →
      Nonempty (RichGradedResult packet.origin.base env U registry target
        (.ref (.left packet.instantiated.normalization)) [] seed (fun _ => []) profile))
    (normalizationF : ∀ {footprint : Footprint},
      RichObs packet.origin.base env U registry target (.ref (.left packet.instantiated.normalization))
        [] seed profile footprint →
      footprint.Available (fun _ => []) →
      Nonempty (OriginalEqualityQueryResult packet.instantiated.normalization env registry target
        [] seed seed (fun _ => []) profile)) :
    let selectedPi := normalizedFamilyPrefix packet nonempty
    Nonempty (RichCodeTransferResult env U registry target left
      (.pi selectedPi.selected.view.domainWF selectedPi.selected.view.bodyWF
        selectedPi.selected.view.domain selectedPi.selected.view.body)
      [] σ seed (fun _ => []) relevant profile) := by
  dsimp only
  obtain ⟨reindexed⟩ := reindex (.code answer.certificate) answer.resources
  obtain ⟨_, ⟨input⟩, resources⟩ := reindexed.code henv answer.certificate.formed
  obtain ⟨normalized⟩ := normalizationF (.code input) resources
  obtain ⟨_, ⟨certificate⟩, resources, code⟩ := normalized.code henv hscoped formed input.formed
  let selectedPi := normalizedFamilyPrefix packet nonempty
  obtain ⟨footprint, ⟨head⟩, available⟩ := (castCertificate certificate selectedPi.shape).atOriginalPiHead
    henv hscoped formed selectedPi.selected.view.domainWF selectedPi.selected.view.bodyWF
    selectedPi.selected.route resources
  refine ⟨⟨footprint, head, available, ?_⟩⟩
  change TypeRelated env U registry target (expression.subst σ)
    ((VExpr.forallE selectedPi.domainExpression selectedPi.bodyExpression).subst seed) profile
  rw [← selectedPi.shape]
  apply answer.related.trans henv
  simpa only [sameSource] using code

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
