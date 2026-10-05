import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! Exact positive Pi row extraction with every named-head policy preserved.
The same selected row carries the original domain/body queries and binder pack;
there is no independent semantic witness or reanchoring in this step. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Strengthen `RichRows.rowCertificate` on the very same selected constructor
record. The domain query is unchanged, and the selected body is an actual child
of `rows`. The bound holds simultaneously for arbitrary, even nonmonotone,
head policies. -/
theorem RichRows.rowCertificate_headDepth
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      HEq row.domain domain ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨{ domainSupport := ambient
                domainFootprint := domainFootprint
                domain := domain
                domainAvailable := domainAvailable
                inputTyped := guard.inputTyped
                alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
                anchor := guard.anchor
                bodyFootprint := _
                body := body
                packed := _
                outside := _
                pack := pack
                covered := covered
                outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) },
        HEq.rfl, ?_⟩
      intro policy
      simp only [RichRows.headDepth]
      omega
    · obtain ⟨row, same, bounded⟩ := tail.rowCertificate_headDepth domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, same, ?_⟩
      intro policy
      have lower := bounded policy
      simp only [RichRows.headDepth]
      omega
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
