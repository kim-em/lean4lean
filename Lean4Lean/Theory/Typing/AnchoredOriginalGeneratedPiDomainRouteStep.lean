import Lean4Lean.Theory.Typing.AnchoredOriginalPiTypeRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedAssignedComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainAlignment
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Whole-Pi history can be queried with empty rows. Therefore a domain
history introduces no additional original recursive call, even at empty q. -/
theorem BoundedParameterReply.piDomainStep
    {base : OriginalCaptureBase env U registry target}
    (left right : OriginalPiTypeRouteSide U common)
    (leftBelow : left.sourceEnv ≤ env)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (transfer : ∀ {rank : Nat} {q : Profile rank} {origin : VExpr},
      BoundedParameterReply base commonCaps origin left.display commonLeft commonRight q initial →
      q.HasType (.sort true) →
      Nonempty (BoundedParameterReply base commonCaps origin right.display commonLeft commonRight q final))
    (incoming : BoundedParameterReply base commonCaps start left.domainDisplay commonLeft commonRight
      (profile : Profile n) initial)
    (sorted : profile.HasType (.sort true)) :
    Nonempty (BoundedParameterReply base commonCaps start right.domainDisplay commonLeft commonRight profile final) := by
  let prior := incoming.reply.answer.reply
  obtain ⟨fp, ⟨domainCode⟩, domainResources⟩ := prior.query.code henv sorted
  let σ := left.raw.comp commonLeft
  let piCode := domainCode.domainOnly left.body left.hu left.hv
  let piQuery : RichGradedResult left.sourceEnv env U registry target left.display.node
      prior.locals σ prior.available (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) := {
    rank := n + 1, bound := Nat.le_refl _, raw := _
    footprint := fp, observation := .code piCode
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := domainResources
    live := Profile.HasType.sortable_live piCode.formed }
  let piReply : BoundedGeneratedQueryReply base commonCaps left.display commonLeft commonRight
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) initial := {
    answer := {
      reply := { prior with query := piQuery }
      capped := incoming.reply.answer.capped }
    bounded := incoming.reply.bounded }
  have originalDomain := left.domain.sound.defeq.mono leftBelow
  have hA := originalDomain.subst henv prior.realization.substitutions.left formed
  have hB := (left.body.sound.defeq.mono leftBelow).subst henv
    (prior.realization.substitutions.left.lift henv originalDomain) ⟨formed, _, hA⟩
  have domainRelated : TypeRelated env U registry target (left.A.subst σ) (left.A.subst σ) profile := by
    simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst]
      using (TypeRelated.symm henv sorted.wf_value incoming.related).left_diagonal
  have piRelated : TypeRelated env U registry target
      (.forallE (left.A.subst σ) (left.B.subst σ.lift))
      (.forallE (left.A.subst σ) (left.B.subst σ.lift))
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) := by
    apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
      .refl .refl .refl .refl domainRelated
    · intro key output member; cases member
    · intro key output member; cases member
  let lifted : BoundedParameterReply base commonCaps
      (left.display.sourceExpression.subst σ) left.display commonLeft commonRight
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) initial := {
    reply := piReply
    related := by simpa only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence,
      subst_subst, subst, ← Subst.comp_lift] using piRelated
    path := by simp only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence,
      subst_subst]; exact .refl }
  obtain ⟨changed⟩ := transfer lifted piCode.formed
  obtain ⟨outFp, ⟨outCode⟩, outResources⟩ := changed.reply.answer.reply.query.code henv piCode.formed
  obtain ⟨outDomain⟩ := outCode.piDomain right.hu right.hv (.done _) outResources
  let selected := changed.reply.answer.reply
  let query : RichGradedResult right.sourceEnv env U registry target right.domainDisplay.node
      selected.locals (right.raw.comp commonLeft) selected.available profile := {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := outDomain.footprint, observation := .code outDomain.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := outDomain.resources
    live := Profile.HasType.sortable_live sorted }
  have whole : TypeRelated env U registry target
      (.forallE (left.A.subst σ) (left.B.subst σ.lift))
      (.forallE (right.A.subst (right.raw.comp commonLeft)) (right.B.subst (right.raw.comp commonLeft).lift))
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) := by
    simpa only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence, subst_subst, subst, ← Subst.comp_lift]
      using changed.related
  refine ⟨{
    reply := {
      answer := { reply := { selected with query := query }, capped := changed.reply.answer.capped }
      bounded := changed.reply.bounded }
    related := ?_
    path := ?_ }⟩
  · have initialRelated : TypeRelated env U registry target start (left.A.subst σ) profile := by
      simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using incoming.related
    have result := initialRelated.trans henv (TypeRelated.literalPiDomain henv hscoped formed whole)
    simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using result
  · have initialPath : TypeConversion env U target start (left.A.subst σ) := by
      simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using incoming.path
    have result := initialPath.trans (TypeRelated.literalPiDomainPath henv formed whole)
    simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
