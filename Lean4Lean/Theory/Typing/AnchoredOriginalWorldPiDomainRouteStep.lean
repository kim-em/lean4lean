import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalPiTypeRouteSide
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- Whole-Pi history can be queried with empty rows. Therefore a domain
history introduces no additional original recursive call, even at empty q. -/
theorem AmbientBoundedParameterReply.piDomainStepWorld
    {base : OriginalCaptureBase env U registry target}
    (left right : OriginalPiTypeRouteSide U common)
    (leftBelow : left.sourceEnv ≤ env)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env}
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initialEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U finalEnvironment)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
    (transfer : ∀ {rank : Nat} {q : Profile rank} {origin : VExpr},
      ∀ reply : AmbientBoundedParameterReply base commonCaps origin left.display commonLeft commonRight q
        (environmentCost initialEnvironment),
      WorldParameterReplyData (P := P) leftControls leftWorld frontier reply →
      q.HasType (.sort true) →
      ∃ changed : AmbientBoundedParameterReply base commonCaps origin right.display commonLeft commonRight q
          (environmentCost finalEnvironment),
        Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier changed))
    (incoming : AmbientBoundedParameterReply base commonCaps start left.domainDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost initialEnvironment))
    (incomingData : WorldParameterReplyData (P := P) leftControls leftWorld frontier incoming)
    (sorted : profile.HasType (.sort true)) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start right.domainDisplay commonLeft commonRight profile
        (environmentCost finalEnvironment),
      Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier result) := by
  let prior := incoming.reply.answer.reply
  obtain ⟨fp, domainCode, domainReady, domainResources, _⟩ :=
    prior.query.code_controlled henv leftControls incomingData.query sorted
  let σ := left.raw.comp commonLeft
  let piCode := RichCert.pi (relevant := true) left.hu left.hv domainCode PiGuard.literal
    (RichRows.nil (body := left.body))
  let piQuery : RichGradedResult left.sourceEnv env U registry target left.display.node
      prior.locals σ prior.available (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) := {
    rank := n + 1, bound := Nat.le_refl _, raw := _
    footprint := fp ++ [], observation := .code piCode
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by simpa only [List.append_nil] using domainResources
    live := Profile.HasType.sortable_live piCode.formed }
  let piReply : BoundedGeneratedQueryReply base commonCaps left.display commonLeft commonRight
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) (environmentCost initialEnvironment) := {
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
  let lifted : AmbientBoundedParameterReply base commonCaps
      (left.display.sourceExpression.subst σ) left.display commonLeft commonRight
      (Profile.pi (left.A.subst σ) (left.B.subst σ.lift) profile []) (environmentCost initialEnvironment) := {
    reply := piReply
    related := by simpa only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence,
      subst_subst, subst, ← Subst.comp_lift] using piRelated
    path := by simp only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence,
      subst_subst]; exact .refl
    generation := incoming.generation }
  have piReady : ControlledStoredQuery leftControls frontier (.observation piQuery.observation) := by
    refine ⟨.code (.pi left.hu left.hv domainCode PiGuard.literal .nil domainReady.annotation .nil), ?_, ?_⟩
    · intro control active
      simp only [piQuery, StoredOriginalQuery.headDepth, RichObs.headDepth, piCode,
        RichCert.headDepth, RichRows.headDepth, Nat.max_zero]
      exact domainReady.within control active
    · change EquationWorldClosureOrder.Sponsored frontier (domainReady.annotation.worlds ++ [])
      rw [List.append_nil]
      exact domainReady.sponsored
  let liftedData : WorldParameterReplyData (P := P) leftControls leftWorld frontier lifted := {
    generation := incomingData.generation
    hereditary := incomingData.hereditary
    replayable := incomingData.replayable
    controlled := incomingData.controlled
    compatible := incomingData.compatible
    query := piReady
    covered := incomingData.covered }
  obtain ⟨changed, ⟨changedData⟩⟩ := transfer lifted liftedData piCode.formed
  obtain ⟨outFp, outCode, outReady, outResources, _⟩ :=
    changed.reply.answer.reply.query.code_controlled henv rightControls changedData.query piCode.formed
  obtain ⟨outDomain, domainReady, _, _⟩ :=
    outCode.piDomain_controlled right.hu right.hv (.done _) outResources outReady
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
    path := ?_
    generation := changed.generation }, ⟨{
      generation := changedData.generation
      hereditary := changedData.hereditary
      replayable := changedData.replayable
      controlled := changedData.controlled
      compatible := changedData.compatible
      query := domainReady.code
      covered := changedData.covered }⟩⟩
  · have initialRelated : TypeRelated env U registry target start (left.A.subst σ) profile := by
      simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using incoming.related
    have result := initialRelated.trans henv (TypeRelated.literalPiDomain henv hscoped formed whole)
    simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using result
  · have initialPath : TypeConversion env U target start (left.A.subst σ) := by
      simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using incoming.path
    have result := initialPath.trans (TypeRelated.literalPiDomainPath henv formed whole)
    simpa only [OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
