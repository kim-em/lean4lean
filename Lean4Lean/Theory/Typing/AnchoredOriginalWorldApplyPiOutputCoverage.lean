import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiPackedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGroupCoverage

/-! The connected packed application returns one actual bounded parameter
reply. Its selected group is covered by the fixed original history envelope;
queries, generation and hereditary replayability remain the same witnesses. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

variable
  {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}
  {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
  {field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType}
  {major : EndpointRef left.sourceEnv U left.source majorExpression majorType}
  {base : OriginalCaptureBase env U registry target}
  {strata : EquationStratification env} {P : VEnv → Prop}
  {sourceControls : OriginalWorldControls strata left.sourceEnv}
  {headerControls : OriginalWorldControls strata right.sourceEnv}
  {frontier : List (World strata.rules.length)}
  {initialProvenance : WorldEnvironmentProvenance strata U ownerInitial}
  {sourceWorld : WorldEnvironmentProvenance strata U
    (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)}
  {priorWorld : WorldEnvironmentProvenance strata U history.final}
  {wholeInputs : history.whole.WorldInputs strata}

/-- The actual selected generation is covered by the fixed original output
history. This uses the same whole reply's capacity and hereditary coverage. -/
theorem WorldApplyPiReplayResult.outputCovered
    (answer : WorldApplyPiReplayResult history field major ownerInitial base commonCaps profile P
      sourceControls headerControls frontier initialProvenance sourceWorld priorWorld wholeInputs) :
    Covered (@EquationControlMeasure.Less strata.rules.length) answer.world.worlds
      (history.outputWorld field major sourceControls headerControls initialProvenance sourceWorld priorWorld wholeInputs).worlds := by
  rw [answer.worlds, WorldEnvironmentProvenance.worlds_append]
  apply Covered.merge
  · have same :
        (WorldEnvironmentProvenance.groupHistory field major history.rightDomain sourceControls headerControls
          initialProvenance priorWorld (answer.seedHistory.route.worldReserve answer.seedData.inputs)).worlds =
        (history.outputWorld field major sourceControls headerControls initialProvenance sourceWorld priorWorld wholeInputs).worlds := by
      simp only [OriginalApplyPiHistory.outputWorld, WorldEnvironmentProvenance.groupHistory,
        WorldEnvironmentProvenance.worlds_append]
      rw [answer.seedWorlds]
    rw [same]
    exact Covered.refl _
  · exact WorldEnvironmentProvenance.group_covered_history sourceControls headerControls initialProvenance
      answer.wholeWorld.environment priorWorld answer.entries
      (history.argumentSeedWorld sourceControls headerControls sourceWorld priorWorld wholeInputs)
      (answer.whole.reply.bounded headerControls.ordered) answer.wholeCovered

/-- The semantic result, query, selected frame and controls are those of the
connected packed replay; only the fixed output envelope is now discharged. -/
noncomputable def WorldApplyPiReplayResult.boundedWorldReply
    (answer : WorldApplyPiReplayResult history field major ownerInitial base commonCaps profile P
      sourceControls headerControls frontier initialProvenance sourceWorld priorWorld wholeInputs) :
    WorldParameterReplyData (P := P) headerControls
      (history.outputWorld field major sourceControls headerControls initialProvenance sourceWorld priorWorld wholeInputs)
      frontier answer.toAmbientApplyPiReplayResult.boundedReply where
  generation := answer.world
  hereditary := answer.hereditary
  replayable := answer.replayable
  controlled := answer.controlled
  compatible := answer.compatible
  query := answer.queryReady
  covered := answer.outputCovered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
