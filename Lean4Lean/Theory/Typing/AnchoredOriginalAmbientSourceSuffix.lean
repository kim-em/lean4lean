import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedSourceSuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- Repeated graph tails follow the actual stored original context spine.
Every step uses the computed full suffix, retaining merged resources. -/
theorem AmbientCaptureGenerated.sourceSuffix
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tailContext : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tailContext domain)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals
      (raw.comp commonLeft) (raw.comp commonRight) available)
    (capped : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw) :
    ∃ result : CappedSourceSuffix (common := common) base commonCaps commonLeft commonRight raw locals available location,
      AmbientCaptureGenerated base commonCaps commonLeft commonRight result.graph result.frame.raw ∧
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (result.frame.dependencyEnvironment ordered)).cost ≤ environmentCost (frame.dependencyEnvironment ordered) := by
  induction location generalizing locals raw available with
  | here =>
    exact ⟨⟨raw.tail, .tail graph, frame.fullTail.tailLocals, frame.fullTail.frame,
      .tail capped.capped frame.valid, rfl, frame.fullTail.positions⟩,
      .tail capped frame.valid, frame.fullTail_domain_bound⟩
  | @there source context tailSource tailContext A level domain B otherLevel newDomain location ih =>
    obtain ⟨answer, answerGenerated, bound⟩ := ih frame.fullTail.frame (.tail capped frame.valid)
    have rawEq : answer.raw = fun i => raw (i + (location.prefix.length + 1 + 1)) := by
      calc
        answer.raw = _ := answer.raw_eq
        _ = _ := by funext i; congr 1
    have positions := (congrArg Locals.push answer.positions).trans frame.fullTail.positions
    have changedAvailable : (fun i => available (i + (location.prefix.length + 1) + 1)) =
        (fun i => available (i + (location.prefix.length + 1 + 1))) := by
      funext i
      congr 1
    let nextFrame := changedAvailable ▸ answer.frame
    have nextCapped : AmbientCaptureGenerated base commonCaps commonLeft commonRight answer.graph nextFrame.raw :=
      by simpa only [nextFrame] using answerGenerated
    refine ⟨⟨answer.raw, answer.graph, answer.locals, nextFrame, nextCapped.capped, rawEq, positions⟩, nextCapped, ?_⟩
    intro ordered
    have sameEnvironment : nextFrame.dependencyEnvironment ordered = answer.frame.dependencyEnvironment ordered := by
      dsimp only [nextFrame]
    rw [sameEnvironment]
    exact Nat.le_trans (bound ordered) (frame.fullTail_environment_le ordered)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
