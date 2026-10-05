import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameSuffix

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A source suffix is generated from the very same base; it does not
pretend to be an identity graph with the larger base's local positions. -/
structure CappedSourceSuffix
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    (base : OriginalCaptureBase env U registry target)
    (commonCaps : CaptureCaps) {common : List VExpr} (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (originalRaw : Subst) (originalLocals : List Nat) (originalAvailable : Valuation)
    {tailContext : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tailContext domain) where
  raw : Subst
  graph : OriginalCaptureMap (common := common) tailContext raw
  locals : List Nat
  frame : OriginalRichFrame sourceEnv env U registry target tailContext locals
    (raw.comp commonLeft) (raw.comp commonRight)
    (fun i => originalAvailable (i + (location.prefix.length + 1)))
  capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw
  raw_eq : raw = fun i => originalRaw (i + (location.prefix.length + 1))
  positions : pushedLocals (location.prefix.length + 1) locals = originalLocals

/-- Repeated graph tails follow the actual stored original context spine.
Every step uses the computed full suffix, retaining merged resources. -/
theorem CappedCaptureGenerated.sourceSuffix
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tailContext : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tailContext domain)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals
      (raw.comp commonLeft) (raw.comp commonRight) available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw) :
    ∃ result : CappedSourceSuffix (common := common) base commonCaps commonLeft commonRight raw locals available location,
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (result.frame.dependencyEnvironment ordered)).cost ≤ environmentCost (frame.dependencyEnvironment ordered) := by
  induction location generalizing locals raw available with
  | here =>
    exact ⟨⟨raw.tail, .tail graph, frame.fullTail.tailLocals, frame.fullTail.frame,
      .tail capped frame.valid, rfl, frame.fullTail.positions⟩, frame.fullTail_domain_bound⟩
  | @there source context tailSource tailContext A level domain B otherLevel newDomain location ih =>
    obtain ⟨answer, bound⟩ := ih frame.fullTail.frame (.tail capped frame.valid)
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
    have nextCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight answer.graph nextFrame.raw :=
      by simpa only [nextFrame] using answer.capped
    refine ⟨⟨answer.raw, answer.graph, answer.locals, nextFrame, nextCapped, rawEq, positions⟩, ?_⟩
    intro ordered
    have sameEnvironment : nextFrame.dependencyEnvironment ordered = answer.frame.dependencyEnvironment ordered := by
      dsimp only [nextFrame]
    rw [sameEnvironment]
    exact Nat.le_trans (bound ordered) (frame.fullTail_environment_le ordered)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
