import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPiTypeReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteReplay

/-! Replay an application query through its finite whole-Pi history. Every
retained baseline frame has separate positive generation evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

/-- The incoming semantic Pi capability comes from the original application's
strictly smaller formation view. The history itself supplies only original
finite F/C/R edges, never a caller-provided type alignment. -/
theorem OriginalApplyPiHistory.replayRequest
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.Generated base commonCaps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : OriginalCaptureRealization left.graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (frameBound : environmentCost (frame.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (request : GeneratedApplicationPiRequest left.domain left.body left.hu left.hv env registry target
      locals (left.raw.comp commonLeft) available left.a true (profile : Profile n))
    (piF : OriginalCodeInductionAt env registry history.leftOrdered left.initial (.appPiFormation left.location)
      (Closure.close (left.node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost)
    (calls : history.whole.Calls base commonCaps limit)
    (scheduled : history.schedule < limit) :
    Nonempty (BoundedParameterReply base commonCaps
      ((VExpr.forallE left.A left.B).subst (left.raw.comp commonLeft)) right.display commonLeft commonRight
      (Profile.pi (left.A.subst (left.raw.comp commonLeft)) (left.B.subst (left.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost history.final)) := by
  obtain ⟨incoming⟩ := left.piRequestReply frame capped history.leftOrdered frameBound formed closed request piF
  exact history.whole.replay generated.whole henv hscoped formed calls
    (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled) incoming request.certificate.formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
