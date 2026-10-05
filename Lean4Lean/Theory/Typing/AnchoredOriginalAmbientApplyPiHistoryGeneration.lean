import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientTypeRouteGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistoryGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

structure OriginalApplyPiHistory.AmbientGenerated
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps) : Prop where
  source : AmbientCaptureGenerated base commonCaps commonLeft commonRight
    left.graph history.sourceFrame.realization.frame.raw
  header : AmbientCaptureGenerated base commonCaps commonLeft commonRight
    right.graph history.headerFrame.realization.frame.raw
  whole : history.whole.AmbientGenerated base commonCaps

theorem OriginalApplyPiHistory.AmbientGenerated.generated
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (generated : history.AmbientGenerated base caps) : history.Generated base caps :=
  ⟨generated.source.capped, generated.header.capped, generated.whole.generated⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
