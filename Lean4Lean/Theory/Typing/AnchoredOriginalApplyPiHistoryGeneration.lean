import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

structure OriginalApplyPiHistory.Generated
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps) : Prop where
  source : CappedCaptureGenerated base commonCaps commonLeft commonRight
    left.graph history.sourceFrame.realization.frame.raw
  header : CappedCaptureGenerated base commonCaps commonLeft commonRight
    right.graph history.headerFrame.realization.frame.raw
  whole : history.whole.Generated base commonCaps

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
