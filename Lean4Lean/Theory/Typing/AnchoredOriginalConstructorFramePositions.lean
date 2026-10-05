import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureRealization

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Express the same actual frame using equal telescope-local positions.
The generated tree and every closure environment remain unchanged. -/
theorem OriginalCaptureRealization.changePositions
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalCaptureRealization graph env registry target locals left right available)
    (generated : SourceCaptureGenerated P base caps left right graph frame.frame.raw)
    (positions : locals = nextLocals) :
    ∃ next : OriginalCaptureRealization graph env registry target nextLocals left right available,
      SourceCaptureGenerated P base caps left right graph next.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered = frame.frame.dependencyEnvironment ordered := by
  cases positions
  exact ⟨frame, generated, fun _ => rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
