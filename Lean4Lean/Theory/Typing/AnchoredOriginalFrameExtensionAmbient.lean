import Lean4Lean.Theory.Typing.AnchoredOriginalFrameExtension
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Traversing actual original binders cannot introduce an unrelated source
world into an occurrence frame. -/
theorem OriginalFrameExtension.ambient
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension base frame) (ambient : base.Ambient) : frame.Ambient := by
  induction extension with
  | refl => exact ambient
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨ambient.below, ih⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
