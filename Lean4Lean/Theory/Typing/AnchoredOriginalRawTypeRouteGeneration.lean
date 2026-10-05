import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! Structural validation and positive evidence for the concrete original
frame leaves of a raw type history. No semantic replay or query callback is
stored in this evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

/-- Validate the exact output reserve and retain the route's actual initial
frames. This does not quantify over future queries or provide an alignment. -/
structure RawGeneratedTypeRoute.Generated
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps) : Prop where
  wellFormed : route.WellFormed
  frames : ∀ boxed ∈ route.frames, CappedCaptureGenerated base commonCaps commonLeft commonRight
    boxed.graph boxed.frame.realization.frame.raw

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
