import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientTypeRouteGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The route and every retained actual semantic frame obey the same source
predicate. This is finite positive provenance, not an interpretation field. -/
structure RawGeneratedTypeRoute.SourceGenerated
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Prop where
  wellFormed : route.WellFormed
  ambient : route.Ambient
  sources : route.AllSources P
  frames : ∀ boxed ∈ route.frames, SourceCaptureGenerated P base caps commonLeft commonRight
    boxed.graph boxed.frame.realization.frame.raw

theorem RawGeneratedTypeRoute.SourceGenerated.ambientGenerated
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    (generated : route.SourceGenerated P base caps) : route.AmbientGenerated base caps :=
  ⟨generated.wellFormed, generated.ambient, fun boxed member => (generated.frames boxed member).ambientGenerated⟩

theorem RawGeneratedTypeRoute.SourceGenerated.mono
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    (generated : route.SourceGenerated P base caps) (implication : ∀ source, P source → Q source) :
    route.SourceGenerated Q base caps :=
  ⟨generated.wellFormed, generated.ambient, RawGeneratedTypeRoute.AllSources.mono route generated.sources implication,
    fun boxed member => (generated.frames boxed member).mono implication⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
