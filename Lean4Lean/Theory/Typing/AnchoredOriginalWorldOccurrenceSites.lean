import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrence

/-! Actual paired occurrence sites and exact prefix-route environment transport.
These constructors preserve existing annotations and do not traverse or reset
nested canonical-query provenance. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def OriginalRichOccurrenceFrame.worldSite
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered)) :
    WorldQuerySite (registry := registry) (target := target) strata node locals σ :=
  ⟨location.contextDerivation initialContext, .ofLocation location initialContext, τ, available,
    occurrence.frame, ⟨controls, environment⟩⟩

theorem OriginalRichOccurrenceFrame.route_worldEnvironment
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U occurrenceSource expression assigned}
    {last : EndpointState sourceEnv U occurrenceSource expression natural}
    {location : Located root first}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (route : PrefixRoute sourceEnv U occurrenceSource expression first last) :
    (occurrence.route route).frame.dependencyEnvironment ordered = occurrence.frame.dependencyEnvironment ordered := by
  induction route with
  | done => rfl
  | expose reference rest ih =>
      exact ih (location := .expose location) ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩
  | convert plan term rest ih =>
      exact ih (location := .convertTerm location) ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩

noncomputable def OriginalRichOccurrenceFrame.routeWorld
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U occurrenceSource expression assigned}
    {last : EndpointState sourceEnv U occurrenceSource expression natural}
    {location : Located root first}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (route : PrefixRoute sourceEnv U occurrenceSource expression first last)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered)) :
    WorldEnvironmentProvenance strata U ((occurrence.route route).frame.dependencyEnvironment controls.ordered) :=
  occurrence.route_worldEnvironment route ▸ environment

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
