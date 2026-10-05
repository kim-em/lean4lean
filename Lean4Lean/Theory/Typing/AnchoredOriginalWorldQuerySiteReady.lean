import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOccurrenceSites
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient

/-! Executable original opening sites. `Ready` does not assert that an arbitrary
site belongs to its surrounding caller: native openings below are constructed
from the caller's exact occurrence, including its right substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure WorldQuerySite.Ready
    {strata : EquationStratification env}
    {node : EndpointState sourceEnv U source expression assigned}
    (site : WorldQuerySite (registry := registry) (target := target) strata node locals σ)
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint) : Prop where
  below : sourceEnv ≤ env
  ambient : site.frame.Ambient
  substitutions : Ctx.SubstEq env U target σ site.right source
  closed : site.available.AtomClosed
  resources : footprint.Available site.available

theorem OriginalRichOccurrenceFrame.worldSite_ready
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (below : sourceEnv ≤ env) (ambient : occurrence.frame.Ambient)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    (occurrence.worldSite controls environment).Ready query :=
  ⟨below, ambient, occurrence.substitutions, closed, resources⟩

theorem OriginalRichOccurrenceFrame.route_ambient
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {first : EndpointState sourceEnv U occurrenceSource expression assigned}
    {last : EndpointState sourceEnv U occurrenceSource expression natural}
    {location : Located root first}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (route : PrefixRoute sourceEnv U occurrenceSource expression first last)
    (ambient : occurrence.frame.Ambient) : (occurrence.route route).frame.Ambient := by
  induction route with
  | done => exact ambient
  | expose reference rest ih =>
      exact ih (location := .expose location) ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩ ambient
  | convert plan term rest ih =>
      exact ih (location := .convertTerm location) ⟨occurrence.frame, occurrence.substitutions, occurrence.environment_le⟩ ambient

/-- The native projection openings use the exact same paired frame, not an
arbitrarily runnable site at the same source expression. -/
theorem OriginalRichOccurrenceFrame.projectionSites_ready
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index majorExpression) assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (head : ProjectionHead node)
    (major : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ profile majorFootprint)
    (field : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (below : sourceEnv ≤ env) (ambient : occurrence.frame.Ambient)
    (closed : available.AtomClosed) (resources : (majorFootprint ++ fieldFootprint).Available available) :
    let routed := occurrence.routeWorld controls head.route environment
    ((occurrence.projMajor head).worldSite controls routed).Ready major ∧
      ((occurrence.projField head).worldSite controls routed).Ready (.code field) := by
  dsimp only
  constructor
  · exact (occurrence.projMajor head).worldSite_ready controls _ major below
      (occurrence.route_ambient head.route ambient) closed
      (fun i need member => resources i need (List.mem_append_left _ member))
  · exact (occurrence.projField head).worldSite_ready controls _ (.code field) below
      (occurrence.route_ambient head.route ambient) closed
      (fun i need member => resources i need (List.mem_append_right _ member))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
