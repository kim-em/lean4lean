import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQuerySiteReady
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContextualProvenance

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The computed contextual annotation actually contains these executable
sites. This is not a theorem about arbitrary externally supplied annotations. -/
theorem RichObs.contextualProjection_sites
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index majorExpression) assigned}
    {location : Located root node}
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (head : ProjectionHead node) (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (major : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
      (.singleton (n := n + 1) (.record record)) majorFootprint)
    (field : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (henv : env.Ordered) (below : sourceEnv ≤ env) (ambient : occurrence.frame.Ambient)
    (closed : available.AtomClosed) (resources : (majorFootprint ++ fieldFootprint).Available available) :
    let routed := occurrence.routeWorld controls head.route environment
    let majorSite := (occurrence.projMajor head).worldSite controls routed
    let fieldSite := (occurrence.projField head).worldSite controls routed
    ∃ (majorAnnotation : WorldObsProvenance strata major) (fieldAnnotation : WorldCertProvenance strata field),
      RichObs.contextualWorldProvenance (.projection head nameEq member major field typed alignment)
          controls occurrence environment henv below resources =
        WorldObsProvenance.projection head nameEq member majorAnnotation fieldAnnotation majorSite fieldSite typed alignment ∧
      majorSite.Ready major ∧ fieldSite.Ready (.code field) := by
  dsimp only
  let majorAnnotation := RichObs.contextualWorldProvenance major controls (occurrence.projMajor head)
    (occurrence.routeWorld controls head.route environment) henv below
    (fun i need member => resources i need (List.mem_append_left _ member))
  let fieldAnnotation := RichCert.contextualWorldProvenance field controls (occurrence.projField head)
    (occurrence.routeWorld controls head.route environment) henv below
    (fun i need member => resources i need (List.mem_append_right _ member))
  refine ⟨majorAnnotation, fieldAnnotation, ?_,
    occurrence.projectionSites_ready controls environment head major field below ambient closed resources⟩
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
