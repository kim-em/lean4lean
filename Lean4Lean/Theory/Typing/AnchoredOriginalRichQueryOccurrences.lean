import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrence
import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyQueryOccurrences

/-! Finite traversal of native and legacy queries with their actual original
frames and root substitutions. Closed declaration children remain in their
earlier source environment rather than being moved into the current root. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

mutual
noncomputable def RichCert.framedOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed (.code certificate) resources metadata sourceTail ::
  match certificate with
  | .legacy certificate => sortableCertOccurrences certificate occurrence henv sourceBelow closed resources metadata sourceTail
  | .observe query _ => query.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail
  | .pi hu hv domain _ rows =>
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    domain.framedOccurrences occurrence.piDomain henv sourceBelow closed domainResources metadata (sourceTail.at rfl) ++
      rows.framedOccurrences hu hv occurrence domain domainResources henv sourceBelow closed
        (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .route route child => child.framedOccurrences (occurrence.route route) henv sourceBelow closed resources metadata (sourceTail.route route)
  | .union left right =>
    left.framedOccurrences occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    right.framedOccurrences occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .pad child | .down child | .map _ child | .support _ child | .select child _ =>
    child.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

noncomputable def RichRows.framedOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U context A (.sort u)}
    {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint)
    (hu : u.WF U) (hv : v.WF U)
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  match rows with
  | .nil => []
  | .cons guard certificate pack covered tail =>
    let child := occurrence.piAnchor henv sourceBelow domainCode domainResources guard pack covered
    certificate.framedOccurrences child henv sourceBelow
      (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push rfl _ _) ++
    tail.framedOccurrences hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

noncomputable def RichObs.framedOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed query resources metadata sourceTail ::
  match query with
  | .legacy query => sortableObsOccurrences query occurrence henv sourceBelow closed resources metadata sourceTail
  | .rigidFamily .. | .family .. | .constructor .. | .canonicalConst .. | .canonicalDelta .. => []
  | .code certificate => certificate.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail
  | .projection head _ _ major field _ _ =>
    major.framedOccurrences (occurrence.projMajor head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ((sourceTail.route head.route).at rfl) ++
    field.framedOccurrences (occurrence.projField head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) true ((sourceTail.route head.route).at rfl)
  | .projectionSortable head _ _ major _ _ _ field _ =>
    major.framedOccurrences (occurrence.projMajor head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ((sourceTail.route head.route).at rfl) ++
    field.framedOccurrences (occurrence.projField head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) true ((sourceTail.route head.route).at rfl)
  | .app _ _ fn arg _ _ =>
    fn.framedOccurrences occurrence.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata (sourceTail.at rfl) ++
    arg.framedOccurrences occurrence.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata (sourceTail.at rfl)
  | .lam _ _ domain guard body pack covered =>
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := occurrence.lamAnchor henv sourceBelow domain domainResources guard pack covered
    domain.framedOccurrences occurrence.lamDomain henv sourceBelow closed domainResources true (sourceTail.at rfl) ++
    body.framedOccurrences child henv sourceBelow
      (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (sourceTail.push rfl _ _)
  | .route route child => child.framedOccurrences (occurrence.route route) henv sourceBelow closed resources metadata (sourceTail.route route)
  | .union left right =>
    left.framedOccurrences occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    right.framedOccurrences occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .view child _ | .action child _ | .select child _ | .pad child | .unpad child =>
    child.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf query
decreasing_by all_goals simp_wf; omega
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
