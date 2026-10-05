import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrence
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! Legacy computational and formation queries are traversed at their actual
original endpoint occurrences. Applications and binders use computed original
prefixes; guards construct actual source frames without reflecting a query.
Declaration plans remain an explicit earlier-header frontier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

mutual
noncomputable def legacyCodeOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed (.code (.legacy (.ofCode certificate certificate.formed))) resources metadata sourceTail ::
  match certificate with
  | .seed source _ => legacyObsOccurrences source occurrence henv sourceBelow closed resources metadata sourceTail
  | .union left right =>
    legacyCodeOccurrences left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    legacyCodeOccurrences right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .pad child | .familyPad child | .unpad child | .down child | .map _ child
  | .select child _ | .focusMinimal child _ _ =>
    legacyCodeOccurrences child occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

noncomputable def legacyRowsOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U context A (.sort u)}
    {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
    (rows : PiRows env U registry target locals σ A B ambient values footprint)
    (hu : u.WF U) (hv : v.WF U)
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (domainCode : CodeCert env U registry target locals σ A ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  match rows with
  | .nil => []
  | .cons guard certificate pack covered tail =>
    let child := occurrence.piAnchor henv sourceBelow (.legacy (.ofCode domainCode domainCode.formed)) domainResources guard pack covered
    legacyCodeOccurrences certificate child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push (by rfl) _ _) ++
    legacyRowsOccurrences tail hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

noncomputable def legacyObsOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : Obs env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed (.legacy (.legacy query)) resources metadata sourceTail ::
  match query with
  | .delta .. | .native .. | .family .. | .constructor .. | .var .. | .sort .. | .empty => []
  | .app fn arg _ _ =>
    let packet := applicationPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    legacyObsOccurrences fn natural.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ ++
    legacyObsOccurrences arg natural.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩
  | .lam domain guard body pack covered =>
    let packet := lambdaPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := natural.lamAnchor henv sourceBelow (.legacy (.ofCode domain domain.formed)) domainResources guard pack covered
    legacyCodeOccurrences domain natural.lamDomain henv sourceBelow closed domainResources true ⟨naturalTail.left, naturalTail.right⟩ ++
    legacyObsOccurrences body child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (naturalTail.push (by rfl) _ _)
  | .pi domain _ rows =>
    let packet := piPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    legacyCodeOccurrences domain natural.piDomain henv sourceBelow closed domainResources metadata ⟨naturalTail.left, naturalTail.right⟩ ++
      legacyRowsOccurrences rows packet.view.domainWF packet.view.bodyWF natural domain domainResources
        henv sourceBelow closed (fun i need member => resources i need (List.mem_append_right _ member)) metadata naturalTail
  | .union left right =>
    legacyObsOccurrences left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    legacyObsOccurrences right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .view child _ | .pad child | .unpad child | .rowShift child =>
    legacyObsOccurrences child occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

mutual
noncomputable def sortableCertOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : SortableCert env U registry target locals σ expression relevant profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed (.code (.legacy certificate)) resources metadata sourceTail ::
  match certificate with
  | .ofCode source _ => legacyCodeOccurrences source occurrence henv sourceBelow closed resources metadata sourceTail
  | .seed source _ => legacyObsOccurrences source occurrence henv sourceBelow closed resources metadata sourceTail
  | .observe source _ => sortableObsOccurrences source occurrence henv sourceBelow closed resources metadata sourceTail
  | .pi domain _ rows =>
    let packet := piPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    sortableCertOccurrences domain natural.piDomain henv sourceBelow closed domainResources metadata ⟨naturalTail.left, naturalTail.right⟩ ++
      sortableRowsOccurrences rows packet.view.domainWF packet.view.bodyWF natural domain domainResources
        henv sourceBelow closed (fun i need member => resources i need (List.mem_append_right _ member)) metadata naturalTail
  | .union left right =>
    sortableCertOccurrences left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    sortableCertOccurrences right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .pad child | .sortPad child | .familyPad child | .unpad child | .down child | .map _ child
  | .support _ child | .select child _ | .focusMinimal child _ _ =>
    sortableCertOccurrences child occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

noncomputable def sortableRowsOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {domain : EndpointState sourceEnv U context A (.sort u)}
    {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
    (rows : SortableRows env U registry target locals σ A B relevant ambient values footprint)
    (hu : u.WF U) (hv : v.WF U)
    {location : Located root (.pi hu hv domain body)}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (domainCode : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  match rows with
  | .nil => []
  | .cons guard certificate pack covered tail =>
    let child := occurrence.piAnchor henv sourceBelow (.legacy domainCode) domainResources guard pack covered
    sortableCertOccurrences certificate child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push (by rfl) _ _) ++
    sortableRowsOccurrences tail hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

noncomputable def sortableObsOccurrences
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : SortableObs env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) :
    List (RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :=
  RichQueryOccurrence.ofQuery occurrence closed (.legacy query) resources metadata sourceTail ::
  match query with
  | .family .. => []
  | .legacy source => legacyObsOccurrences source occurrence henv sourceBelow closed resources metadata sourceTail
  | .code _ certificate => sortableCertOccurrences certificate occurrence henv sourceBelow closed resources metadata sourceTail
  | .app fn arg _ _ =>
    let packet := applicationPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    sortableObsOccurrences fn natural.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ ++
    sortableObsOccurrences arg natural.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩
  | .lam domain guard body pack covered =>
    let packet := lambdaPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := natural.lamAnchor henv sourceBelow (.legacy domain) domainResources guard pack covered
    sortableCertOccurrences domain natural.lamDomain henv sourceBelow closed domainResources true ⟨naturalTail.left, naturalTail.right⟩ ++
    sortableObsOccurrences body child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (naturalTail.push (by rfl) _ _)
  | .union left right =>
    sortableObsOccurrences left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail ++
    sortableObsOccurrences right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail
  | .view child _ | .action child _ | .pad child | .unpad child | .rowShift child =>
    sortableObsOccurrences child occurrence henv sourceBelow closed resources metadata sourceTail
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
