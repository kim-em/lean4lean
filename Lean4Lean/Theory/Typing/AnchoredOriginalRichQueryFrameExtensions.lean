import Lean4Lean.Theory.Typing.AnchoredOriginalFrameExtension
import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrences
import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyQueryFrameExtensions

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
local infixr:65 " +++ " => AllFrameExtensions.append

mutual
theorem RichCert.framedOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (certificate.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match certificate, location, occurrence, resources, sourceTail, extension with
  | .legacy certificate, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <| sortableCertOccurrences_frames certificate occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .observe query _, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <| query.framedOccurrences_frames occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .pi hu hv domain _ rows, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    domain.framedOccurrences_frames occurrence.piDomain henv sourceBelow closed domainResources metadata (sourceTail.at rfl) extension +++
      rows.framedOccurrences_frames hu hv occurrence domain domainResources henv sourceBelow closed
        (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .route route child, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <| child.framedOccurrences_frames (occurrence.route route) henv sourceBelow closed resources metadata (sourceTail.route route) (OriginalFrameExtension.route occurrence route extension)
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    left.framedOccurrences_frames occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    right.framedOccurrences_frames occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .pad child, location, occurrence, resources, sourceTail, extension | .down child, location, occurrence, resources, sourceTail, extension | .map _ child, location, occurrence, resources, sourceTail, extension | .support _ child, location, occurrence, resources, sourceTail, extension | .select child _, location, occurrence, resources, sourceTail, extension => by
    rw [RichCert.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    child.framedOccurrences_frames occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichRows.framedOccurrences_frames
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
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (rows.framedOccurrences hu hv occurrence domainCode domainResources henv sourceBelow closed resources metadata sourceTail) :=
  match rows, location, occurrence, resources, sourceTail, extension with
  | .nil, location, occurrence, resources, sourceTail, extension => by
    rw [RichRows.framedOccurrences]
    exact AllFrameExtensions.nil
  | .cons guard certificate pack covered tail, location, occurrence, resources, sourceTail, extension => by
    rw [RichRows.framedOccurrences]
    exact
    let child := occurrence.piAnchor henv sourceBelow domainCode domainResources guard pack covered
    let childExtension := OriginalFrameExtension.piAnchor occurrence henv sourceBelow domainCode domainResources guard pack covered extension
    certificate.framedOccurrences_frames child henv sourceBelow
      (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push rfl _ _) childExtension +++
    tail.framedOccurrences_frames hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.framedOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (query.framedOccurrences occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match query, location, occurrence, resources, sourceTail, extension with
  | .legacy query, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <| sortableObsOccurrences_frames query occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .rigidFamily .., location, occurrence, resources, sourceTail, extension | .family .., location, occurrence, resources, sourceTail, extension | .constructor .., location, occurrence, resources, sourceTail, extension | .canonicalConst .., location, occurrence, resources, sourceTail, extension | .canonicalDelta .., location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <| AllFrameExtensions.nil
  | .code certificate, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <| certificate.framedOccurrences_frames occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .projection head _ _ major field _ _, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    major.framedOccurrences_frames (occurrence.projMajor head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ((sourceTail.route head.route).at rfl) (OriginalFrameExtension.route occurrence head.route extension) +++
    field.framedOccurrences_frames (occurrence.projField head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) true ((sourceTail.route head.route).at rfl) (OriginalFrameExtension.route occurrence head.route extension)
  | .projectionSortable head _ _ major _ _ _ field _, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    major.framedOccurrences_frames (occurrence.projMajor head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ((sourceTail.route head.route).at rfl) (OriginalFrameExtension.route occurrence head.route extension) +++
    field.framedOccurrences_frames (occurrence.projField head) henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) true ((sourceTail.route head.route).at rfl) (OriginalFrameExtension.route occurrence head.route extension)
  | .app _ _ fn arg _ _, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    fn.framedOccurrences_frames occurrence.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata (sourceTail.at rfl) extension +++
    arg.framedOccurrences_frames occurrence.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata (sourceTail.at rfl) extension
  | .lam _ _ domain guard body pack covered, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := occurrence.lamAnchor henv sourceBelow domain domainResources guard pack covered
    let childExtension := OriginalFrameExtension.lamAnchor occurrence henv sourceBelow domain domainResources guard pack covered extension
    domain.framedOccurrences_frames occurrence.lamDomain henv sourceBelow closed domainResources true (sourceTail.at rfl) extension +++
    body.framedOccurrences_frames child henv sourceBelow
      (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (sourceTail.push rfl _ _) childExtension
  | .route route child, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <| child.framedOccurrences_frames (occurrence.route route) henv sourceBelow closed resources metadata (sourceTail.route route) (OriginalFrameExtension.route occurrence route extension)
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    left.framedOccurrences_frames occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    right.framedOccurrences_frames occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .view child _, location, occurrence, resources, sourceTail, extension | .action child _, location, occurrence, resources, sourceTail, extension | .select child _, location, occurrence, resources, sourceTail, extension | .pad child, location, occurrence, resources, sourceTail, extension | .unpad child, location, occurrence, resources, sourceTail, extension => by
    rw [RichObs.framedOccurrences]
    exact AllFrameExtensions.cons extension <|
    child.framedOccurrences_frames occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
