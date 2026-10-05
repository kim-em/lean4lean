import Lean4Lean.Theory.Typing.AnchoredOriginalFrameExtension
import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyQueryOccurrences

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
local infixr:65 " +++ " => AllFrameExtensions.append

mutual
theorem legacyCodeOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (legacyCodeOccurrences certificate occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match certificate, location, occurrence, resources, sourceTail, extension with
  | .seed source _, location, occurrence, resources, sourceTail, extension => by
    rw [legacyCodeOccurrences]
    exact AllFrameExtensions.cons extension <| legacyObsOccurrences_frames source occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [legacyCodeOccurrences]
    exact AllFrameExtensions.cons extension <|
    legacyCodeOccurrences_frames left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    legacyCodeOccurrences_frames right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .pad child, location, occurrence, resources, sourceTail, extension | .familyPad child, location, occurrence, resources, sourceTail, extension | .unpad child, location, occurrence, resources, sourceTail, extension | .down child, location, occurrence, resources, sourceTail, extension | .map _ child, location, occurrence, resources, sourceTail, extension | .select child _, location, occurrence, resources, sourceTail, extension | .focusMinimal child _ _, location, occurrence, resources, sourceTail, extension => by
    rw [legacyCodeOccurrences]
    exact AllFrameExtensions.cons extension <|
    legacyCodeOccurrences_frames child occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem legacyRowsOccurrences_frames
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
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (legacyRowsOccurrences rows hu hv occurrence domainCode domainResources henv sourceBelow closed resources metadata sourceTail) :=
  match rows, location, occurrence, resources, sourceTail, extension with
  | .nil, location, occurrence, resources, sourceTail, extension => by
    rw [legacyRowsOccurrences]
    exact AllFrameExtensions.nil
  | .cons guard certificate pack covered tail, location, occurrence, resources, sourceTail, extension => by
    rw [legacyRowsOccurrences]
    exact
    let child := occurrence.piAnchor henv sourceBelow (.legacy (.ofCode domainCode domainCode.formed)) domainResources guard pack covered
    let childExtension := OriginalFrameExtension.piAnchor occurrence henv sourceBelow (.legacy (.ofCode domainCode domainCode.formed)) domainResources guard pack covered extension
    legacyCodeOccurrences_frames certificate child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push (by rfl) _ _) childExtension +++
    legacyRowsOccurrences_frames tail hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem legacyObsOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : Obs env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (legacyObsOccurrences query occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match query, location, occurrence, resources, sourceTail, extension with
  | .delta .., location, occurrence, resources, sourceTail, extension | .native .., location, occurrence, resources, sourceTail, extension | .family .., location, occurrence, resources, sourceTail, extension | .constructor .., location, occurrence, resources, sourceTail, extension | .var .., location, occurrence, resources, sourceTail, extension | .sort .., location, occurrence, resources, sourceTail, extension | .empty, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <| AllFrameExtensions.nil
  | .app fn arg _ _, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := applicationPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    legacyObsOccurrences_frames fn natural.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
    legacyObsOccurrences_frames arg natural.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension
  | .lam domain guard body pack covered, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := lambdaPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := natural.lamAnchor henv sourceBelow (.legacy (.ofCode domain domain.formed)) domainResources guard pack covered
    let childExtension := OriginalFrameExtension.lamAnchor natural henv sourceBelow (.legacy (.ofCode domain domain.formed)) domainResources guard pack covered naturalExtension
    legacyCodeOccurrences_frames domain natural.lamDomain henv sourceBelow closed domainResources true ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
    legacyObsOccurrences_frames body child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (naturalTail.push (by rfl) _ _) childExtension
  | .pi domain _ rows, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := piPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    legacyCodeOccurrences_frames domain natural.piDomain henv sourceBelow closed domainResources metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
      legacyRowsOccurrences_frames rows packet.view.domainWF packet.view.bodyWF natural domain domainResources
        henv sourceBelow closed (fun i need member => resources i need (List.mem_append_right _ member)) metadata naturalTail naturalExtension
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    legacyObsOccurrences_frames left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    legacyObsOccurrences_frames right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .view child _, location, occurrence, resources, sourceTail, extension | .pad child, location, occurrence, resources, sourceTail, extension | .unpad child, location, occurrence, resources, sourceTail, extension | .rowShift child, location, occurrence, resources, sourceTail, extension => by
    rw [legacyObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    legacyObsOccurrences_frames child occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

mutual
theorem sortableCertOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (certificate : SortableCert env U registry target locals σ expression relevant profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (sortableCertOccurrences certificate occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match certificate, location, occurrence, resources, sourceTail, extension with
  | .ofCode source _, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <| legacyCodeOccurrences_frames source occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .seed source _, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <| legacyObsOccurrences_frames source occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .observe source _, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <| sortableObsOccurrences_frames source occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .pi domain _ rows, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := piPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    sortableCertOccurrences_frames domain natural.piDomain henv sourceBelow closed domainResources metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
      sortableRowsOccurrences_frames rows packet.view.domainWF packet.view.bodyWF natural domain domainResources
        henv sourceBelow closed (fun i need member => resources i need (List.mem_append_right _ member)) metadata naturalTail naturalExtension
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <|
    sortableCertOccurrences_frames left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    sortableCertOccurrences_frames right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .pad child, location, occurrence, resources, sourceTail, extension | .sortPad child, location, occurrence, resources, sourceTail, extension | .familyPad child, location, occurrence, resources, sourceTail, extension | .unpad child, location, occurrence, resources, sourceTail, extension | .down child, location, occurrence, resources, sourceTail, extension | .map _ child, location, occurrence, resources, sourceTail, extension | .support _ child, location, occurrence, resources, sourceTail, extension | .select child _, location, occurrence, resources, sourceTail, extension | .focusMinimal child _ _, location, occurrence, resources, sourceTail, extension => by
    rw [sortableCertOccurrences]
    exact AllFrameExtensions.cons extension <|
    sortableCertOccurrences_frames child occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem sortableRowsOccurrences_frames
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
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (sortableRowsOccurrences rows hu hv occurrence domainCode domainResources henv sourceBelow closed resources metadata sourceTail) :=
  match rows, location, occurrence, resources, sourceTail, extension with
  | .nil, location, occurrence, resources, sourceTail, extension => by
    rw [sortableRowsOccurrences]
    exact AllFrameExtensions.nil
  | .cons guard certificate pack covered tail, location, occurrence, resources, sourceTail, extension => by
    rw [sortableRowsOccurrences]
    exact
    let child := occurrence.piAnchor henv sourceBelow (.legacy domainCode) domainResources guard pack covered
    let childExtension := OriginalFrameExtension.piAnchor occurrence henv sourceBelow (.legacy domainCode) domainResources guard pack covered extension
    sortableCertOccurrences_frames certificate child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_left _ member))) metadata (sourceTail.push (by rfl) _ _) childExtension +++
    sortableRowsOccurrences_frames tail hu hv occurrence domainCode domainResources henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem sortableObsOccurrences_frames
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (query : SortableObs env U registry target locals σ expression profile footprint)
    {location : Located root node}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (closed : available.AtomClosed) (resources : footprint.Available available) (metadata : Bool)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base occurrence.frame.raw) :
    AllFrameExtensions base (sortableObsOccurrences query occurrence henv sourceBelow closed resources metadata sourceTail) :=
  match query, location, occurrence, resources, sourceTail, extension with
  | .family .., location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <| AllFrameExtensions.nil
  | .legacy source, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <| legacyObsOccurrences_frames source occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .code _ certificate, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <| sortableCertOccurrences_frames certificate occurrence henv sourceBelow closed resources metadata sourceTail extension
  | .app fn arg _ _, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := applicationPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    sortableObsOccurrences_frames fn natural.appFunction henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
    sortableObsOccurrences_frames arg natural.appArgument henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata ⟨naturalTail.left, naturalTail.right⟩ naturalExtension
  | .lam domain guard body pack covered, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    let packet := lambdaPrefix location
    let natural : OriginalRichOccurrenceFrame packet.view.location initialContext env registry target locals σ τ available
        ordered initialEnvironment := packet.location_eq ▸ occurrence.route packet.route
    let naturalExtension := OriginalFrameExtension.locationCast packet.location_eq
      (occurrence.route packet.route) (OriginalFrameExtension.route occurrence packet.route extension)
    let naturalTail : RichSourceTail packet.view.location σ τ rootLeft rootRight :=
      packet.location_eq ▸ sourceTail.route packet.route
    let domainResources := fun i need member => resources i need (List.mem_append_left _ member)
    let child := natural.lamAnchor henv sourceBelow (.legacy domain) domainResources guard pack covered
    let childExtension := OriginalFrameExtension.lamAnchor natural henv sourceBelow (.legacy domain) domainResources guard pack covered naturalExtension
    sortableCertOccurrences_frames domain natural.lamDomain henv sourceBelow closed domainResources true ⟨naturalTail.left, naturalTail.right⟩ naturalExtension +++
    sortableObsOccurrences_frames body child henv sourceBelow (Valuation.push_atomized_closed closed _)
      (pack.available_atomized_localNeeds (fun i need member => resources i need (List.mem_append_right _ member))) metadata (naturalTail.push (by rfl) _ _) childExtension
  | .union left right, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    sortableObsOccurrences_frames left occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_left _ member)) metadata sourceTail extension +++
    sortableObsOccurrences_frames right occurrence henv sourceBelow closed
      (fun i need member => resources i need (List.mem_append_right _ member)) metadata sourceTail extension
  | .view child _, location, occurrence, resources, sourceTail, extension | .action child _, location, occurrence, resources, sourceTail, extension | .pad child, location, occurrence, resources, sourceTail, extension | .unpad child, location, occurrence, resources, sourceTail, extension | .rowShift child, location, occurrence, resources, sourceTail, extension => by
    rw [sortableObsOccurrences]
    exact AllFrameExtensions.cons extension <|
    sortableObsOccurrences_frames child occurrence henv sourceBelow closed resources metadata sourceTail extension
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
