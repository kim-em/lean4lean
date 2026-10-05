import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! Syntax-first discovery for an actual projected declaration domain. The
certificate and exact earlier-slot demand are computed before choosing the
right valuation or constructing any group frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def projectedDomainQuery
    {domain : EndpointRef headerEnv U headerSource (.proj name index (.bvar slot)) (.sort level)}
    (head : ProjectionHead (.ref domain))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (profile : Profile n) (typed : profile.HasType (.sort true)) :
    RichCert headerEnv env U registry target (.ref domain) locals σ true profile
      [(slot, majorNeed (fieldRecord family familyRelevant index
        (fieldRequest head σ profile (.sort true))))] := by
  let request := fieldRequest head σ profile (Profile.sort true)
  let record := fieldRecord family familyRelevant index request
  have fieldCode : SortableCert env U registry target locals σ
      head.fieldType true (Profile.sort (n := n) true) [] := by
    rw [sortField]
    exact .seed (.sort sortRelevant) (Profile.HasType.sort true)
  let majorQuery : RichObs headerEnv env U registry target (.ref (.right head.major)) locals σ
      (Profile.singleton (n := n + 1) (.record record)) [(slot, majorNeed record)] :=
    .legacy (.legacy (.var _ _ slot _))
  have projection : RichObs headerEnv env U registry target (.ref domain) locals σ profile
      ([(slot, majorNeed record)] ++ []) :=
    .projection head familyName (List.mem_singleton_self _) majorQuery (.legacy fieldCode) typed (.refl _)
  simpa only [List.append_nil] using RichCert.observe projection typed

/-- The actual projected syntax asks for precisely one earlier-slot need.
There is no preselected right frame in this statement. -/
theorem projectedDomainQuery_available
    {domain : EndpointRef headerEnv U headerSource (.proj name index (.bvar slot)) (.sort level)}
    {available : Valuation}
    (head : ProjectionHead (.ref domain)) (family : FamilyData (Profile n))
    (familyRelevant : family.relevant = true) (profile : Profile n) :
    Footprint.Available [(slot, majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head σ profile (.sort true))))] available ↔
    majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head σ profile (.sort true))) ∈ available slot := by
  constructor
  · intro resources
    exact resources _ _ (List.mem_singleton_self _)
  · intro member i need h
    cases List.mem_singleton.mp h
    exact member

/-- Replaying the discovered demand only visits an earlier declaration slot.
In chronological order that slot's preceding prefix is strictly shorter. -/
theorem projectedDomainQuery_earlier (lookup : Lookup headerSource slot S) :
    headerSource.length - (slot + 1) < headerSource.length := by
  have := lookup.lt
  omega

/-- After recursively producing the earlier prefix, interpret the SAME
syntax-first certificate and finish the owner alignment. -/
noncomputable def PendingRichCapture.finishProjectedDemand
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource (.proj name index (.bvar slot)) (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (lookup : Lookup headerSource slot S)
    (head : ProjectionHead (.ref domain))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (value : RichBinderValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (family : FamilyData (Profile pending.rank)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (same : pending.owner.assigned.subst pending.ownerLeft = .proj name index (σ slot))
    (needed : majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head σ value.support (.sort true))) ∈ available slot) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue := by
  let request := fieldRequest head σ value.support (Profile.sort true)
  let record := fieldRecord family familyRelevant index request
  let entry := Classical.choose (frame.lookup_allDepth henv formed needed lookup)
  have projected := entry.related.projectRecord henv hscoped formed
    (show (index, request) ∈ record.fields from List.mem_singleton_self _)
  have code := (projected.code_of_sortable henv hscoped formed value.certificate.formed).left_diagonal
  exact pending.complete {
    value := value
    aligned := {
      footprint := [(slot, majorNeed record)]
      certificate := projectedDomainQuery head sortField sortRelevant family familyName familyRelevant
        value.support value.certificate.formed
      resources := (projectedDomainQuery_available head family familyRelevant value.support).mpr needed
      related := by simpa only [record, fieldRecord, familyName, same, subst_proj, subst_bvar] using code }
    path := by simpa only [same, subst_proj, subst_bvar] using
      (TypeConversion.refl : TypeConversion env U target (.proj name index (σ slot)) (.proj name index (σ slot))) }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
