import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableProducer

/-! Reconstruct an original projected declaration domain from any earlier
slot of the actual generic frame. Lookup traverses ordinary binders and
finite grouped captures, retaining the selected original owner semantics. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.projectedDomainAlignment
    {context : ContextDerivation headerEnv U headerSource}
    {domainX : EndpointRef headerEnv U headerSource (.proj name index (.bvar slot)) (.sort xLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (lookup : Lookup headerSource slot S)
    (head : ProjectionHead (.ref domainX))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (owner : HeaderOwner field major)
    (value : RichBinderValue sourceEnv env U registry target owner.node ownerLocals ownerLeft ownerRight
      ownerAvailable (input : Profile n))
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (same : owner.assigned.subst ownerLeft = .proj name index (σ slot))
    (needed : majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head σ value.support (.sort true))) ∈ available slot) :
    Nonempty (HeaderValueAlignment owner domainX env registry target ownerLocals locals
      ownerLeft ownerRight σ ownerAvailable (available) input) := by
  let request := fieldRequest head σ value.support (Profile.sort true)
  let record := fieldRecord family familyRelevant index request
  have member : (index, request) ∈ record.fields := List.mem_singleton_self _
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed needed lookup
  have majorRelated := entry.related
  have projected := majorRelated.projectRecord henv hscoped formed member
  have code := (projected.code_of_sortable henv hscoped formed value.certificate.formed).left_diagonal
  have fieldCode : SortableCert env U registry target locals σ
      head.fieldType true (Profile.sort (n := n) true) [] := by
    rw [sortField]
    exact .seed (.sort sortRelevant) (Profile.HasType.sort true)
  let majorQuery : RichObs headerEnv env U registry target (.ref (.right head.major)) locals
      σ (Profile.singleton (n := n + 1) (.record record)) [(slot, majorNeed record)] :=
    .legacy (.legacy (.var _ _ slot _))
  let projection : RichObs headerEnv env U registry target (.ref domainX) locals
      σ value.support ([(slot, majorNeed record)] ++ []) :=
    .projection head familyName member majorQuery (.legacy fieldCode) value.certificate.formed (.refl _)
  refine ⟨{ value := value, aligned := {
    footprint := [(slot, majorNeed record)] ++ []
    certificate := .observe projection value.certificate.formed
    resources := ?_
    related := ?_ }, path := ?_ }⟩
  · intro i need hm
    simp only [List.append_nil, List.mem_singleton] at hm
    cases hm
    exact needed
  · simpa only [record, fieldRecord, familyName, same, subst_proj, subst_bvar, Subst.cons] using code
  · simpa only [same, subst_proj, subst_bvar, Subst.cons] using
      (TypeConversion.refl : TypeConversion env U target (.proj name index (σ slot)) (.proj name index (σ slot)))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
