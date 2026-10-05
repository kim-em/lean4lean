import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableProducer

/-! The declared domain `s.T` after a captured `s : Pack`. The source
certificate at that exact original projected domain is produced from the
prior slot's actual record demand, including native rich domain metadata. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichGroupedCapture.projectedDomainAlignment
    {domainS : EndpointRef headerEnv U headerSource S (.sort sLevel)}
    {domainX : EndpointRef headerEnv U (S :: headerSource) (.proj name index (.bvar 0)) (.sort xLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domainS env registry target
      locals σ available ownerInitial rawS leftS rightS)
    (head : ProjectionHead (.ref domainX))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (owner : HeaderOwner field major)
    (value : RichBinderValue sourceEnv env U registry target owner.node ownerLocals ownerLeft ownerRight
      ownerAvailable (input : Profile n))
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (same : owner.assigned.subst ownerLeft = .proj name index leftS)
    (needed : majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head (σ.cons leftS) value.support (.sort true))) ∈ entries.needs) :
    Nonempty (HeaderValueAlignment owner domainX env registry target ownerLocals (Locals.push locals)
      ownerLeft ownerRight (σ.cons leftS) ownerAvailable (available.push entries.needs) input) := by
  let request := fieldRequest head (σ.cons leftS) value.support (Profile.sort true)
  let record := fieldRecord family familyRelevant index request
  have member : (index, request) ∈ record.fields := List.mem_singleton_self _
  obtain ⟨_, _, _, _, _, _, _, majorRelated⟩ := entries.lookup henv formed needed
  have projected := majorRelated.projectRecord henv hscoped formed member
  have code := (projected.code_of_sortable henv hscoped formed value.certificate.formed).left_diagonal
  have fieldCode : SortableCert env U registry target (Locals.push locals) (σ.cons leftS)
      head.fieldType true (Profile.sort (n := n) true) [] := by
    rw [sortField]
    exact .seed (.sort sortRelevant) (Profile.HasType.sort true)
  let majorQuery : RichObs headerEnv env U registry target (.ref (.right head.major)) (Locals.push locals)
      (σ.cons leftS) (Profile.singleton (n := n + 1) (.record record)) [(0, majorNeed record)] :=
    .legacy (.legacy (.var _ _ 0 _))
  let projection : RichObs headerEnv env U registry target (.ref domainX) (Locals.push locals)
      (σ.cons leftS) value.support ([(0, majorNeed record)] ++ []) :=
    .projection head familyName member majorQuery (.legacy fieldCode) value.certificate.formed (.refl _)
  refine ⟨{ value := value, aligned := {
    footprint := [(0, majorNeed record)] ++ []
    certificate := .observe projection value.certificate.formed
    resources := ?_
    related := ?_ }, path := ?_ }⟩
  · intro i need hm
    simp only [List.append_nil, List.mem_singleton] at hm
    cases hm
    exact needed
  · simpa only [record, fieldRecord, familyName, same, subst_proj, subst_bvar, Subst.cons] using code
  · simpa only [same, subst_proj, subst_bvar, Subst.cons] using
      (TypeConversion.refl : TypeConversion env U target (.proj name index leftS) (.proj name index leftS))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
