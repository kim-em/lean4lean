import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainOrigins

/-! Legacy and sortable Pi-domain extraction constructs the requested
certificate together with its existing world provenance and depth bound.
A fixed budget is inherited through all wrappers, including empty Pi rows. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

mutual
theorem WorldLegacyObsProvenance.piDomainOrigins
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {profile : Profile n}
    {query : Obs env U registry target locals σ (.forallE A B) profile footprint}
    {budget : WorldPiDomainBudget strata}
    (annotation : WorldLegacyObsProvenance strata query)
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, query.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .empty => exact fun _ member => nomatch member
  | _, _, _, _, .pi domain guard rows domainAnnotation rowsAnnotation =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨{
      toRichDomainCertificate := ⟨_, .legacy (.ofCode domain domain.formed),
      fun i need member => resources i need (List.mem_append_left _ member)⟩
      annotation := .legacy _ (.ofCode domain domain.formed domainAnnotation)
      worlds_subset := fun _ member => worlds (List.mem_append_left _ member)
      depth_le := ?_ }⟩
    intro policy
    simpa only [RichCert.headDepth, SortableCert.headDepth] using
      Nat.le_trans (Nat.le_max_left _ _) (depth policy)
  | _, _, _, _, .union _ _ left right =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds (List.mem_append_left _ member))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member
    · exact right.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds (List.mem_append_right _ member))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [Obs.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .view _ change child =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _)).view change
  | _, _, _, _, .rowShift _ child =>
    try simp only [Obs.headDepth] at depth
    have impossible := child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldLegacyCertProvenance.piDomainOrigins
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {profile : Profile n}
    {query : CodeCert env U registry target locals σ (.forallE A B) profile footprint}
    {budget : WorldPiDomainBudget strata}
    (annotation : WorldLegacyCertProvenance strata query)
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, query.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .seed _ _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds (List.mem_append_left _ member))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member
    · exact right.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds (List.mem_append_right _ member))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .familyPad _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact False.elim (child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _))
  | _, _, _, _, .down _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).down
  | _, _, _, _, .map change _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).map change
  | _, _, _, _, .focusMinimal _ minimal bound child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).focusMinimal minimal bound
  | _, _, _, _, .select _ selected child =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ selected
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldSortableObsProvenance.piDomainOrigins
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {profile : Profile n}
    {query : SortableObs env U registry target locals σ (.forallE A B) profile footprint}
    {budget : WorldPiDomainBudget strata}
    (annotation : WorldSortableObsProvenance strata query)
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, query.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .legacy _ child | _, _, _, _, .code _ _ child =>
    try simp only [SortableObs.headDepth] at depth
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds (List.mem_append_left _ member))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member
    · exact right.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds (List.mem_append_right _ member))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [SortableObs.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .view _ change child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _)).view change
  | _, _, _, _, .rowShift _ child =>
    try simp only [SortableObs.headDepth] at depth
    have impossible := child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _)
    cases impossible
  | _, _, _, _, .action _ change child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _)).action change
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldSortableCertProvenance.piDomainOrigins
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {profile : Profile n}
    {query : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
    {budget : WorldPiDomainBudget strata}
    (annotation : WorldSortableCertProvenance strata query)
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, query.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .pi domain guard rows domainAnnotation rowsAnnotation =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨{
      toRichDomainCertificate := ⟨_, .legacy domain,
      fun i need member => resources i need (List.mem_append_left _ member)⟩
      annotation := .legacy domain domainAnnotation
      worlds_subset := fun _ member => worlds (List.mem_append_left _ member)
      depth_le := ?_ }⟩
    intro policy
    simpa only [RichCert.headDepth, SortableCert.headDepth] using
      Nat.le_trans (Nat.le_max_left _ _) (depth policy)
  | _, _, _, _, .seed _ _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth
  | _, _, _, _, .observe _ _ child | _, _, _, _, .ofCode _ _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds (List.mem_append_left _ member))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy)) atom member
    · exact right.piDomainOrigins (domainNode := domainNode)
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds (List.mem_append_right _ member))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (depth policy)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .familyPad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact False.elim (child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ (List.mem_singleton_self _))
  | _, _, _, _, .down _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).down
  | _, _, _, _, .map change _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).map change
  | _, _, _, _, .focusMinimal _ minimal bound child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).focusMinimal minimal bound
  | _, _, _, _, .select _ selected child =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact child.piDomainOrigins (domainNode := domainNode) resources worlds depth _ selected
  | _, _, _, _, .sortPad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact False.elim (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).not_sort
  | _, _, _, _, .support action _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piDomainOrigins (domainNode := domainNode) resources worlds depth).support action
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
