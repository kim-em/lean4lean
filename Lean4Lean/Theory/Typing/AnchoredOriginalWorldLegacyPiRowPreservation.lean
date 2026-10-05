import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowSelection

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

variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
section
variable
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) →
    row.Controlled controls frontier →
    Admitted env U registry target key anchor anchor →
    ∃ next : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
      (reanchorKey key anchor) result, Nonempty (next.Controlled controls frontier))
include henv hscoped hTarget closed reanchorRow
mutual
theorem WorldLegacyObsProvenance.piRowOrigins
    {profile : Profile n}
    {query : Obs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyObsProvenance strata query)
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .empty => exact fun _ member => nomatch member
  | _, _, _, _, .pi domain guard rows domainAnnotation rowsAnnotation =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    intro key result selected
    obtain ⟨row, ready⟩ := rowsAnnotation.selectPiRow (domainNode := domainNode) (bodyNode := bodyNode) domain
      ⟨.legacy _ (.ofCode domain domain.formed domainAnnotation),
        (fun control active => by
          simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (depth control active)),
        (fun world member => worlds world (List.mem_append_left _ member))⟩
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
      (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active))
      (fun world member => worlds world (List.mem_append_right _ member)) selected
    exact ⟨_, row, ready⟩
  | _, _, _, _, .union _ _ left right =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds _ (List.mem_append_left _ member))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (depth control active)) atom member
    · exact right.piRowOrigins
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds _ (List.mem_append_right _ member))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [Obs.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    exact child.piRowOrigins resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .view _ change child =>
    try simp only [Obs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact (child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _)).view change
  | _, _, _, _, .rowShift _ child =>
    try simp only [Obs.headDepth] at depth
    have impossible := child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldLegacyCertProvenance.piRowOrigins
    {profile : Profile n}
    {query : CodeCert env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldLegacyCertProvenance strata query)
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .seed _ _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact child.piRowOrigins resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds _ (List.mem_append_left _ member))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (depth control active)) atom member
    · exact right.piRowOrigins
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds _ (List.mem_append_right _ member))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    exact child.piRowOrigins resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .familyPad _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact False.elim (child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _))
  | _, _, _, _, .down _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).down
  | _, _, _, _, .map change _ child =>
    try simp only [CodeCert.headDepth] at depth
    exact WorldPiProfileOrigins.mapWith henv hscoped hTarget closed reanchorRow change
      (child.piRowOrigins resources worlds depth)
  | _, _, _, _, .focusMinimal _ minimal bound child =>
    try simp only [CodeCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).focusMinimal minimal bound
  | _, _, _, _, .select _ selected child =>
    try simp only [CodeCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact child.piRowOrigins resources worlds depth _ selected
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldSortableObsProvenance.piRowOrigins
    {profile : Profile n}
    {query : SortableObs env U registry target locals σ (.forallE A B) profile footprint}
    (annotation : WorldSortableObsProvenance strata query)
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .legacy _ child | _, _, _, _, .code _ _ child =>
    try simp only [SortableObs.headDepth] at depth
    exact child.piRowOrigins resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds _ (List.mem_append_left _ member))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (depth control active)) atom member
    · exact right.piRowOrigins
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds _ (List.mem_append_right _ member))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [SortableObs.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    exact child.piRowOrigins resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .view _ change child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact (child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _)).view change
  | _, _, _, _, .rowShift _ child =>
    try simp only [SortableObs.headDepth] at depth
    have impossible := child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _)
    cases impossible
  | _, _, _, _, .action _ change child =>
    try simp only [SortableObs.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact WorldPiAtomOrigins.actionWith henv hscoped hTarget closed reanchorRow change
      (child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _))
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

theorem WorldSortableCertProvenance.piRowOrigins
    {profile : Profile n}
    {query : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint}
    (annotation : WorldSortableCertProvenance strata query)
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match n, profile, footprint, query, annotation with
  | _, _, _, _, .pi domain guard rows domainAnnotation rowsAnnotation =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    intro key result selected
    obtain ⟨row, ready⟩ := rowsAnnotation.selectPiRow (domainNode := domainNode) (bodyNode := bodyNode) domain
      ⟨.legacy domain domainAnnotation,
        (fun control active => by
          simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (depth control active)),
        (fun world member => worlds world (List.mem_append_left _ member))⟩
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
      (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active))
      (fun world member => worlds world (List.mem_append_right _ member)) selected
    exact ⟨_, row, ready⟩
  | _, _, _, _, .seed _ _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact child.piRowOrigins resources worlds depth
  | _, _, _, _, .observe _ _ child | _, _, _, _, .ofCode _ _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact child.piRowOrigins resources worlds depth
  | _, _, _, _, .union _ _ left right =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun _ member => worlds _ (List.mem_append_left _ member))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (depth control active)) atom member
    · exact right.piRowOrigins
        (fun i need member => resources i need (List.mem_append_right _ member))
        (fun _ member => worlds _ (List.mem_append_right _ member))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (depth control active)) atom member
  | _, _, _, _, .pad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).pad
  | _, _, _, _, .unpad _ child =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    exact child.piRowOrigins resources worlds depth (.pad atom) (List.mem_map_of_mem member)
  | _, _, _, _, .familyPad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact False.elim (child.piRowOrigins resources worlds depth _ (List.mem_singleton_self _))
  | _, _, _, _, .down _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).down
  | _, _, _, _, .map change _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact WorldPiProfileOrigins.mapWith henv hscoped hTarget closed reanchorRow change
      (child.piRowOrigins resources worlds depth)
  | _, _, _, _, .focusMinimal _ minimal bound child =>
    try simp only [SortableCert.headDepth] at depth
    exact (child.piRowOrigins resources worlds depth).focusMinimal minimal bound
  | _, _, _, _, .select _ selected child =>
    try simp only [SortableCert.headDepth] at depth
    intro atom member
    cases List.mem_singleton.mp member
    exact child.piRowOrigins resources worlds depth _ selected
  | _, _, _, _, .sortPad _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact False.elim (child.piRowOrigins resources worlds depth).not_sort
  | _, _, _, _, .support action _ child =>
    try simp only [SortableCert.headDepth] at depth
    exact WorldPiProfileOrigins.supportWith henv hscoped hTarget closed reanchorRow action
      (child.piRowOrigins resources worlds depth)
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
