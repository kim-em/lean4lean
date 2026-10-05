import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyPiStoredRow
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainOrigins

/-! Joint legacy row and provenance selection. The returned body annotation
is a literal child of the given annotation, on the very same selected row. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldLegacyRowsProvenance.storedCursor
    {strata : EquationStratification env}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    {rows : PiRows env U registry target locals σ A B ambient table footprint}
    (annotation : WorldLegacyRowsProvenance strata rows)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available true key result,
    ∃ bodyAnnotation : WorldSortableCertProvenance strata row.body.certificate,
      row.ambient = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain (SortableCert.ofCode domain domain.formed) ∧ row.body.programSize < sizeOf rows ∧
      bodyAnnotation.worlds ⊆ annotation.worlds ∧
      ∀ policy, row.body.certificate.headDepth policy ≤ rows.headDepth policy := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, .ofCode domain domain.formed, domainAvailable, guard, _, .plain body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩,
        .ofCode body body.formed bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_⟩
      · simp only [LegacyRowBody.programSize]
        simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [LegacyRowBody.certificate, SortableCert.headDepth, PiRows.headDepth]
        exact Nat.le_max_left _ _
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth⟩ :=
        tailAnnotation.storedCursor domain domainAvailable
          (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [PiRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation

theorem WorldSortableRowsProvenance.storedCursor
    {strata : EquationStratification env}
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    {rows : SortableRows env U registry target locals σ A B relevant ambient table footprint}
    (annotation : WorldSortableRowsProvenance strata rows)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available relevant key result,
    ∃ bodyAnnotation : WorldSortableCertProvenance strata row.body.certificate,
      row.ambient = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain (domain) ∧ row.body.programSize < sizeOf rows ∧
      bodyAnnotation.worlds ⊆ annotation.worlds ∧
      ∀ policy, row.body.certificate.headDepth policy ≤ rows.headDepth policy := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, domain, domainAvailable, guard, _, .sortable body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩,
        bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_⟩
      · simp only [LegacyRowBody.programSize]
        simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [LegacyRowBody.certificate, SortableRows.headDepth]
        exact Nat.le_max_left _ _
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth⟩ :=
        tailAnnotation.storedCursor domain domainAvailable
          (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [SortableRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
