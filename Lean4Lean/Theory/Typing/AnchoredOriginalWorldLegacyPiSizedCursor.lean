import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiCursor

/-! Literal legacy annotation programs remain separate from the harmless
SortableCert wrapper used by row attachment. Recursive descent measures the
actual CodeCert or SortableCert annotation selected from the stored table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

inductive WorldLegacyRowBodyProvenance (strata : EquationStratification env) :
    {relevant : Bool} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    LegacyRowBody env U registry target locals σ expression relevant profile footprint → Type where
  | plain {body : CodeCert env U registry target locals σ expression profile footprint}
      (child : WorldLegacyCertProvenance strata body) :
      WorldLegacyRowBodyProvenance strata (.plain body)
  | sortable {body : SortableCert env U registry target locals σ expression relevant profile footprint}
      (child : WorldSortableCertProvenance strata body) :
      WorldLegacyRowBodyProvenance strata (.sortable body)

noncomputable def WorldLegacyRowBodyProvenance.programSize
    {body : LegacyRowBody env U registry target locals σ expression relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata body) : Nat :=
  match annotation with
  | .plain child => sizeOf child
  | .sortable child => sizeOf child

noncomputable def WorldLegacyRowBodyProvenance.certificate
    {body : LegacyRowBody env U registry target locals σ expression relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata body) :
    WorldSortableCertProvenance strata body.certificate :=
  match annotation with
  | .plain child => .ofCode _ _ child
  | .sortable child => child

theorem WorldLegacyRowsProvenance.storedCursorSized
    {strata : EquationStratification env}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    {rows : PiRows env U registry target locals σ A B ambient table footprint}
    (annotation : WorldLegacyRowsProvenance strata rows)
    (budget : Nat) (annotationBound : sizeOf annotation ≤ budget)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available true key result,
    ∃ bodyAnnotation : WorldLegacyRowBodyProvenance strata row.body,
      row.ambient = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain (SortableCert.ofCode domain domain.formed) ∧ row.body.programSize < sizeOf rows ∧
      bodyAnnotation.certificate.worlds ⊆ annotation.worlds ∧
      (∀ policy, row.body.certificate.headDepth policy ≤ rows.headDepth policy) ∧
      bodyAnnotation.programSize < budget := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, .ofCode domain domain.formed, domainAvailable, guard, _, .plain body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩,
        .plain bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_, ?_⟩
      · simp only [LegacyRowBody.programSize]
        simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [LegacyRowBody.certificate, SortableCert.headDepth, PiRows.headDepth]
        exact Nat.le_max_left _ _
      · apply Nat.lt_of_lt_of_le _ annotationBound
        simp only [WorldLegacyRowBodyProvenance.programSize]
        simp_wf
        omega
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth, annotationSmaller⟩ :=
        tailAnnotation.storedCursorSized domain budget (by apply Nat.le_trans _ annotationBound; simp_wf) domainAvailable
          (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_, annotationSmaller⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [PiRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation

theorem WorldSortableRowsProvenance.storedCursorSized
    {strata : EquationStratification env}
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    {rows : SortableRows env U registry target locals σ A B relevant ambient table footprint}
    (annotation : WorldSortableRowsProvenance strata rows)
    (budget : Nat) (annotationBound : sizeOf annotation ≤ budget)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available relevant key result,
    ∃ bodyAnnotation : WorldLegacyRowBodyProvenance strata row.body,
      row.ambient = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain (domain) ∧ row.body.programSize < sizeOf rows ∧
      bodyAnnotation.certificate.worlds ⊆ annotation.worlds ∧
      (∀ policy, row.body.certificate.headDepth policy ≤ rows.headDepth policy) ∧
      bodyAnnotation.programSize < budget := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, domain, domainAvailable, guard, _, .sortable body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩,
        .sortable bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_, ?_⟩
      · simp only [LegacyRowBody.programSize]
        simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [LegacyRowBody.certificate, SortableRows.headDepth]
        exact Nat.le_max_left _ _
      · apply Nat.lt_of_lt_of_le _ annotationBound
        simp only [WorldLegacyRowBodyProvenance.programSize]
        simp_wf
        omega
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth, annotationSmaller⟩ :=
        tailAnnotation.storedCursorSized domain budget (by apply Nat.le_trans _ annotationBound; simp_wf) domainAvailable
          (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_, annotationSmaller⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [SortableRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
