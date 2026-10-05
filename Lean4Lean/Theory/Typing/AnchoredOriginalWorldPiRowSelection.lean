import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowOperations

/-! Selecting a Pi row retains the annotations of the exact selected body
and domain, including legacy certificates attached to actual original nodes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}

theorem WorldLegacyRowsProvenance.selectPiRow
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    {rows : PiRows env U registry target locals σ A B ambient table footprint}
    (annotation : WorldLegacyRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate (node := domainNode) (.legacy (.ofCode domain domain.formed))))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available true domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    simp only [PiRows.headDepth] at within
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨{
        domainSupport := ambient
        domainFootprint := domainFootprint
        domain := .legacy (.ofCode domain domain.formed)
        domainAvailable := domainAvailable
        inputTyped := guard.inputTyped
        alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
        anchor := guard.anchor
        bodyFootprint := _
        body := .legacy (.ofCode body body.formed)
        packed := _
        outside := _
        pack := pack
        covered := covered
        outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) },
        ⟨⟨domainReady, ⟨.legacy _ (.ofCode body body.formed bodyAnnotation), ?_, ?_⟩⟩⟩⟩
      · intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth] using
          Nat.le_trans (Nat.le_max_left _ _) (within control active)
      · intro world present
        exact sponsored world (List.mem_append_left _ present)
    · exact tailAnnotation.selectPiRow domain domainReady domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (within control active))
        (fun world present => sponsored world (List.mem_append_right _ present)) member
termination_by sizeOf annotation

theorem WorldSortableRowsProvenance.selectPiRow
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    {rows : SortableRows env U registry target locals σ A B relevant ambient table footprint}
    (annotation : WorldSortableRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate (node := domainNode) (.legacy domain)))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    simp only [SortableRows.headDepth] at within
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨{
        domainSupport := ambient
        domainFootprint := domainFootprint
        domain := .legacy domain
        domainAvailable := domainAvailable
        inputTyped := guard.inputTyped
        alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
        anchor := guard.anchor
        bodyFootprint := _
        body := .legacy body
        packed := _
        outside := _
        pack := pack
        covered := covered
        outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) },
        ⟨⟨domainReady, ⟨.legacy body bodyAnnotation, ?_, ?_⟩⟩⟩⟩
      · intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth] using
          Nat.le_trans (Nat.le_max_left _ _) (within control active)
      · intro world present
        exact sponsored world (List.mem_append_left _ present)
    · exact tailAnnotation.selectPiRow domain domainReady domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (within control active))
        (fun world present => sponsored world (List.mem_append_right _ present)) member
termination_by sizeOf annotation

theorem WorldRowsProvenance.selectPiRow
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate (node := domainNode) (domain)))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
    simp only [RichRows.headDepth] at within
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨{
        domainSupport := ambient
        domainFootprint := domainFootprint
        domain := domain
        domainAvailable := domainAvailable
        inputTyped := guard.inputTyped
        alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
        anchor := guard.anchor
        bodyFootprint := _
        body := body
        packed := _
        outside := _
        pack := pack
        covered := covered
        outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) },
        ⟨⟨domainReady, ⟨bodyAnnotation, ?_, ?_⟩⟩⟩⟩
      · intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth] using
          Nat.le_trans (Nat.le_max_left _ _) (within control active)
      · intro world present
        exact sponsored world (List.mem_append_left _ present)
    · exact tailAnnotation.selectPiRow domain domainReady domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (within control active))
        (fun world present => sponsored world (List.mem_append_right _ present)) member
termination_by sizeOf annotation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
