import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeRows
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedRowActions
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowSelection

/-! Pending row execution selects the body and its annotation together from
the original native table. The strict descent concerns that retained body,
before any pending input, anchor, or output operation is executed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem WorldRowsProvenance.nativeCursor
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
    ∃ bodyAnnotation : WorldCertProvenance strata row.body,
      row.domainSupport = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      bodyAnnotation.worlds ⊆ annotation.worlds ∧
      ∀ policy, row.body.headDepth policy ≤ rows.headDepth policy := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
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
        bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [RichRows.headDepth]
        exact Nat.le_max_left _ _
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth⟩ := tailAnnotation.nativeCursor domain
        domainAvailable (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [RichRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation

/-- The operative pending row receives controls on the SAME strict native
child. No eager reanchoring or F result is used as the recursive body. -/
theorem PendingNativeRow.controlledCursor
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (pending : PendingNativeRow env U registry target table relevant nextRelevant key result)
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domain))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
    ∃ ready : row.Controlled controls frontier,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ready.body.annotation.worlds ⊆ annotation.worlds ∧
      ∀ policy, row.body.headDepth policy ≤ rows.headDepth policy := by
  obtain ⟨row, child, supportEq, footprintEq, same, smaller, worlds, depth⟩ :=
    annotation.nativeCursor domain domainAvailable resources pending.member
  have domainReady' : ControlledStoredQuery controls frontier (.certificate row.domain) := by
    cases row
    dsimp only at supportEq footprintEq same ⊢
    cases supportEq
    cases footprintEq
    cases same
    exact domainReady
  let bodyReady : ControlledStoredQuery controls frontier (.certificate row.body) := {
    annotation := child
    within := fun control active => Nat.le_trans (depth _) (within control active)
    sponsored := fun world present => sponsored world (worlds present) }
  exact ⟨row, ⟨domainReady', bodyReady⟩, same, smaller, worlds, depth⟩

/-- Full output-path selection retains controls on the original body even
when pending row operations change rank, input, domain, anchor, or support. -/
theorem WorldRowsProvenance.pathNativeCursor
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {nextAmbient : Profile m} {nextTable : List (Key m × Profile m)}
    {key : Key m} {result : Profile m}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domain))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody nextAmbient nextTable))
    (member : (key, result) ∈ nextTable) :
    ∃ pending : RankedPendingNativeRow env U registry target table relevant key result,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
    ∃ ready : row.Controlled controls frontier,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ready.body.annotation.worlds ⊆ annotation.worlds ∧
      ∀ policy, row.body.headDepth policy ≤ rows.headDepth policy := by
  obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result member
  obtain ⟨row, child, supportEq, footprintEq, same, smaller, worlds, depth⟩ :=
    annotation.nativeCursor domain domainAvailable resources pending.member
  have domainReady' : ControlledStoredQuery controls frontier (.certificate row.domain) := by
    cases row
    dsimp only at supportEq footprintEq same ⊢
    cases supportEq
    cases footprintEq
    cases same
    exact domainReady
  let bodyReady : ControlledStoredQuery controls frontier (.certificate row.body) := {
    annotation := child
    within := fun control active => Nat.le_trans (depth _) (within control active)
    sponsored := fun world present => sponsored world (worlds present) }
  exact ⟨pending, row, ⟨domainReady', bodyReady⟩, same, smaller, worlds, depth⟩

/-- The selected body is a strict child of the actual annotation program.
The supplied budget bounds the incoming program, not a newly built query. -/
theorem WorldRowsProvenance.nativeCursorSized
    {strata : EquationStratification env}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (budget : Nat) (annotationBound : sizeOf annotation ≤ budget)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
    ∃ bodyAnnotation : WorldCertProvenance strata row.body,
      row.domainSupport = ambient ∧ row.domainFootprint = domainFootprint ∧
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      bodyAnnotation.worlds ⊆ annotation.worlds ∧
      (∀ policy, row.body.headDepth policy ≤ rows.headDepth policy) ∧
      sizeOf bodyAnnotation < budget := by
  match annotation with
  | .nil => cases member
  | .cons guard body pack covered tail bodyAnnotation tailAnnotation =>
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
        bodyAnnotation, rfl, rfl, HEq.rfl, ?_, ?_, ?_, ?_⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_left _ present
      · intro policy
        simp only [RichRows.headDepth]
        exact Nat.le_max_left _ _
      · apply Nat.lt_of_lt_of_le _ annotationBound
        simp_wf
        omega
    · obtain ⟨row, next, supportEq, footprintEq, same, smaller, worlds, depth, annotationSmaller⟩ := tailAnnotation.nativeCursorSized domain
        budget (by apply Nat.le_trans _ annotationBound; simp_wf) domainAvailable (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, next, supportEq, footprintEq, same, ?_, ?_, ?_, annotationSmaller⟩
      · simp_wf
        omega
      · exact fun _ present => List.mem_append_right _ (worlds present)
      · intro policy
        simp only [RichRows.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
termination_by sizeOf annotation


/-- Mixed-rank row selection keeps the same strict annotation child. -/
theorem WorldRowsProvenance.pathNativeCursorSized
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {nextAmbient : Profile m} {nextTable : List (Key m × Profile m)}
    {key : Key m} {result : Profile m}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (budget : Nat) (annotationBound : sizeOf annotation ≤ budget)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domain))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds)
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody nextAmbient nextTable))
    (member : (key, result) ∈ nextTable) :
    ∃ pending : RankedPendingNativeRow env U registry target table relevant key result,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
    ∃ ready : row.Controlled controls frontier,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ready.body.annotation.worlds ⊆ annotation.worlds ∧
      (∀ policy, row.body.headDepth policy ≤ rows.headDepth policy) ∧
      sizeOf (show WorldCertProvenance strata row.body from ready.body.annotation) < budget := by
  obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result member
  obtain ⟨row, child, supportEq, footprintEq, same, smaller, worlds, depth, annotationSmaller⟩ :=
    annotation.nativeCursorSized domain budget annotationBound domainAvailable resources pending.member
  have domainReady' : ControlledStoredQuery controls frontier (.certificate row.domain) := by
    cases row
    dsimp only at supportEq footprintEq same ⊢
    cases supportEq
    cases footprintEq
    cases same
    exact domainReady
  let bodyReady : ControlledStoredQuery controls frontier (.certificate row.body) := {
    annotation := child
    within := fun control active => Nat.le_trans (depth _) (within control active)
    sponsored := fun world present => sponsored world (worlds present) }
  exact ⟨pending, row, ⟨domainReady', bodyReady⟩, same, smaller, worlds, depth, annotationSmaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
