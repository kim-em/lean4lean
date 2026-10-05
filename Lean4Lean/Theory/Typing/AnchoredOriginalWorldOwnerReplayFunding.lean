import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerEnvironment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldStaticCallBounds

/-! A grouped capture retains the reconstruction phase of its actual owner.
The recursive bank uses that fixed original reservation, while the selected
owner frame is admitted separately by its capacity and world coverage. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

section
variable {strata : EquationStratification env}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  {domain : EndpointRef headerEnv U headerSource A (.sort level)}
  (ownerControls : OriginalWorldControls strata sourceEnv)
  (headerControls : OriginalWorldControls strata headerEnv)
  (initial : WorldEnvironmentProvenance strata U ownerInitial)
  (prior : WorldEnvironmentProvenance strata U priorEnvironment)
  (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
    locals σ available ownerInitial rawCapture leftValue rightValue)
  {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
    locals σ available ownerInitial rawCapture leftValue rightValue}

private theorem groupEntries_owner_reindex_mem (present : entry ∈ entries) :
    originalCallWorld ownerControls .expressionReindex entry.owner.node
      (entry.owner.worldEnvironment ownerControls initial) ∈
      (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initial prior entries).worlds := by
  have ownerMember : originalCallWorld ownerControls .expressionReindex entry.owner.node
      (entry.owner.worldEnvironment ownerControls initial) ∈
      (WorldEnvironmentProvenance.owner ownerControls entry.owner initial).worlds := by
    rw [entry.owner.worldEnvironment_owner]
    exact List.mem_singleton_self _
  induction entries with
  | nil => cases present
  | cons selected rest ih =>
    change _ ∈ (_ ++ _) ++ _
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_append_left _ (List.mem_append_left _ ownerMember)
    · exact List.mem_append_right _ (ih present)

/-- This is membership of the actual retained owner reservation, with its
own source controls and original location-derived capture environment. -/
theorem WorldEnvironmentProvenance.group_owner_reindex_mem (present : entry ∈ entries) :
    originalCallWorld ownerControls .expressionReindex entry.owner.node
      (entry.owner.worldEnvironment ownerControls initial) ∈
      (WorldEnvironmentProvenance.group ownerControls headerControls initial prior entries).worlds := by
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (groupEntries_owner_reindex_mem ownerControls headerControls initial prior entries present)))

/-- The owner can be reconstructed even when its checking source is later
than the header's. The strict edge is actual capture descent, not a comparison
of those two source counts or a reversed same-cost F-to-R phase edge. -/
theorem WorldEnvironmentProvenance.group_owner_reindex_below
    (present : entry ∈ entries)
    (node : EndpointState headerEnv U current expression assigned)
    (phase : RichPhase)
    (history : WorldEnvironmentProvenance strata U historyEnvironment) :
    CallBelow strata.rules.length
      [originalCallWorld ownerControls .expressionReindex entry.owner.node
        (entry.owner.worldEnvironment ownerControls initial)]
      [originalCallWorld headerControls phase node
        (history.append (WorldEnvironmentProvenance.group ownerControls headerControls initial prior entries))] := by
  apply split_call
  intro child member
  cases List.mem_singleton.mp member
  apply Below.child
  rw [WorldEnvironmentProvenance.worlds_append]
  exact List.mem_append_right _
    (WorldEnvironmentProvenance.group_owner_reindex_mem ownerControls headerControls initial prior entries present)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
