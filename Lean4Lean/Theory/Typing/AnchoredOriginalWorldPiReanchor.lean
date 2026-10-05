import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBindReservation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyEntryRestriction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbientDiagonal

/-! The concrete frames and original-world calls used when a selected Pi row
is reanchored. Diagonalization preserves the exact stored queries; the body
frame adds the actual domain certificate and its original domain closure. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Controls belong to the exact two certificates stored in this row. -/
structure RichPiRowCertificate.Controlled
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) where
  domain : ControlledStoredQuery controls frontier (.certificate row.domain)
  body : ControlledStoredQuery controls frontier (.certificate row.body)

private theorem HeaderRichTail.diagonal_storedQueries
    (tail : HeaderRichTail header field major env registry target context locals σ τ available) :
    tail.leftDiagonal.storedQueries = tail.storedQueries := by
  match tail with
  | .nil => simp only [HeaderRichTail.leftDiagonal, HeaderRichTail.storedQueries]
  | .skip tail .. => simpa only [HeaderRichTail.leftDiagonal, HeaderRichTail.storedQueries] using tail.diagonal_storedQueries
  | .push tail .. =>
    simp only [HeaderRichTail.leftDiagonal, HeaderRichTail.storedQueries,
      HeaderValueAlignment.leftDiagonal, HeaderValueAlignment.storedQueries,
      RichBinderValue.leftDiagonal, tail.diagonal_storedQueries]
termination_by sizeOf tail

private theorem HeaderBinderFrame.diagonal_storedQueries
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) :
    frame.leftDiagonal.storedQueries = frame.storedQueries := by
  match frame with
  | .captured tail => simpa only [HeaderBinderFrame.leftDiagonal, HeaderBinderFrame.storedQueries] using tail.diagonal_storedQueries
  | .bind tail .. =>
    simp only [HeaderBinderFrame.leftDiagonal, HeaderBinderFrame.storedQueries,
      tail.diagonal_storedQueries]
termination_by sizeOf frame

mutual
 theorem RawOriginalRichFrame.diagonal_storedQueries
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    frame.leftDiagonal.storedQueries = frame.storedQueries := by
  match frame with
  | .nil => simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries]
  | .reserve frame .. => simpa only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries] using frame.diagonal_storedQueries
  | .merge left right =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries,
      left.diagonal_storedQueries, right.diagonal_storedQueries]
  | .header _ _ frame => simpa only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries] using frame.diagonal_storedQueries
  | .bind frame .. | .capture frame .. =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries,
      frame.diagonal_storedQueries]
  | .group frame _ _ _ entries =>
    simp only [RawOriginalRichFrame.leftDiagonal, RawOriginalRichFrame.storedQueries,
      entries.diagonal_storedQueries, frame.diagonal_storedQueries]
 termination_by sizeOf frame
 decreasing_by all_goals simp_wf <;> omega

 theorem RawRichGroupEntry.diagonal_storedQueries
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.leftDiagonal.storedQueries = entry.storedQueries := by
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ query _ answer =>
    simp only [RawRichGroupEntry.leftDiagonal, RawRichGroupEntry.storedQueries,
      HeaderValueAlignment.leftDiagonal, HeaderValueAlignment.storedQueries,
      RichBinderValue.leftDiagonal, frame.diagonal_storedQueries]
 termination_by sizeOf entry
 decreasing_by all_goals simp_wf <;> omega

 theorem RawRichGroupEntries.diagonal_storedQueries
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    entries.leftDiagonal.storedQueries = entries.storedQueries := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.storedQueries]
  | .cons entry rest =>
    simp only [RawRichGroupEntries.leftDiagonal, RawRichGroupEntries.storedQueries,
      entry.diagonal_storedQueries, rest.diagonal_storedQueries]
 termination_by sizeOf entries
 decreasing_by all_goals simp_wf <;> omega
end

/-- Actual stored queries are copied unchanged by the diagonal frame. -/
theorem OriginalRichFrame.diagonal_queryControls
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    {frontier : List (World strata.rules.length)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ready : ∀ query ∈ frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query)) :
    ∀ query ∈ frame.leftDiagonal.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query) := by
  simpa only [OriginalRichFrame.leftDiagonal, RawOriginalRichFrame.diagonal_storedQueries] using ready

private theorem piRowWorldChildren
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (captured : WorldEnvironmentProvenance strata U environment) :
    let parent := originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.ref domain) captured) parent ∧
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental body
      (reservedBindWorldEnvironment controls domain captured captured)) parent := by
  have domainCost := binder_domain_cost (domain.dependencyOrigin controls.ordered)
    [body.dependencyOrigin controls.ordered] [] environment
  have domainBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref domain) captured)
      (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured) :=
    original_child (richSchedule_strict domainCost _ _) _ _ _ _ _
  have bodyBelow := (reservedBindWorld_pi_children controls domain body hu hv captured).2
  exact ⟨domainBelow, bodyBelow⟩

/-- Both original formation children are proper world descendants of the
same Pi. The body retains the actual newly bound domain world as a child,
not a duplicate token in the measured call frontier. -/
theorem piRowWorldFunding
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (captured : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length)) :
    let parent := originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref domain) captured]) (frontier ++ [parent]) ∧
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental body
        (reservedBindWorldEnvironment controls domain captured captured)]) (frontier ++ [parent]) := by
  obtain ⟨domainBelow, bodyBelow⟩ := piRowWorldChildren controls domain body hu hv captured
  have first := split_call (calls := [originalCallWorld controls .fundamental (.ref domain) captured])
    (fun child member => by cases List.mem_singleton.mp member; exact domainBelow)
  have second := split_call (calls := [originalCallWorld controls .fundamental body
      (reservedBindWorldEnvironment controls domain captured captured)])
    (fun child member => by cases List.mem_singleton.mp member; exact bodyBelow)
  dsimp only
  induction frontier with
  | nil => exact ⟨first, second⟩
  | cons sponsor rest ih => exact ⟨ih.1.cons sponsor, ih.2.cons sponsor⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
