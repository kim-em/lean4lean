import Lean4Lean.Theory.Typing.AnchoredRecordRequestRetag
import Lean4Lean.Theory.Typing.AnchoredAtomActionInterpretation

/-! Finite covariant field-output actions. The original frozen domain and
anchor remain literal; both semantic legs and the complete support are mapped
by the same action. No new anchor admission is supplied. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The exact output request, including its computed support. -/
noncomputable def fieldOutputRequest (request : DataRequest (Profile n))
    (action : AtomAction env U registry Γ (atom : Atom n) output) : DataRequest (Profile n) :=
  ⟨⟨request.domain, request.anchor, .singleton output⟩, action.support.apply request.support⟩

theorem RequestAdmission.outputAction
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {request : DataRequest (Profile n)}
    (admitted : RequestAdmission env U (relations env U registry n) Γ request left right)
    (selected : atom ∈ request.input.atoms)
    (action : AtomAction env U registry Γ atom output) :
    RequestAdmission env U (relations env U registry n) Γ
      (fieldOutputRequest request action) left right := by
  obtain ⟨anchor, pair, typed, supported, code, first, second⟩ := admitted.singleton selected
  exact ⟨anchor, pair, action.typed typed, action.support.preservesSort supported,
    action.support.codeMap henv hscoped code,
    action.termMap henv hscoped formed typed first,
    action.termMap henv hscoped formed typed second⟩

/-- A finite occurrence-indexed change. Unselected fields are retained exactly;
duplicate field indices do not identify distinct stored requests. -/
inductive RecordFieldOutputs (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : List (Nat × DataRequest (Profile n)) →
      List (Nat × DataRequest (Profile n)) → Type where
  | nil : RecordFieldOutputs env U registry Γ [] []
  | keep (entry : Nat × DataRequest (Profile n))
      (tail : RecordFieldOutputs env U registry Γ before after) :
      RecordFieldOutputs env U registry Γ (entry :: before) (entry :: after)
  | action (index : Nat) (request : DataRequest (Profile n))
      (selected : atom ∈ request.input.atoms)
      (change : AtomAction env U registry Γ atom output)
      (tail : RecordFieldOutputs env U registry Γ before after) :
      RecordFieldOutputs env U registry Γ ((index, request) :: before)
        ((index, fieldOutputRequest request change) :: after)

theorem RecordFieldOutputs.origin
    (program : RecordFieldOutputs env U registry Γ before after)
    (member : entry ∈ after) :
    ∃ old ∈ before, old.1 = entry.1 ∧ old.2.domain = entry.2.domain := by
  induction program with
  | nil => cases member
  | keep head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨old, present, same⟩ := ih member
      exact ⟨old, List.mem_cons_of_mem _ present, same⟩
  | action index request selected change tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨old, present, same⟩ := ih member
      exact ⟨old, List.mem_cons_of_mem _ present, same⟩

/-- Full field admissions in an actual private world. Every transported output
uses the same private insertion as the original record witness. -/
theorem RecordFieldOutputs.argumentsMixed
    {before after : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (insertion : MixedInsertion env U Γ Δ ρ)
    (program : RecordFieldOutputs env U registry Γ before after)
    (fields : Arguments env U (relations env U registry n) Δ
      (before.map fun entry => entry.2.rename ρ)
      (before.map fun entry => .proj name entry.1 left)
      (before.map fun entry => .proj name entry.1 right)) :
    Arguments env U (relations env U registry n) Δ
      (after.map fun entry => entry.2.rename ρ)
      (after.map fun entry => .proj name entry.1 left)
      (after.map fun entry => .proj name entry.1 right) := by
  induction program with
  | nil => exact .nil
  | keep entry tail ih =>
    cases fields with
    | cons first rest => exact .cons first (ih rest)
  | action index request selected change tail ih =>
    cases fields with
    | cons first rest =>
      have member : _ ∈ (request.rename ρ).input.atoms :=
        List.mem_map.mpr ⟨_, selected, rfl⟩
      have changed := first.outputAction henv hscoped (insertion.targetWF henv formed)
        member (change.mixed henv insertion)
      have equal : fieldOutputRequest (request.rename ρ) (change.mixed henv insertion) =
          (fieldOutputRequest request change).rename ρ := by
        simp only [fieldOutputRequest, DataRequest.rename, DataRequest.map, KeyData.map,
          AtomAction.support_mixed, ← SupportAction.apply_mixed, Profile.rename_singleton]
      rw [equal] at changed
      exact .cons changed (ih rest)

theorem RecordWitness.outputFields
    {newFields : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : RecordWitness env U registry (relations env U registry n) Γ left right type record)
    (program : RecordFieldOutputs env U registry Γ record.fields newFields) :
    Nonempty (RecordWitness env U registry (relations env U registry n) Γ left right type
      { record with fields := newFields }) := by
  refine ⟨{ witness with
    bounded := ?_
    leftOrigins := ?_
    rightOrigins := ?_
    fields := program.argumentsMixed henv hscoped witness.baseWF witness.insertion witness.fields }⟩
  · intro entry member
    obtain ⟨old, present, indexEq, _⟩ := program.origin member
    simpa only [← indexEq] using witness.bounded old present
  · intro entry member
    obtain ⟨old, present, indexEq, domainEq⟩ := program.origin member
    simpa only [← indexEq, ← domainEq] using witness.leftOrigins old present
  · intro entry member
    obtain ⟨old, present, indexEq, domainEq⟩ := program.origin member
    simpa only [← indexEq, ← domainEq] using witness.rightOrigins old present

noncomputable def RecordFieldOutputs.future
    {before after : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (insertion : FutureInsertion env U Γ Δ ρ)
    (program : RecordFieldOutputs env U registry Γ before after) :
    RecordFieldOutputs env U registry Δ
      (before.map fun entry => (entry.1, entry.2.rename ρ))
      (after.map fun entry => (entry.1, entry.2.rename ρ)) := by
  induction program with
  | nil => exact .nil
  | keep entry tail ih => exact .keep _ ih
  | action index request selected change tail ih =>
    have member : _ ∈ (request.rename ρ).input.atoms := List.mem_map.mpr ⟨_, selected, rfl⟩
    have next := RecordFieldOutputs.action index (request.rename ρ) member
      (change.future henv insertion) ih
    have equal : fieldOutputRequest (request.rename ρ) (change.future henv insertion) =
        (fieldOutputRequest request change).rename ρ := by
      simp only [fieldOutputRequest, DataRequest.rename, DataRequest.map, KeyData.map,
        AtomAction.support_future, ← SupportAction.apply_future, Profile.rename_singleton]
    rw [equal] at next
    exact next

theorem RecordRelation.outputFields
    {newFields : List (Nat × DataRequest (Profile n))}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (related : RecordRelation env U registry (relations env U registry n) Γ left right type record)
    (program : RecordFieldOutputs env U registry Γ record.fields newFields) :
    RecordRelation env U registry (relations env U registry n) Γ left right type
      { record with fields := newFields } := by
  intro Δ ρ insertion
  obtain ⟨witness⟩ := related Δ ρ insertion
  exact witness.outputFields henv hscoped (program.future henv insertion)

end Lean4Lean.AnchoredSemantics.RankedData
