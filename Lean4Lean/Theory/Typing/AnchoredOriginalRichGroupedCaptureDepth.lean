import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameDepth

/-! A grouped source slot bounds every actual occurrence frame and whole
query as well as both type certificates. Selecting a need retains one such
entry; it never reconstructs the owner's frame from certificate availability. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichGroupedCaptureEntry.nativeDepth (current : Name → Bool)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) : Nat :=
  max (entry.frame.nativeDepth current)
    (max (entry.query.nativeDepth current) (entry.answer.nativeDepth current))

noncomputable def RichGroupedCapture.nativeDepth (current : Name → Bool)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) : Nat :=
  match entries with
  | [] => 0
  | entry :: rest => max (entry.nativeDepth current) (RichGroupedCapture.nativeDepth current rest)

@[simp] theorem RichGroupedCaptureEntry.nativeDepth_toRaw (current : Name → Bool)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    entry.toRaw.nativeDepth current = entry.nativeDepth current := by
  simp only [RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.nativeDepth,
    RichGroupedCaptureEntry.nativeDepth, OriginalRichFrame.nativeDepth]

@[simp] theorem richGroupedEntriesRaw_nativeDepth (current : Name → Bool)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (richGroupedEntriesRaw entries).nativeDepth current = entries.nativeDepth current := by
  induction entries with
  | nil => simp only [richGroupedEntriesRaw, RawRichGroupEntries.nativeDepth, RichGroupedCapture.nativeDepth]
  | cons entry rest ih =>
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.nativeDepth, RichGroupedCapture.nativeDepth,
      RichGroupedCaptureEntry.nativeDepth_toRaw, ih]

/-- The actual semantic group constructor retains the complete owner-side
budget, not only the externally visible replacement certificates. -/
theorem OriginalRichFrame.nativeDepth_group (current : Name → Bool)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (tail : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (capturedOrdered : sourceEnv.Ordered) (ownerInitial : List Closure)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (OriginalRichFrame.group tail domain capturedOrdered ownerInitial entries).nativeDepth current =
      max (entries.nativeDepth current) (tail.nativeDepth current) := by
  simp only [OriginalRichFrame.nativeDepth, OriginalRichFrame.group, RawOriginalRichFrame.nativeDepth,
    richGroupedEntriesRaw_nativeDepth]

theorem RichGroupedCapture.entry_depth_le (current : Name → Bool)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : entry ∈ entries) : entry.nativeDepth current ≤ entries.nativeDepth current := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private theorem lowerProfile_sortFlags {n N : Nat} (bound : n ≤ N) (profile : Profile N) :
    (lowerProfile n bound profile).sortFlags = profile.sortFlags := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      rw [lowerProfile_self]
    · have prior : n ≤ N := by omega
      rw [lowerProfile_step prior]
      exact ih prior profile.down

/-- Keep the assigned-code interpretation from the actual aligned answer,
including when the requested value profile is empty. Deriving this code from
the value relation would discard independently requested type information. -/
theorem RichGroupedCapture.lookup_supportedAllDepth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : need ∈ entries.needs) :
    ∃ entry, entry ∈ entries ∧ ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
        true (support : Profile need.rank) footprint,
      footprint.Available headerAvailable ∧ need.profile.HasType support ∧
      Related env U registry target leftValue rightValue (A.subst declaredLeft) need.profile support ∧
      TypeRelated env U registry target (A.subst declaredLeft) (A.subst declaredLeft) support ∧
      support.sortFlags = entry.answer.value.support.sortFlags ∧
      ∀ current, max (certificate.nativeDepth current) (entry.nativeDepth current) ≤ entries.nativeDepth current := by
  obtain ⟨entry, entryMember, member⟩ := List.mem_flatMap.mp member
  have bounded := (captureNeeds_covered entry.input need member).1
  have covered := (captureNeeds_covered entry.input need member).2
  simp only [Need.atGrade, dif_pos bounded] at covered
  have typed := lowerProfile.hasType bounded (typed_subset covered entry.answer.value.typed)
  have related : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
      (entry.owner.expression.subst entry.ownerRight) (A.subst declaredLeft)
      (raiseProfile entry.rank bounded need.profile) entry.answer.value.support :=
    Related.of_singletons (fun atom hm => (entry.answer.related henv).singleton_of_mem (covered atom hm))
  have lowered := lowerProfile.related bounded henv formed related
  rw [entry.left_eq, entry.right_eq] at lowered
  refine ⟨entry, entryMember, _, entry.answer.aligned.footprint,
    entry.answer.aligned.certificate.lower need.rank bounded,
    entry.answer.aligned.resources, typed, lowered,
    ((entry.answer.aligned.related.symm henv
      entry.answer.value.typed.wf_type).left_diagonal).lower henv bounded,
    lowerProfile_sortFlags bounded _, ?_⟩
  intro current
  have selected := entries.entry_depth_le current entryMember
  apply Nat.max_le.mpr ⟨?_, selected⟩
  rw [RichCert.nativeDepth_lower]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) selected))

/-- The returned certificate and every retained owner-side obligation use
the very entry selected by finite footprint membership. -/
theorem RichGroupedCapture.lookup_allDepth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : need ∈ entries.needs) :
    ∃ entry, entry ∈ entries ∧ ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
        true (support : Profile need.rank) footprint,
      footprint.Available headerAvailable ∧ need.profile.HasType support ∧
      Related env U registry target leftValue rightValue (A.subst declaredLeft) need.profile support ∧
      ∀ current, max (certificate.nativeDepth current) (entry.nativeDepth current) ≤ entries.nativeDepth current := by
  obtain ⟨entry, member, support, footprint, certificate, resources, typed, related, _, _, depth⟩ :=
    entries.lookup_supportedAllDepth henv formed member
  exact ⟨entry, member, support, footprint, certificate, resources, typed, related, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
