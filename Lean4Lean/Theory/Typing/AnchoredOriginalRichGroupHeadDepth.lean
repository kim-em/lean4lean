import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceResourceClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHeadDepth

/-! A grouped source slot bounds every actual occurrence frame and whole
query as well as both type certificates. Selecting a need retains one such
entry; it never reconstructs the owner's frame from certificate availability. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

noncomputable def RichGroupedCaptureEntry.headDepth (policy : Name → Nat → Nat)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) : Nat :=
  max (entry.frame.headDepth policy)
    (max (entry.query.headDepth policy) (entry.answer.headDepth policy))

noncomputable def RichGroupedCapture.headDepth (policy : Name → Nat → Nat)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) : Nat :=
  match entries with
  | [] => 0
  | entry :: rest => max (entry.headDepth policy) (RichGroupedCapture.headDepth policy rest)

@[simp] theorem RichGroupedCaptureEntry.headDepth_toRaw (policy : Name → Nat → Nat)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    entry.toRaw.headDepth policy = entry.headDepth policy := by
  simp only [RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.headDepth,
    RichGroupedCaptureEntry.headDepth, OriginalRichFrame.headDepth]

@[simp] theorem richGroupedEntriesRaw_headDepth (policy : Name → Nat → Nat)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (richGroupedEntriesRaw entries).headDepth policy = entries.headDepth policy := by
  induction entries with
  | nil => simp only [richGroupedEntriesRaw, RawRichGroupEntries.headDepth, RichGroupedCapture.headDepth]
  | cons entry rest ih =>
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.headDepth, RichGroupedCapture.headDepth,
      RichGroupedCaptureEntry.headDepth_toRaw, ih]

/-- The actual semantic group constructor retains the complete owner-side
budget, not only the externally visible replacement certificates. -/
theorem OriginalRichFrame.headDepth_group (policy : Name → Nat → Nat)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (tail : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (capturedOrdered : sourceEnv.Ordered) (ownerInitial : List Closure)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (OriginalRichFrame.group tail domain capturedOrdered ownerInitial entries).headDepth policy =
      max (entries.headDepth policy) (tail.headDepth policy) := by
  simp only [OriginalRichFrame.headDepth, OriginalRichFrame.group, RawOriginalRichFrame.headDepth,
    richGroupedEntriesRaw_headDepth]

theorem RichGroupedCapture.entry_headDepth_le (policy : Name → Nat → Nat)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : entry ∈ entries) : entry.headDepth policy ≤ entries.headDepth policy := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)


theorem RichGroupedCapture.headDepth_headerAvailableMono
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) (policy : Name → Nat → Nat) :
    (entries.headerAvailableMono included).headDepth policy = entries.headDepth policy := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    change max (entry.headerAvailableMono included |>.headDepth policy)
      (RichGroupedCapture.headDepth policy (RichGroupedCapture.headerAvailableMono tail included)) = _
    rw [ih]
    rfl

/-- The operative history-group resource return changes only its selected
header tail and availability proofs. All owner queries/alignment certificates
keep exactly the same named masks; the identical history reserve is retained. -/
theorem OriginalRichFrame.headDepth_historyGroup_return
    (policy : Name → Nat → Nat)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (previous : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (next : OriginalRichFrame headerEnv env U registry target context locals σ τ nextAvailable)
    (included : ∀ index need, need ∈ available index → need ∈ nextAvailable index)
    (tailBound : next.headDepth policy ≤ previous.headDepth policy)
    (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
    {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
    {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue)
    (reserve : List Closure) :
    ((OriginalRichFrame.group next domain ownerOrdered ownerInitial
      (entries.headerAvailableMono included)).reserve reserve).headDepth policy ≤
      ((OriginalRichFrame.group previous domain ownerOrdered ownerInitial entries).reserve reserve).headDepth policy := by
  simp only [OriginalRichFrame.headDepth_reserve, OriginalRichFrame.headDepth_group,
    RichGroupedCapture.headDepth_headerAvailableMono]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans tailBound (Nat.le_max_right _ _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
