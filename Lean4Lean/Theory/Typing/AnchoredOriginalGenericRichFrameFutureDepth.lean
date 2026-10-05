import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameDepth

/-! Future transport preserves the declaration budget on the very same
retained original frame, including grouped owners and captured arguments. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

@[simp] theorem HeaderValueAlignment.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    (answer.future henv future).nativeDepth current = answer.nativeDepth current := by
  simp only [nativeDepth, HeaderValueAlignment.future, RichBinderValue.future,
    RichCert.nativeDepth_future]

private theorem HeaderRichTail.nativeDepth_mpr (current : Name → Bool)
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : HeaderRichTail header field major env registry target context locals left right available =
      HeaderRichTail header field major env registry target context locals nextLeft nextRight nextAvailable)
    (tail : HeaderRichTail header field major env registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr tail).nativeDepth current = tail.nativeDepth current := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

@[simp] theorem HeaderRichTail.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    (tail.future henv future).nativeDepth current = tail.nativeDepth current := by
  match tail with
  | .nil => simp only [HeaderRichTail.future, nativeDepth]
  | .skip tail domain location lineage arguments =>
    simp only [HeaderRichTail.future]
    refine (nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push, List.map_nil]
    · simp only [nativeDepth, tail.nativeDepth_future current henv future]
  | .push tail domain location lineage owner answer arguments needs bounded covered =>
    simp only [HeaderRichTail.future]
    refine (nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future, lift'_subst]
    · simp only [subst_cons_future, lift'_subst]
    · simp only [Valuation.rename_push]
    · simp only [nativeDepth, tail.nativeDepth_future current henv future,
        HeaderValueAlignment.nativeDepth_future]
termination_by sizeOf tail
decreasing_by all_goals simp_wf <;> omega

private theorem HeaderBinderFrame.nativeDepth_mpr (current : Name → Bool)
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : HeaderBinderFrame header field major env registry target context locals left right available =
      HeaderBinderFrame header field major env registry target context locals nextLeft nextRight nextAvailable)
    (frame : HeaderBinderFrame header field major env registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr frame).nativeDepth current = frame.nativeDepth current := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

@[simp] theorem HeaderBinderFrame.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available) :
    (frame.future henv future).nativeDepth current = frame.nativeDepth current := by
  match frame with
  | .captured tail => simp only [HeaderBinderFrame.future, nativeDepth, HeaderRichTail.nativeDepth_future]
  | .bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    simp only [HeaderBinderFrame.future]
    refine (nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [nativeDepth, tail.nativeDepth_future current henv future, RichCert.nativeDepth_future]
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

private theorem RawOriginalRichFrame.nativeDepth_mpr (current : Name → Bool)
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : RawOriginalRichFrame sourceEnv env U registry target context locals left right available =
      RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr frame).nativeDepth current = frame.nativeDepth current := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

private theorem RawRichGroupEntries.nativeDepth_cast (current : Name → Bool)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (needsEq : needs = nextNeeds)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    (needsEq ▸ entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue nextNeeds).nativeDepth
      current = entries.nativeDepth current := by
  cases needsEq
  rfl

mutual
@[simp] theorem RawOriginalRichFrame.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    (frame.future henv future).nativeDepth current = frame.nativeDepth current := by
  match frame with
  | .nil => simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.nativeDepth]
  | .reserve frame closures =>
    simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.nativeDepth, frame.nativeDepth_future current henv future]
  | .merge left right =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.nativeDepth_mpr current rfl rfl ?_ _ _).trans ?_
    · simp only [Valuation.rename_append]
    · simp only [RawOriginalRichFrame.nativeDepth, left.nativeDepth_future current henv future,
        right.nativeDepth_future current henv future]
  | .header capturedOrdered initial frame =>
    simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.nativeDepth, HeaderBinderFrame.nativeDepth_future]
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.nativeDepth, tail.nativeDepth_future current henv future,
        RichCert.nativeDepth_future]
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.nativeDepth, tail.nativeDepth_future current henv future,
        RichCert.nativeDepth_future, RichObs.nativeDepth_future]
  | .group tail domain capturedOrdered initial entries =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.nativeDepth_mpr current ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.nativeDepth, tail.nativeDepth_future current henv future,
        entries.nativeDepth_future current henv future]
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem RawRichGroupEntry.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entry : RawRichGroupEntry (U := U) (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    (entry.future henv future).nativeDepth current = entry.nativeDepth current := by
  match entry with
  | .mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix
      sourceEq depthEq expressionEq leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer =>
    rw [RawRichGroupEntry.future]
    simp only [RawRichGroupEntry.nativeDepth, frame.nativeDepth_future current henv future,
      RichObs.nativeDepth_future, HeaderValueAlignment.nativeDepth_future]
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem RawRichGroupEntries.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entries : RawRichGroupEntries (U := U) (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    (entries.future henv future).nativeDepth current = entries.nativeDepth current := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.future, RawRichGroupEntries.nativeDepth]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.future]
    rw [RawRichGroupEntries.nativeDepth_cast]
    simp only [RawRichGroupEntries.nativeDepth, entry.nativeDepth_future current henv future,
      tail.nativeDepth_future current henv future]
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

@[simp] theorem OriginalRichFrame.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    (frame.future henv future).nativeDepth current = frame.nativeDepth current :=
  frame.raw.nativeDepth_future current henv future

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
