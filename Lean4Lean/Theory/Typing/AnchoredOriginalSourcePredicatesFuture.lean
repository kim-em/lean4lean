import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicates
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameFuture

/-! Future target insertion preserves the original source stage of every
retained owner frame. The source predicate is independent of target syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem RawRichGroupEntries.allSources_cast
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (needsEq : needs = nextNeeds)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    (needsEq ▸ entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue nextNeeds).AllSources P ↔
      entries.AllSources P := by
  cases needsEq
  rfl

private theorem RawOriginalRichFrame.allSources_mpr
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : RawOriginalRichFrame sourceEnv env U registry target context locals left right available =
      RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr frame).AllSources P ↔ frame.AllSources P := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

mutual
theorem RawOriginalRichFrame.AllSources.future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (sources : frame.AllSources P) : (frame.future henv future).AllSources P := by
  match frame with
  | .nil =>
    simpa only [RawOriginalRichFrame.future, RawOriginalRichFrame.AllSources.eq_def] using sources
  | .reserve frame closures =>
    rw [RawOriginalRichFrame.future]
    rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
    exact ⟨sources.1, RawOriginalRichFrame.AllSources.future henv future frame sources.2⟩
  | .merge left right =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.allSources_mpr rfl rfl ?_ _ _).mpr ?_
    · simp only [Valuation.rename_append]
    · rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
      exact ⟨sources.1, RawOriginalRichFrame.AllSources.future henv future left sources.2.1,
        RawOriginalRichFrame.AllSources.future henv future right sources.2.2⟩
  | .header .. =>
    simpa only [RawOriginalRichFrame.future, RawOriginalRichFrame.AllSources.eq_def] using sources
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.allSources_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
      exact ⟨sources.1, RawOriginalRichFrame.AllSources.future henv future tail sources.2⟩
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.allSources_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
      exact ⟨sources.1, RawOriginalRichFrame.AllSources.future henv future tail sources.2⟩
  | .group tail domain capturedOrdered initial entries =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.allSources_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · rw [RawOriginalRichFrame.AllSources.eq_def] at sources ⊢
      exact ⟨sources.1, RawOriginalRichFrame.AllSources.future henv future tail sources.2.1,
        sources.2.2.1, RawRichGroupEntries.AllSources.future henv future entries sources.2.2.2⟩
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.AllSources.future
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (sources : entry.AllSources P) : (entry.future henv future).AllSources P := by
  match entry with
  | .mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix
      sourceEq depthEq expressionEq leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer =>
    rw [RawRichGroupEntry.future, RawRichGroupEntry.AllSources.eq_def]
    apply RawOriginalRichFrame.AllSources.future henv future frame
    simpa only [RawRichGroupEntry.AllSources.eq_def] using sources
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.AllSources.future
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (sources : entries.AllSources P) : (entries.future henv future).AllSources P := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.future, RawRichGroupEntries.AllSources.eq_def]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.future]
    rw [RawRichGroupEntries.allSources_cast]
    rw [RawRichGroupEntries.AllSources.eq_def] at sources ⊢
    exact ⟨RawRichGroupEntry.AllSources.future henv future entry sources.1,
      RawRichGroupEntries.AllSources.future henv future tail sources.2⟩
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

theorem OriginalRichFrame.AllSources.future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (sources : frame.AllSources P) : (frame.future henv future).AllSources P :=
  RawOriginalRichFrame.AllSources.future henv future frame.raw sources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
