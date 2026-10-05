import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderFrameTransportMeasure

/-! Future target contexts transport the whole generic source frame,
including every heterogeneous owner frame and both retained alignment
certificates. Original source occurrences and capture spines are unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
open private renamedBound renamedCoverage from Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFuture
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem captureNeeds_rename (profile : Profile n) (ρ : Lift) :
    captureNeeds (profile.rename ρ) = (captureNeeds profile).map (Need.rename ρ) := by
  simp only [captureNeeds, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_append, List.map_nil]
  rw [← Need.singletons_rename]
  rfl

mutual
noncomputable def RawOriginalRichFrame.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    {context : ContextDerivation sourceEnv U source}
    (frame : RawOriginalRichFrame sourceEnv env U registry Γ context locals σ τ available) :
    RawOriginalRichFrame sourceEnv env U registry Δ context locals (σ.lift_r ρ) (τ.lift_r ρ)
      (available.rename ρ) := by
  match frame with
  | .nil => exact .nil
  | .reserve frame closures => exact .reserve (frame.future henv future) closures
  | .merge left right =>
    simpa only [Valuation.rename_append] using
      RawOriginalRichFrame.merge (left.future henv future) (right.future henv future)
  | .header capturedOrdered initial header => exact .header capturedOrdered initial (header.future henv future)
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    have shifted := arguments.future henv future
    rw [lift'_subst] at shifted
    simpa only [subst_cons_future, Valuation.rename_push] using
      RawOriginalRichFrame.bind (tail.future henv future) domain (certificate.future henv future)
        (resources.rename ρ) (Profile.rename_hasType_iff.mpr typed) shifted
        (needs.map (Need.rename ρ)) (renamedBound needs ρ bounded) (renamedCoverage needs ρ covered)
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    have shifted := arguments.future henv future
    rw [lift'_subst] at shifted
    simpa only [subst_cons_future, Valuation.rename_push] using
      RawOriginalRichFrame.capture (tail.future henv future) domain initialContext argument
        argumentLocation argumentLineage (argumentQuery.future henv future) (argumentAvailable.rename ρ)
        (certificate.future henv future) (resources.rename ρ) (Profile.rename_hasType_iff.mpr typed) shifted
        (needs.map (Need.rename ρ)) (renamedBound needs ρ bounded) (renamedCoverage needs ρ covered)
  | .group tail domain capturedOrdered initial entries =>
    simpa only [subst_cons_future, Valuation.rename_push] using
      RawOriginalRichFrame.group (tail.future henv future) domain capturedOrdered initial (entries.future henv future)
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntry.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (entry : RawRichGroupEntry (U := U) (field := field) (major := major) domain env registry Γ
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    RawRichGroupEntry (field := field) (major := major) domain env registry Δ headerLocals
      (declaredLeft.lift_r ρ) (headerAvailable.rename ρ) ownerInitial rawCapture
      (leftValue.lift' ρ) (rightValue.lift' ρ) n (input.rename ρ) := by
  match entry with
  | .mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix
      sourceEq depthEq expressionEq leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer =>
    exact .mk owner ownerLocals (ownerLeft.lift_r ρ) (ownerRight.lift_r ρ) (ownerAvailable.rename ρ)
      initialContext (frame.future henv future) (substitutions.future henv future) depth sourcePrefix
      sourceEq depthEq expressionEq (by simpa only [lift'_subst] using congrArg (fun e => e.lift' ρ) leftEq)
      (by simpa only [lift'_subst] using congrArg (fun e => e.lift' ρ) rightEq)
      queryRank (queryInput.rename ρ) queryBound
      (by simpa only [raiseProfile_rename] using queryAdapter.future henv future)
      (Footprint.rename ρ footprint) (query.future henv future) (queryAvailable.rename ρ) (answer.future henv future)
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (entries : RawRichGroupEntries (U := U) (field := field) (major := major) domain env registry Γ
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    RawRichGroupEntries (field := field) (major := major) domain env registry Δ headerLocals
      (declaredLeft.lift_r ρ) (headerAvailable.rename ρ) ownerInitial rawCapture
      (leftValue.lift' ρ) (rightValue.lift' ρ) (needs.map (Need.rename ρ)) := by
  match entries with
  | .nil => exact .nil
  | .cons (input := input) (needs := needs) entry tail =>
    have same : captureNeeds (input.rename ρ) ++ needs.map (Need.rename ρ) =
        (captureNeeds input ++ needs).map (Need.rename ρ) := by
      rw [captureNeeds_rename, List.map_append]
    exact same ▸ RawRichGroupEntries.cons (entry.future henv future) (tail.future henv future)
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

private theorem RawRichGroupEntries.ownerClosures_cast
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (needsEq : needs = nextNeeds)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (ordered : sourceEnv.Ordered) (declared : Closure) :
    (needsEq ▸ entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue nextNeeds).ownerClosures
      ordered declared = entries.ownerClosures ordered declared := by
  cases needsEq
  rfl

theorem RawRichGroupEntries.ownerClosures_future
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (ordered : sourceEnv.Ordered) (declared : Closure) :
    (entries.future henv future).ownerClosures ordered declared = entries.ownerClosures ordered declared := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.future, ownerClosures]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.future]
    rw [ownerClosures_cast]
    cases entry
    rw [RawRichGroupEntry.future]
    simp only [ownerClosures, RawRichGroupEntry.owner,
      tail.ownerClosures_future henv future ordered declared]
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega

private theorem RawOriginalRichFrame.dependencyEnvironment_mpr
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : RawOriginalRichFrame sourceEnv env U registry target context locals left right available =
      RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable)
    (ordered : sourceEnv.Ordered) :
    (equal.mpr frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

theorem RawOriginalRichFrame.dependencyEnvironment_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (frame.future henv future).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  match frame with
  | .nil => simp only [RawOriginalRichFrame.future, dependencyEnvironment]
  | .reserve frame closures =>
    simp only [RawOriginalRichFrame.future, dependencyEnvironment, frame.dependencyEnvironment_future henv future ordered]
  | .merge left right =>
    simp only [RawOriginalRichFrame.future]
    refine (dependencyEnvironment_mpr rfl rfl ?_ _ _ ordered).trans ?_
    · simp only [Valuation.rename_append]
    · simp only [dependencyEnvironment, left.dependencyEnvironment_future henv future ordered,
        right.dependencyEnvironment_future henv future ordered]
  | .header capturedOrdered initial frame =>
    simpa only [RawOriginalRichFrame.future, dependencyEnvironment] using frame.dependencyEnvironment_future henv future ordered capturedOrdered initial
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (dependencyEnvironment_mpr ?_ ?_ ?_ _ _ ordered).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [dependencyEnvironment, tail.dependencyEnvironment_future henv future ordered]
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (dependencyEnvironment_mpr ?_ ?_ ?_ _ _ ordered).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [dependencyEnvironment, tail.dependencyEnvironment_future henv future ordered]
  | .group tail domain capturedOrdered initial entries =>
    simp only [RawOriginalRichFrame.future]
    refine (dependencyEnvironment_mpr ?_ ?_ ?_ _ _ ordered).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [dependencyEnvironment, tail.dependencyEnvironment_future henv future ordered,
        entries.ownerClosures_future henv future capturedOrdered]
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

private theorem RawRichGroupEntries.valid_cast
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (needsEq : needs = nextNeeds)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    (needsEq ▸ entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue nextNeeds).Valid ↔
      entries.Valid := by
  cases needsEq
  rfl

private theorem RawOriginalRichFrame.valid_mpr
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : RawOriginalRichFrame sourceEnv env U registry target context locals left right available =
      RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr frame).Valid ↔ frame.Valid := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

mutual
theorem RawOriginalRichFrame.valid_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (valid : frame.Valid) : (frame.future henv future).Valid := by
  match frame with
  | .nil => simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.Valid]
  | .reserve frame closures =>
    simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.Valid] at valid ⊢
    exact frame.valid_future henv future valid
  | .merge left right =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.valid_mpr rfl rfl ?_ _ _).mpr ?_
    · simp only [Valuation.rename_append]
    · simp only [RawOriginalRichFrame.Valid] at valid ⊢
      exact ⟨left.valid_future henv future valid.1, right.valid_future henv future valid.2⟩
  | .header .. => simp only [RawOriginalRichFrame.future, RawOriginalRichFrame.Valid]
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.valid_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.Valid] at valid ⊢
      exact tail.valid_future henv future valid
  | .capture tail domain initialContext argument argumentLocation argumentLineage argumentQuery argumentAvailable
      certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.valid_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.Valid] at valid ⊢
      exact tail.valid_future henv future valid
  | .group tail domain capturedOrdered initial entries =>
    simp only [RawOriginalRichFrame.future]
    refine (RawOriginalRichFrame.valid_mpr ?_ ?_ ?_ _ _).mpr ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simp only [RawOriginalRichFrame.Valid] at valid ⊢
      exact ⟨tail.valid_future henv future valid.1, entries.valid_future henv future valid.2⟩
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.valid_future
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (valid : entry.frame.Valid)
    (bounded : ∀ ordered : sourceEnv.Ordered,
      environmentCost (entry.frame.dependencyEnvironment ordered) ≤
        environmentCost (entry.owner.dependencyEnvironment ordered ownerInitial)) :
    (entry.future henv future).frame.Valid ∧
      ∀ ordered : sourceEnv.Ordered,
        environmentCost ((entry.future henv future).frame.dependencyEnvironment ordered) ≤
          environmentCost ((entry.future henv future).owner.dependencyEnvironment ordered ownerInitial) := by
  match entry with
  | .mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix
      sourceEq depthEq expressionEq leftEq rightEq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer =>
    rw [RawRichGroupEntry.future]
    simp only [RawRichGroupEntry.frame, RawRichGroupEntry.owner] at valid bounded ⊢
    refine ⟨frame.valid_future henv future valid, ?_⟩
    intro ordered
    simpa only [frame.dependencyEnvironment_future henv future ordered] using bounded ordered
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.valid_future
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (valid : entries.Valid) : (entries.future henv future).Valid := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.future, RawRichGroupEntries.Valid]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.future]
    rw [RawRichGroupEntries.valid_cast]
    simp only [RawRichGroupEntries.Valid] at valid ⊢
    have head := entry.valid_future henv future valid.1 valid.2.1
    exact ⟨head.1, head.2, tail.valid_future henv future valid.2.2⟩
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega

end

/-- Future target transport retains the entire original formation spine,
including every heterogeneous captured owner and its actual source frame. -/
noncomputable def OriginalRichFrame.future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry next context locals (σ.lift_r ρ) (τ.lift_r ρ)
      (available.rename ρ) :=
  ⟨frame.raw.future henv future, frame.raw.valid_future henv future frame.valid⟩

@[simp] theorem OriginalRichFrame.dependencyEnvironment_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (frame.future henv future).dependencyEnvironment ordered = frame.dependencyEnvironment ordered :=
  frame.raw.dependencyEnvironment_future henv future ordered

noncomputable def OriginalRichOccurrenceFrame.future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (occurrence : OriginalRichOccurrenceFrame (U := U) location initialContext env registry target locals σ τ available
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame location initialContext env registry next locals (σ.lift_r ρ) (τ.lift_r ρ)
      (available.rename ρ) ordered initialEnvironment :=
  ⟨occurrence.frame.future henv future, occurrence.substitutions.future henv future,
    by simpa only [OriginalRichFrame.dependencyEnvironment_future] using occurrence.environment_le⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
