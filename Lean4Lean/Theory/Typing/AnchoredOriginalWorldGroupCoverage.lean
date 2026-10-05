import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerReplayFunding

/-! Hereditary coverage of the actual grouped reply. Equal-cost changes to
the selected prior frame are handled by a retained reconstruction-phase
domain reservation, not by claiming equal-key world monotonicity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem covered_singleton
    {count : Nat} {world : World count} {bound : List (World count)}
    (member : world ∈ bound) : Covered (@EquationControlMeasure.Less count) [world] bound := by
  intro selected present
  cases List.mem_singleton.mp present
  exact ⟨world, member, .inl rfl⟩

section
variable {strata : EquationStratification env}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  {domain : EndpointRef headerEnv U headerSource A (.sort level)}
  (ownerControls : OriginalWorldControls strata sourceEnv)
  (headerControls : OriginalWorldControls strata headerEnv)
  (initial : WorldEnvironmentProvenance strata U ownerInitial)
  (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
  (prior : WorldEnvironmentProvenance strata U priorEnvironment)
  (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
    locals σ available ownerInitial rawCapture leftValue rightValue)

/-- The selected domain's unary interpretation spends the real retained
R-phase reservation even when its frame duplicated equal-cost captures. -/
theorem WorldEnvironmentProvenance.domainFundamental_below_reindex
    (capacity : environmentCost selectedEnvironment ≤ environmentCost priorEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds prior.worlds) :
    WorldBelow strata.rules.length
      (originalCallWorld headerControls .fundamental (.ref domain) selected)
      (originalCallWorld headerControls .expressionReindex (.ref domain) prior) := by
  apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans
    (originalCallWorld_boundedNode headerControls .expressionReindex (.ref domain) selected prior capacity covered)
  apply original_child
  simp only [richSchedule, RichPhase.code]
  omega

/-- Exact entry owners are covered by the original field/major reservations.
The selected header's domain may have a different, genuinely covered frame. -/
theorem WorldEnvironmentProvenance.group_covered_replayRoots
    (capacity : environmentCost selectedEnvironment ≤ environmentCost priorEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds prior.worlds) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (WorldEnvironmentProvenance.group ownerControls headerControls initial selected entries).worlds
      ([originalCallWorld headerControls .expressionReindex (.ref domain) prior,
        originalCallWorld ownerControls .expressionReindex (.ref field) initial,
        originalCallWorld ownerControls .expressionReindex (.ref major) initial] ++ prior.worlds) := by
  let bound := [originalCallWorld headerControls .expressionReindex (.ref domain) prior,
    originalCallWorld ownerControls .expressionReindex (.ref field) initial,
    originalCallWorld ownerControls .expressionReindex (.ref major) initial] ++ prior.worlds
  have domainCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      [originalCallWorld headerControls .fundamental (.ref domain) selected] bound := by
    intro world member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self), .inr
      (WorldEnvironmentProvenance.domainFundamental_below_reindex headerControls selected prior capacity covered)⟩
  have fieldCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      [originalCallWorld ownerControls .expressionReindex (.ref field) initial] bound :=
    covered_singleton (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have majorCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      [originalCallWorld ownerControls .expressionReindex (.ref major) initial] bound :=
    covered_singleton (List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds bound := by
    apply Covered.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans covered
    exact fun world member => ⟨world, List.mem_append_right _ member, .inl rfl⟩
  have ownerCovered (owner : HeaderOwner field major) :
      Covered (@EquationControlMeasure.Less strata.rules.length)
        (WorldEnvironmentProvenance.owner ownerControls owner initial).worlds bound := by
    cases owner with
    | inl location =>
      exact Covered.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans
        (initial.located_call_coveredAt ownerControls location.location .expressionReindex) fieldCovered
    | inr location =>
      exact Covered.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans
        (initial.located_call_coveredAt ownerControls location.location .expressionReindex) majorCovered
  have entriesCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initial selected entries).worlds bound := by
    induction entries with
    | nil => exact tailCovered
    | cons entry rest ih => exact ((ownerCovered entry.owner).merge domainCovered).merge ih
  exact domainCovered.merge ((fieldCovered.merge domainCovered).merge
    ((majorCovered.merge domainCovered).merge entriesCovered))

/-- Every retained reconstruction root is a literal member of the fixed
baseline, including its repeated domain reservations. -/
theorem WorldEnvironmentProvenance.replayRoots_subset_groupBaseline :
    ([originalCallWorld headerControls .expressionReindex (.ref domain) prior,
      originalCallWorld ownerControls .expressionReindex (.ref field) initial,
      originalCallWorld ownerControls .expressionReindex (.ref major) initial] ++ prior.worlds) ⊆
      (WorldEnvironmentProvenance.groupBaseline field major domain ownerControls headerControls initial prior).worlds := by
  intro world member
  change world ∈ [_] ++ (([_] ++ [_]) ++ (([_] ++ [_]) ++ prior.worlds))
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_append_left _ (List.mem_singleton_self _)
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
    rcases List.mem_singleton.mp member with rfl
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))))
  · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member))

/-- The actual selected group is covered by the query-independent group
baseline. Its unary domain world spends the retained reconstruction phase. -/
theorem WorldEnvironmentProvenance.group_covered_baseline
    (capacity : environmentCost selectedEnvironment ≤ environmentCost priorEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds prior.worlds) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (WorldEnvironmentProvenance.group ownerControls headerControls initial selected entries).worlds
      (WorldEnvironmentProvenance.groupBaseline field major domain ownerControls headerControls initial prior).worlds := by
  apply Covered.trans (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans
    (WorldEnvironmentProvenance.group_covered_replayRoots ownerControls headerControls initial selected prior entries capacity covered)
  exact fun world member => ⟨world,
    WorldEnvironmentProvenance.replayRoots_subset_groupBaseline ownerControls headerControls initial prior member, .inl rfl⟩

/-- Adding the actual finite type history retains the entire fixed group
baseline; no annotation is recovered from a scalar capacity bound. -/
theorem WorldEnvironmentProvenance.group_covered_history
    (route : WorldEnvironmentProvenance strata U reserve)
    (capacity : environmentCost selectedEnvironment ≤ environmentCost priorEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds prior.worlds) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (WorldEnvironmentProvenance.group ownerControls headerControls initial selected entries).worlds
      (WorldEnvironmentProvenance.groupHistory field major domain ownerControls headerControls initial prior route).worlds := by
  rw [WorldEnvironmentProvenance.groupHistory, WorldEnvironmentProvenance.worlds_append]
  apply Covered.trans (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans
    (WorldEnvironmentProvenance.group_covered_baseline ownerControls headerControls initial selected prior entries capacity covered)
  exact fun world member => ⟨world, List.mem_append_right _ member, .inl rfl⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
