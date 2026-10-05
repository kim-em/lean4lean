import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateParameterWorldCalls

/-! Actual retained-family history ledgers remain below their original
projection. Later header domains may capture earlier parameter histories;
constant descent pays their root and inherited sponsorship pays those exact
captures. Entry owners are taken from their actual field/major locations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem sponsored_covered
    {count : Nat} {uses roots frontier : List (World count)}
    (covered : Covered (@EquationControlMeasure.Less count) uses roots)
    (sponsored : Sponsored frontier roots) : Sponsored frontier uses := by
  intro world member
  obtain ⟨root, present, rfl | smaller⟩ := covered world member
  · exact sponsored _ present
  · obtain ⟨sponsor, present, below⟩ := sponsored root present
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans smaller below⟩

theorem WorldEnvironmentProvenance.owner_sponsored
    {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (controls : OriginalWorldControls strata sourceEnv)
    (initial : WorldEnvironmentProvenance strata U environment)
    (owner : HeaderOwner field major)
    {frontier : List (World strata.rules.length)}
    (fieldReady : Sponsored frontier [originalCallWorld controls .expressionReindex (.ref field) initial])
    (majorReady : Sponsored frontier [originalCallWorld controls .expressionReindex (.ref major) initial]) :
    Sponsored frontier (WorldEnvironmentProvenance.owner controls owner initial).worlds := by
  cases owner with
  | inl selected => exact sponsored_covered (initial.located_call_coveredAt controls selected.location .expressionReindex) fieldReady
  | inr selected => exact sponsored_covered (initial.located_call_coveredAt controls selected.location .expressionReindex) majorReady

/-- The earlier source can carry an already retained parameter prefix.
Every actual captured world must still have its existing caller sponsor. -/
theorem originalRetainedHeader_below
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (node : EndpointState origin.source U headerSource expression assigned)
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment)
    (phase callerPhase : RichPhase)
    (inherited : Sponsored [originalCallWorld controls callerPhase caller captured] prior.worlds) :
    WorldBelow strata.rules.length
      (originalCallWorld (controls.atHeader origin) phase node prior)
      (originalCallWorld controls callerPhase caller captured) := by
  apply Below.root (EquationControlMeasure.constantsDecrease (origin.count_lt controls.ordered) _ _ _ _ _)
  intro child member
  obtain ⟨sponsor, present, below⟩ := inherited child member
  cases List.mem_singleton.mp present
  exact below

section
variable {strata : EquationStratification env}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  {domain : EndpointRef headerEnv U headerSource A (.sort level)}
  (ownerControls : OriginalWorldControls strata sourceEnv)
  (headerControls : OriginalWorldControls strata headerEnv)
  (initial : WorldEnvironmentProvenance strata U ownerInitial)
  (prior : WorldEnvironmentProvenance strata U priorEnvironment)
  {frontier : List (World strata.rules.length)}
  (fieldReady : Sponsored frontier [originalCallWorld ownerControls .expressionReindex (.ref field) initial])
  (majorReady : Sponsored frontier [originalCallWorld ownerControls .expressionReindex (.ref major) initial])
  (domainReady : Sponsored frontier [originalCallWorld headerControls .expressionReindex (.ref domain) prior])
  (priorReady : Sponsored frontier prior.worlds)

include fieldReady majorReady domainReady priorReady

private theorem domainFundamental_sponsored :
    Sponsored frontier [originalCallWorld headerControls .fundamental (.ref domain) prior] := by
  intro child member
  cases List.mem_singleton.mp member
  obtain ⟨sponsor, present, smaller⟩ := domainReady _ (List.mem_singleton_self _)
  refine ⟨sponsor, present, EquationWorldClosureOrder.trans
    (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans ?_ smaller⟩
  apply original_child
  simp only [richSchedule, RichPhase.code]
  omega

private theorem groupEntries_sponsored
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue) :
    Sponsored frontier (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initial prior entries).worlds := by
  have domainF := domainFundamental_sponsored ownerControls headerControls initial prior
    fieldReady majorReady domainReady priorReady
  induction entries with
  | nil => exact priorReady
  | cons entry rest ih =>
    exact ((WorldEnvironmentProvenance.owner_sponsored ownerControls initial entry.owner fieldReady majorReady).merge
      domainF).merge ih

theorem WorldEnvironmentProvenance.group_sponsored
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue) :
    Sponsored frontier (WorldEnvironmentProvenance.group ownerControls headerControls initial prior entries).worlds := by
  have domainF := domainFundamental_sponsored ownerControls headerControls initial prior
    fieldReady majorReady domainReady priorReady
  exact domainF.merge ((fieldReady.merge domainF).merge ((majorReady.merge domainF).merge
    (groupEntries_sponsored ownerControls headerControls initial prior fieldReady majorReady domainReady priorReady entries)))

theorem WorldEnvironmentProvenance.groupHistory_sponsored
    (route : WorldEnvironmentProvenance strata U reserve)
    (routeReady : Sponsored frontier route.worlds) :
    Sponsored frontier (WorldEnvironmentProvenance.groupHistory field major domain
      ownerControls headerControls initial prior route).worlds := by
  rw [WorldEnvironmentProvenance.groupHistory, WorldEnvironmentProvenance.worlds_append]
  exact routeReady.merge (domainReady.merge ((fieldReady.merge domainReady).merge
    ((majorReady.merge domainReady).merge priorReady)))
end

/-- The real field, major, earlier header domain, and every entry owner
pay for the history reserve and actual grouped frame at the SAME projection.
The two inherited premises are precisely the previous prefix and the actual
route reserve, produced by the finite-family fold. -/
theorem ProjectionHead.familyHistory_sponsored
    {strata : EquationStratification env}
    {outer : EndpointState sourceEnv U source (.proj name index majorExpression) assigned}
    (head : OriginalFactorCut.ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    (major : EndpointRef sourceEnv U source selectedExpression selectedType)
    (majorLocation : Located (.right head.major) (.ref major))
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U ownerInitial)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (domain : EndpointRef origin.source U headerSource A (.sort level))
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds prior.worlds)
    (route : WorldEnvironmentProvenance strata U reserve)
    (priorReady : Sponsored [originalCallWorld controls .assignedComparison outer captured] prior.worlds)
    (routeReady : Sponsored [originalCallWorld controls .assignedComparison outer captured] route.worlds)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture leftValue rightValue) :
    Sponsored [originalCallWorld controls .assignedComparison outer captured]
      ((WorldEnvironmentProvenance.groupHistory field major domain controls (controls.atHeader origin)
        captured prior route).append
        (WorldEnvironmentProvenance.group controls (controls.atHeader origin) captured selected entries)).worlds := by
  have fieldReady : Sponsored [originalCallWorld controls .assignedComparison outer captured]
      [originalCallWorld controls .expressionReindex (.ref field) captured] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      ProjectionHead.parameterOwner_below head field fieldEq .here controls captured _ _⟩
  have majorReady : Sponsored [originalCallWorld controls .assignedComparison outer captured]
      [originalCallWorld controls .expressionReindex (.ref major) captured] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      ProjectionHead.parameter_below head majorLocation controls captured _ _⟩
  have domainReady : Sponsored [originalCallWorld controls .assignedComparison outer captured]
      [originalCallWorld (controls.atHeader origin) .expressionReindex (.ref domain) prior] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      originalRetainedHeader_below controls origin (.ref domain) prior outer captured _ _ priorReady⟩
  have selectedReady := sponsored_covered selectedCovered priorReady
  have selectedDomainReady : Sponsored [originalCallWorld controls .assignedComparison outer captured]
      [originalCallWorld (controls.atHeader origin) .expressionReindex (.ref domain) selected] := by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      originalRetainedHeader_below controls origin (.ref domain) selected outer captured _ _ selectedReady⟩
  rw [WorldEnvironmentProvenance.worlds_append]
  exact (WorldEnvironmentProvenance.groupHistory_sponsored controls (controls.atHeader origin) captured prior
    fieldReady majorReady domainReady priorReady route routeReady).merge
    (WorldEnvironmentProvenance.group_sponsored controls (controls.atHeader origin) captured selected
      fieldReady majorReady selectedDomainReady selectedReady entries)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
