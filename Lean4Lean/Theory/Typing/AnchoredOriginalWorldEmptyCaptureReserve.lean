import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistorySponsorship
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation

/-! The reserve of an actual empty parameter capture is sponsored by its
original projection. The owner frame is retained through both its literal
dependency environment and its world ledger; numerical capacity alone does
not justify the calls saved in this reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem ProjectionHead.emptyCaptureReserve_sponsored
    {strata : EquationStratification env}
    {outer : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned}
    (head : OriginalFactorCut.ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (majorLocation : Located (.right head.major) (.ref major))
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (captured : WorldEnvironmentProvenance strata U sourceEnvironment)
    (sameEnvironment : ownerInitial = sourceEnvironment)
    (sameWorlds : initial.worlds = captured.worlds)
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (headerEarlier : headerControls.ordered.constantCount < sourceControls.ordered.constantCount)
    (sameCutoff : headerControls.cutoff = sourceControls.cutoff)
    (sameFuel : headerControls.fuel = sourceControls.fuel)
    (priorPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer captured] prior.worlds)
    (route : WorldEnvironmentProvenance strata U routeEnvironment)
    (routePaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer captured] route.worlds) :
    Sponsored [originalCallWorld sourceControls .assignedComparison outer captured]
      (WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
        initial prior route).worlds := by
  have sameCall {e T : VExpr} (node : EndpointState sourceEnv U source e T) (phase : RichPhase) :
      originalCallWorld sourceControls phase node initial =
        originalCallWorld sourceControls phase node captured := by
    simp only [originalCallWorld, sameEnvironment, sameWorlds]
  have fieldPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer captured]
      [originalCallWorld sourceControls .expressionReindex (.ref field) initial] := by
    rw [sameCall]
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      ProjectionHead.parameterOwner_below head field fieldEq .here sourceControls captured _ _⟩
  have majorPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer captured]
      [originalCallWorld sourceControls .expressionReindex (.ref major) initial] := by
    rw [sameCall]
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      ProjectionHead.parameter_below head majorLocation sourceControls captured _ _⟩
  have domainPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer captured]
      [originalCallWorld headerControls .expressionReindex (.ref domain) prior] := by
    intro child member
    cases List.mem_singleton.mp member
    refine ⟨_, List.mem_singleton_self _, Below.root ?_ ?_⟩
    · simpa only [originalCallWorld, sameCutoff, sameFuel] using
        (EquationControlMeasure.constantsDecrease headerEarlier
          strata.rules.length sourceControls.cutoff sourceControls.fuel _ _ : _)
    · intro child member
      obtain ⟨parent, present, below⟩ := priorPaid child member
      cases List.mem_singleton.mp present
      exact below
  exact WorldEnvironmentProvenance.groupHistory_sponsored sourceControls headerControls initial prior
    fieldPaid majorPaid domainPaid priorPaid route routePaid


theorem ProjectionHead.emptyCaptureReserve_retargetedSponsored
    {strata : EquationStratification env}
    {outer : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned}
    (head : OriginalFactorCut.ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (majorLocation : Located (.right head.major) (.ref major))
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial)
    (captured : WorldEnvironmentProvenance strata U sourceEnvironment)
    (sameEnvironment : ownerInitial = sourceEnvironment)
    (sameWorlds : initial.worlds = captured.worlds)
    (outerWorld : WorldEnvironmentProvenance strata U outerEnvironment)
    (capacity : environmentCost sourceEnvironment ≤ environmentCost outerEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds outerWorld.worlds)
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (headerEarlier : headerControls.ordered.constantCount < sourceControls.ordered.constantCount)
    (sameCutoff : headerControls.cutoff = sourceControls.cutoff)
    (sameFuel : headerControls.fuel = sourceControls.fuel)
    (priorPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld] prior.worlds)
    (route : WorldEnvironmentProvenance strata U routeEnvironment)
    (routePaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld] route.worlds) :
    Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      (WorldEnvironmentProvenance.groupHistory field major domain sourceControls headerControls
        initial prior route).worlds := by
  have sameCall {e T : VExpr} (node : EndpointState sourceEnv U source e T) (phase : RichPhase) :
      originalCallWorld sourceControls phase node initial =
        originalCallWorld sourceControls phase node captured := by
    simp only [originalCallWorld, sameEnvironment, sameWorlds]
  have fieldPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      [originalCallWorld sourceControls .expressionReindex (.ref field) initial] := by
    rw [sameCall]
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      originalCallWorld_retargetBelow sourceControls outer .assignedComparison captured outerWorld capacity covered
        (ProjectionHead.parameterOwner_below head field fieldEq .here sourceControls captured _ _)⟩
  have majorPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      [originalCallWorld sourceControls .expressionReindex (.ref major) initial] := by
    rw [sameCall]
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _,
      originalCallWorld_retargetBelow sourceControls outer .assignedComparison captured outerWorld capacity covered
        (ProjectionHead.parameter_below head majorLocation sourceControls captured _ _)⟩
  have domainPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      [originalCallWorld headerControls .expressionReindex (.ref domain) prior] := by
    intro child member
    cases List.mem_singleton.mp member
    refine ⟨_, List.mem_singleton_self _, Below.root ?_ ?_⟩
    · simpa only [originalCallWorld, sameCutoff, sameFuel] using
        (EquationControlMeasure.constantsDecrease headerEarlier
          strata.rules.length sourceControls.cutoff sourceControls.fuel _ _ : _)
    · intro child member
      obtain ⟨parent, present, below⟩ := priorPaid child member
      cases List.mem_singleton.mp present
      exact below
  exact WorldEnvironmentProvenance.groupHistory_sponsored sourceControls headerControls initial prior
    fieldPaid majorPaid domainPaid priorPaid route routePaid

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
