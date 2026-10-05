import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls

/-! Retained route calls descend through the actual history capture, even
when the route and its enclosing variable use different source controls.
The route itself selects each reserved F/C/R phase. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

/-- The exact route reservation is present in the real group history.
There is no comparison of its source key with the enclosing variable key. -/
theorem RawGeneratedTypeRoute.reserveBelowGroupHistory
    {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (inputs : route.WorldInputs strata)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (ownerInitial : WorldEnvironmentProvenance strata U ownerEnvironment)
    (prior : WorldEnvironmentProvenance strata U priorEnvironment)
    (caller : EndpointState headerEnv U callerSource callerExpression callerType)
    (phase : RichPhase) :
    CallBelow strata.rules.length (route.worldReserve inputs).worlds
      [originalCallWorld headerControls phase caller
        (WorldEnvironmentProvenance.groupHistory field major domain ownerControls headerControls
          ownerInitial prior (route.worldReserve inputs))] := by
  apply split_call
  intro child member
  apply Below.child
  change child ∈ ((route.worldReserve inputs).append _).worlds
  rw [WorldEnvironmentProvenance.worlds_append]
  exact List.mem_append_left _ member

namespace RetainedHeaderUniverse

/-- Future execution reads the SAME retained reserve. In particular its
R endpoints are genuinely captured R worlds, rather than F worlds silently
treated as larger calls. The parent may be in an unrelated earlier source. -/
theorem replayFundingOfCaptured
    {U : Nat} {leftLevels rightLevels : List VLevel}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (parentControls : OriginalWorldControls strata parentEnv)
    (caller : EndpointState parentEnv U parentSource expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (reserved : ((route leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right).worldReserve
      (worldInputs controls leftOrigin rightOrigin leftWF rightWF equivalent below common registry target left right)).worlds
        ⊆ captured.worlds) :
    let equality := original rightOrigin leftWF rightWF equivalent
    let parent := originalCallWorld parentControls phase caller captured
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
        (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.left equality)) .nil] [parent] ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .fundamental (.ref (.left equality)) .nil] [parent] ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.right equality)) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
        (.ref (rightOrigin.familyHeader rightWF).reference) .nil] [parent] := by
  rw [worldReserve_worlds] at reserved
  dsimp only at reserved ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply split_call
    intro child member
    apply Below.child
    apply reserved
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self
    · cases List.mem_singleton.mp member
      exact List.mem_cons_of_mem _ List.mem_cons_self
  · apply split_call
    intro child member
    apply Below.child
    apply reserved
    cases List.mem_singleton.mp member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · apply split_call
    intro child member
    apply Below.child
    apply reserved
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · cases List.mem_singleton.mp member
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
