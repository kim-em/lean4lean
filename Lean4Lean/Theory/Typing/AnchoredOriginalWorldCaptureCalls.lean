import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureBounds
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureBundle
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! The own-capture producer's actual original calls decrease in the shared
world order. The captured ledger is built from the same argument, domain,
and tail as the returned frame; no caller-supplied cost inequality is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def ownCaptureWorldEnvironment
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (captured : WorldEnvironmentProvenance strata U environment) :
    WorldEnvironmentProvenance strata U
      ([Closure.bundle (.close (argument.dependencyOrigin controls.ordered) environment)
        (.close (domain.dependencyOrigin controls.ordered) environment)] ++
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) environment)
        (.close (domain.dependencyOrigin controls.ordered) environment) :: environment)) :=
  reservedCaptureWorldEnvironment controls domain argument captured captured

/-- The variable's actual capture ledger contains both original owners.
Each child keeps the old tail, whose worlds occur literally in that ledger. -/
theorem ownCaptureWorldFunding
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (captured : WorldEnvironmentProvenance strata U environment) :
    let parent := originalCallWorld controls .fundamental variableNode
      (ownCaptureWorldEnvironment controls domain argument captured)
    CallBelow strata.rules.length
      [originalCallWorld controls .fundamental argument captured] [parent] ∧
    CallBelow strata.rules.length
      [originalCallWorld controls .expressionReindex argument.typeFormation.node captured,
       originalCallWorld controls .expressionReindex (.ref domain) captured] [parent] := by
  have bundleBound := capturedVariable_bundle_lt (variableNode.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (domain.dependencyOrigin controls.ordered) environment
  have argumentBound := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bundleBound
  have domainBound := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bundleBound
  have formationBound := Nat.lt_of_le_of_lt
    (argument.typeFormation_dependency_cost_le controls.ordered environment) argumentBound
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds (ownCaptureWorldEnvironment controls domain argument captured).worlds := by
    intro world member
    refine ⟨world, ?_, .inl rfl⟩
    change world ∈ _ ++ (_ ++ captured.worlds)
    exact List.mem_append_right _ (List.mem_append_right _ member)
  have lower {expression type : VExpr} {node : EndpointState sourceEnv U source expression type} (phase : RichPhase)
      (cost : (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) environment).cost <
        (OriginalClosureMeasure.Closure.close (variableNode.dependencyOrigin controls.ordered)
          (OriginalClosureMeasure.Closure.bundle
            (.close (argument.dependencyOrigin controls.ordered) environment)
            (.close (domain.dependencyOrigin controls.ordered) environment) :: environment)).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node captured)
        (originalCallWorld controls .fundamental variableNode
          (ownCaptureWorldEnvironment controls domain argument captured)) := by
    apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict (by
        simpa only [Closure.cost, List.cons_append, List.nil_append, environmentCost, ← Nat.max_assoc, Nat.max_self] using cost) _ _) _ _ _ _) covered
  dsimp only
  constructor
  · apply split_call
    intro world member
    cases List.mem_singleton.mp member
    exact lower .fundamental argumentBound
  · apply split_call
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact lower .expressionReindex formationBound
    · cases List.mem_singleton.mp member
      exact lower .expressionReindex domainBound

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
