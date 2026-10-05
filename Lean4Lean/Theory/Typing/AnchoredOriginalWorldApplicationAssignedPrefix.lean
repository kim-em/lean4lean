import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationBackwardStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix

/-! Keep the actual type comparison while crossing a function application's
conversion prefix. In a dependent family spine this relation is needed to
compare the next declared domain; keeping only the returned certificate
would lose the caller Pi that exposed that domain. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

local notation "leftDisplay" => OriginalNestedDisplay.ofOccurrence initial (Located.appFunction location) graph

/-- The comparison pair is computed below the actual outer application;
neither an all-budget bank nor a strict-decrease premise is supplied. -/
theorem AmbientBoundedParameterReply.functionPrefixWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {naturalType : VExpr}
    (natural : EndpointState sourceEnv U source f naturalType)
    (route : PrefixRoute sourceEnv U source f function natural)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (incoming : AmbientBoundedParameterReply base caps start (leftDisplay).formationDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost baselineEnvironment))
    (incomingData : WorldParameterReplyData (P := P) controls baseline frontier incoming)
    (henv : env.Ordered) (sorted : profile.HasType (.sort relevant))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ answer : AmbientBoundedParameterReply base caps start
        (originalPrefixDisplay initial (.appFunction location) graph route).formationDisplay
        commonLeft commonRight profile (environmentCost baselineEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls baseline frontier answer) := by
  let last := originalPrefixDisplay initial (.appFunction location) graph route
  let parent := originalCallWorld controls .fundamental
    (.app hu hv (.ref domain) body function argument result) baseline
  have firstCost : (Closure.close (function.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin
        controls.ordered) baselineEnvironment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have lastCost := Nat.lt_of_le_of_lt (route.dependency_cost_le controls.ordered baselineEnvironment) firstCost
  have firstBelow : WorldBelow strata.rules.length (originalCallWorld controls .assignedComparison function baseline) parent :=
    original_child (richSchedule_strict firstCost _ _) _ _ _ _ _
  have lastBelow : WorldBelow strata.rules.length (originalCallWorld controls .assignedComparison natural baseline) parent :=
    original_child (richSchedule_strict lastCost _ _) _ _ _ _ _
  have lower : ∀ child ∈ [originalCallWorld controls .assignedComparison (leftDisplay).node baseline,
      originalCallWorld controls .assignedComparison last.node baseline], WorldBelow strata.rules.length child parent := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstBelow
    · cases List.mem_singleton.mp member
      exact lastBelow
  have smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .assignedComparison (leftDisplay).node baseline,
        originalCallWorld controls .assignedComparison last.node baseline]) (frontier ++ [parent]) := by
    have split := split_call lower
    clear incomingData paid bank
    induction frontier with
    | nil => exact split
    | cons sponsor tail ih => exact ih.cons sponsor
  have sponsored : Sponsored frontier [originalCallWorld controls .assignedComparison (leftDisplay).node baseline,
      originalCallWorld controls .assignedComparison last.node baseline] := by
    intro child member
    obtain ⟨sponsor, member', bound⟩ := paid parent (List.mem_singleton_self _)
    exact ⟨sponsor, member', EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans (lower child member) bound⟩
  let prior := incoming.reply.answer.reply
  let rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := last) controls baseline frontier prior.realization := {
    generation := incomingData.generation
    hereditary := incomingData.hereditary
    replayable := incomingData.replayable
    controlled := incomingData.controlled
    compatible := incomingData.compatible
    closed := prior.closed
    capacity := incoming.reply.bounded controls.ordered
    covered := incomingData.covered }
  exact incoming.assignedAtWorld (left := leftDisplay) (right := last) henv controls controls rfl rfl
    baseline baseline frontier _ incomingData sorted prior.realization rightData sponsored smaller bank

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
