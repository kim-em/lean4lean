import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! An enriched application Pi request is transferred to the actual function's
assigned formation. Both endpoints are proper original children of the same
application, and the returned frame is the frame selected by that exact R call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

noncomputable def OriginalApplicationTypeRouteSide.functionFormationDisplay
    (side : OriginalApplicationTypeRouteSide U common) :=
  (OriginalNestedDisplay.ofOccurrence side.initial (.appFunction side.location) side.graph).formationDisplay

/-- The actual Pi selected inside the function formation is a proper
original descendant of this application. Its bank stays at the fixed caller
baseline even when the preceding R chooses a different semantic frame. -/
theorem OriginalApplicationTypeRouteSide.functionPiWorldBank
    (side : OriginalApplicationTypeRouteSide U common)
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata side.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental side.node baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline])) :
    let selected := piPrefix (.assignedFormation (.appFunction side.location))
    let node := EndpointState.pi selected.view.domainWF selected.view.bodyWF
      selected.view.domain selected.view.body
    Sponsored frontier [originalCallWorld controls .fundamental node baseline] ∧
    WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node baseline]) := by
  dsimp only
  let selected := piPrefix (.assignedFormation (.appFunction side.location))
  let node := EndpointState.pi selected.view.domainWF selected.view.bodyWF
    selected.view.domain selected.view.body
  have child : (Closure.close (side.function.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close (side.node.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have formation := side.function.typeFormation_dependency_cost_le controls.ordered baselineEnvironment
  have selectedCost := selected.route.dependency_cost_le controls.ordered baselineEnvironment
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental node baseline)
      (originalCallWorld controls .fundamental side.node baseline) :=
    original_child (richSchedule_strict (Nat.lt_of_le_of_lt (Nat.le_trans selectedCost formation) child) _ _)
      _ _ _ _ _
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental node baseline])
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline]) := by
    have step := split_call (calls := [originalCallWorld controls .fundamental node baseline])
      (fun world member => by cases List.mem_singleton.mp member; exact lower)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length
          (sponsors ++ [originalCallWorld controls .fundamental node baseline])
          (sponsors ++ [originalCallWorld controls .fundamental side.node baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  exact ⟨singletonSponsoredBelow paid lower, fun retained smaller => bank retained (smaller.trans funded)⟩

/-- The request may contain support and argument demands absent from the old
function observation. Its semantics is obtained at the actual application Pi,
then its exact requested profile is replayed to the function formation. -/
theorem OriginalApplicationTypeRouteSide.piRequestFunctionFormationWorld
    (side : OriginalApplicationTypeRouteSide U common)
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata side.sourceEnv)
    (frame : OriginalCaptureRealization side.graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight side.graph frame.frame.raw controls)
    (replayable : generated.Replayable)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (request : GeneratedApplicationPiRequest side.domain side.body side.hu side.hv
      env registry target locals (side.raw.comp commonLeft) available side.a relevant (profile : Profile n))
    (requestReady : ControlledStoredQuery controls frontier (.certificate request.certificate))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental side.node baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline])) :
    ∃ answer : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft))
      side.functionFormationDisplay commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost baselineEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls baseline frontier answer) := by
  obtain ⟨incoming, ⟨incomingData⟩⟩ := side.piRequestReplyWorld controls frame generated replayable frontier
    frameReady compatible hereditary baseline capacity covered henv hscoped formed closed request requestReady
    sponsored unaryBank
  let parent := originalCallWorld controls .fundamental side.node baseline
  have enlarged := application_cost_le_captured (side.domain.dependencyOrigin controls.ordered)
    (side.body.dependencyOrigin controls.ordered) (side.function.dependencyOrigin controls.ordered)
    (side.argument.dependencyOrigin controls.ordered) (side.result.dependencyOrigin controls.ordered)
    baselineEnvironment
  have functionLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := side.function.dependencyOrigin controls.ordered)
    (domain := side.domain.dependencyOrigin controls.ordered)
    (bodies := [side.body.dependencyOrigin controls.ordered])
    (children := [side.function.dependencyOrigin controls.ordered, side.argument.dependencyOrigin controls.ordered,
      side.result.dependencyOrigin controls.ordered]) (by simp) baselineEnvironment) enlarged
  have formationLess := Nat.lt_of_le_of_lt
    (side.function.typeFormation_dependency_cost_le controls.ordered baselineEnvironment) functionLess
  have piLess := EndpointState.appPiFormation_dependency_cost_lt controls.ordered side.hu side.hv
    (.ref side.domain) side.body side.function side.argument side.result baselineEnvironment
  have lower {context expression assigned}
      (node : EndpointState side.sourceEnv U context expression assigned)
      (cost : (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.close (side.node.dependencyOrigin controls.ordered) baselineEnvironment).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls .expressionReindex node baseline) parent :=
    smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict cost _ _) _ _ _ _) (Covered.refl _)
  have piBelow := lower (.pi side.hu side.hv (.ref side.domain) side.body) piLess
  have formationBelow := lower side.function.typeFormation.node formationLess
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .expressionReindex side.pi.display.node baseline,
        originalCallWorld controls .expressionReindex side.functionFormationDisplay.node baseline])
      (frontier ++ [parent]) := by
    have decrease := split_call (calls := [originalCallWorld controls .expressionReindex side.pi.display.node baseline,
        originalCallWorld controls .expressionReindex side.functionFormationDisplay.node baseline])
      (fun child member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact piBelow
        · cases List.mem_singleton.mp member; exact formationBelow)
    clear unaryBank replayBank sponsored incoming incomingData frameReady requestReady hereditary
    induction frontier with
    | nil => exact decrease
    | cons world rest ih => exact ih.cons world
  have pairSponsored : Sponsored frontier
      [originalCallWorld controls .expressionReindex side.pi.display.node baseline,
        originalCallWorld controls .expressionReindex side.functionFormationDisplay.node baseline] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow sponsored piBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow sponsored formationBelow _ (List.mem_singleton_self _)
  let rightData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := side.functionFormationDisplay) controls baseline frontier frame :=
    ⟨generated, replayable, frameReady, compatible, closed, capacity, covered, hereditary⟩
  obtain ⟨replayed, ⟨replayedData⟩⟩ :=
    (replayBank _ funded).observation base commonCaps side.pi.display side.functionFormationDisplay
      commonLeft commonRight controls controls rfl rfl baseline baseline frontier rfl pairSponsored
      incoming.reply.answer.reply.realization incomingData.callFrame frame rightData
      incoming.reply.answer.reply.query.observation incoming.reply.answer.reply.query.resources incomingData.query
  let adapted := replayed.mapQuery
    (replayed.answer.reply.query.adaptRequest henv hscoped formed
      incoming.reply.answer.reply.query.bound incoming.reply.answer.reply.query.adapter)
  let answer : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft))
      side.functionFormationDisplay commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost baselineEnvironment) := {
    toBoundedParameterReply := incoming.toBoundedParameterReply.reindex adapted.toBoundedGeneratedQueryReply
    generation := adapted.generation }
  exact ⟨answer, ⟨⟨replayedData.generation, replayedData.replayable, replayedData.controlled,
    replayedData.compatible, replayedData.query, replayedData.covered, replayedData.hereditary⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
