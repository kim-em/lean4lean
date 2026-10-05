import Lean4Lean.Theory.Typing.AnchoredOriginalWorldAssignedSortDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationAssignedDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionParameterFunding

/-! An actual parameter-hole assigned demand starts at the original field's
literal assigned sort. Its nonempty code seed is transferred by a proper
original C call to the retained nominal argument. This supplies the actual
syntax consumed by application-domain replay, including at empty value
demand. No assigned-type path or semantic code answer is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The resulting query is frozen from the SAME actual C reply to the
current source frame. Both the support profile and its nonempty sort flag
are fixed by the original field's assigned universe. -/
theorem ProjectionHead.parameterAssignedSortWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {argument : EndpointState sourceEnv U source head.fieldType argumentType}
    (location : Located (.right head.major) argument)
    (fieldProvenance : EndpointProvenance context head.field)
    (argumentProvenance : EndpointProvenance context argument)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (other : World strata.rules.length)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target argument.typeFormation.node
        locals (raw.comp commonLeft) true (Profile.sort (n := n) (assignedSortFlag head.fieldLevel)) footprint,
      footprint.Available available ∧
      TypeRelated env U registry target (.sort head.fieldLevel)
        (argumentType.subst (raw.comp commonLeft)) (Profile.sort (n := n) (assignedSortFlag head.fieldLevel)) ∧
      TypeConversion env U target (.sort head.fieldLevel) (argumentType.subst (raw.comp commonLeft)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  let diagonal := frame.frame.leftDiagonal
  let captured := frame.frame.diagonalWorld controls generated.environment
  have selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using covered
  have selectedCapacity : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal] using capacity
  let sandbox := diagonal.captureBase frame.substitutions.left
  let identity := frameData.leftDiagonal.generation frame.substitutions.left
  obtain ⟨identityReady⟩ := frameData.leftDiagonal.controlled frame.substitutions.left
  let leftDisplay := OriginalNestedDisplay.identity sandbox head.field fieldProvenance
  let rightDisplay := OriginalNestedDisplay.identity sandbox argument argumentProvenance
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  let seed : RichCert sourceEnv env U registry target head.field.typeFormation.node
      locals (raw.comp commonLeft) true (Profile.sort (n := n) (assignedSortFlag head.fieldLevel)) [] :=
    .legacy (.seed (.sort (assignedSortFlag_relevant head.fieldLevel))
      (Profile.HasType.sort (assignedSortFlag head.fieldLevel)))
  let seedReady : ControlledStoredQuery controls frontier (.certificate seed) := {
    annotation := .legacy _ (.seed _ _ (.sort _))
    within := by
      intro control active
      simp only [StoredOriginalQuery.headDepth, seed, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨decrease, sponsored⟩ := ProjectionHead.parameterAssignedSelectedFunding head location
    controls captured baseline selectedCapacity selectedCovered other frontier paid
  obtain ⟨answer, ⟨answerData⟩⟩ := bank.assigned _ decrease sandbox sandbox.initialCaps
    leftDisplay rightDisplay (raw.comp commonLeft) (raw.comp commonLeft) controls controls rfl rfl
    captured captured frontier rfl sponsored sandbox.identityRealization leftData
    sandbox.identityRealization rightData seed (by intro _ _ impossible; cases impossible) seedReady
  obtain ⟨frozenReady⟩ := answer.reply.answer.freezeBase_controlled answerData.query
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    answer.reply.answer.freezeBase.code_controlled henv controls frozenReady seed.formed
  refine ⟨footprint, certificate, resources, ?_, ?_, ⟨ready⟩⟩
  · simpa only [leftDisplay, rightDisplay, OriginalNestedDisplay.identity, subst_sort] using answer.related
  · simpa only [leftDisplay, rightDisplay, OriginalNestedDisplay.identity, subst_sort] using answer.path


/-- Produce the assigned-code supplement at the actual family application's
domain. The field seed is compared to the application's nominal argument;
then the formation F and domain R calls run strictly below that same actual
application, itself a proper descendant of the original projection major.
The exact nonempty support survives every step at the original resources. -/
theorem ProjectionHead.parameterApplicationAssignedSortWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source head.fieldType A}
    {result : EndpointState sourceEnv U source (B.inst head.fieldType) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (majorLocation : Located (.right head.major) (.app hu hv (.ref domain) body function argument result))
    (fieldProvenance : EndpointProvenance (location.contextDerivation initial) head.field)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (other : World strata.rules.length)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target (.ref domain)
        locals (raw.comp commonLeft) true (Profile.sort (n := n) (assignedSortFlag head.fieldLevel)) footprint,
      footprint.Available available ∧
      TypeRelated env U registry target (A.subst (raw.comp commonLeft))
        (A.subst (raw.comp commonLeft)) (Profile.sort (n := n) (assignedSortFlag head.fieldLevel)) ∧
      TypeConversion env U target (.sort head.fieldLevel) (A.subst (raw.comp commonLeft)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) := by
  obtain ⟨seedFootprint, seed, seedResources, seedRelated, seedPath, ⟨seedReady⟩⟩ :=
    ProjectionHead.parameterAssignedSortWorld (n := n) head (.appArgument majorLocation)
      fieldProvenance (.ofLocation (.appArgument location) initial) controls frame generated
      frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered other henv hscoped formed closed paid replayBank
  let application := EndpointState.app hu hv (.ref domain) body function argument result
  let parent := originalCallWorld controls .fundamental application generated.environment
  have outerAdmitted := originalCallWorld_boundedNode controls .assignedComparison outer
    generated.environment baseline capacity covered
  have applicationBelow : WorldBelow strata.rules.length parent
      (originalCallWorld controls .assignedComparison outer baseline) :=
    BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans outerAdmitted
      (ProjectionHead.parameter_below head majorLocation controls generated.environment
        .fundamental .assignedComparison)
  have actualDecrease : CallBelow strata.rules.length [parent]
      [other, originalCallWorld controls .assignedComparison outer baseline] := by
    have replace : CallBelow strata.rules.length [other, parent]
        [other, originalCallWorld controls .assignedComparison outer baseline] :=
      (split_call (fun world member => by cases List.mem_singleton.mp member; exact applicationBelow)).cons other
    have drop : CallBelow strata.rules.length [parent] [other, parent] :=
      .single (.head (replacement := []) (by intro world member; cases member))
    exact drop.trans replace
  have decrease : CallBelow strata.rules.length (frontier ++ [parent])
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length (inherited ++ [parent])
          (inherited ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
      intro inherited
      induction inherited with
      | nil => exact actualDecrease
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  have appPaid : Sponsored frontier [parent] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := paid _ (List.mem_cons_of_mem other (List.mem_singleton_self _))
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans applicationBelow below⟩
  have appUnary : WorldBoundedUnaryCallBank env U registry strata P (frontier ++ [parent]) :=
    fun retained smaller => unaryBank retained (smaller.trans decrease)
  have appReplay : WorldBoundedCallBank env U registry strata P (frontier ++ [parent]) :=
    fun retained smaller => replayBank retained (smaller.trans decrease)
  obtain ⟨footprint, certificate, resources, code, ready⟩ :=
    applicationAssignedDemandWorld (location := location) controls frame generated frontier frameReady frameReplayable frameCompatible frameHereditary
      generated.environment (Nat.le_refl _) (Covered.refl _) henv hscoped formed closed
      seed seedResources seedReady appPaid appUnary appReplay
  exact ⟨footprint, certificate, resources, code, seedPath, ready⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
