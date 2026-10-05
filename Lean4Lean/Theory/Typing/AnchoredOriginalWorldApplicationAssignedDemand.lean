import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay

/-! Interpret an independently retained assigned-code demand at an actual
application argument, then move the SAME resulting certificate to the actual
application domain. The selected R query is frozen back to the caller frame;
the support profile is unchanged even when the value demand is empty. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}

/-- Both calls are computed proper children of the actual application. The
input is finite original code syntax, not a supplied interpretation of it.
The output stays at the original caller resources and retains the exact
support requested by `seed`. -/
theorem applicationAssignedDemandWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
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
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (seed : RichCert sourceEnv env U registry target argument.typeFormation.node
      locals (raw.comp commonLeft) true (support : Profile n) seedFootprint)
    (seedResources : seedFootprint.Available available)
    (seedReady : ControlledStoredQuery controls frontier (.certificate seed))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target (.ref domain)
        locals (raw.comp commonLeft) true support footprint,
      footprint.Available available ∧
      TypeRelated env U registry target (A.subst (raw.comp commonLeft))
        (A.subst (raw.comp commonLeft)) support ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  let diagonal := frame.frame.leftDiagonal
  let captured := frame.frame.diagonalWorld controls generated.environment
  have selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using covered
  have diagonalEnvironment : diagonal.dependencyEnvironment controls.ordered =
      frame.frame.dependencyEnvironment controls.ordered :=
    frame.frame.dependencyEnvironment_leftDiagonal controls.ordered
  let parent := originalCallWorld controls .fundamental
    (.app hu hv (.ref domain) body function argument result) baseline
  have enlarged := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered)
    (frame.frame.dependencyEnvironment controls.ordered)
  have domainLess := Nat.lt_of_lt_of_le (binder_domain_cost (domain.dependencyOrigin controls.ordered)
    [body.dependencyOrigin controls.ordered]
    [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered] (frame.frame.dependencyEnvironment controls.ordered)) enlarged
  have argumentLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := argument.dependencyOrigin controls.ordered)
    (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered])
    (children := [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered]) (by simp) (frame.frame.dependencyEnvironment controls.ordered)) enlarged
  have lower {context expression assigned} (node : EndpointState sourceEnv U context expression assigned)
      (phase : RichPhase)
      (cost : (Closure.close (node.dependencyOrigin controls.ordered)
        (frame.frame.dependencyEnvironment controls.ordered)).cost <
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin controls.ordered)
          (frame.frame.dependencyEnvironment controls.ordered)).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node captured) parent := by
    apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans _ selectedCovered
    apply EquationControlMeasure.scheduleDecrease
    apply richSchedule_strict
    change (Closure.close (node.dependencyOrigin controls.ordered)
      (diagonal.dependencyEnvironment controls.ordered)).cost < _
    rw [diagonalEnvironment]
    exact Nat.lt_of_lt_of_le cost
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1))
  have formationLess := Nat.lt_of_le_of_lt
    (argument.typeFormation_dependency_cost_le controls.ordered _) argumentLess
  have codeBelow := lower argument.typeFormation.node .fundamental formationLess
  have formationBelow := lower argument.typeFormation.node .expressionReindex formationLess
  have domainBelow := lower (.ref domain) .expressionReindex domainLess
  have fund {children : List (World strata.rules.length)}
      (smaller : ∀ child ∈ children, WorldBelow strata.rules.length child parent) :
      CallBelow strata.rules.length (frontier ++ children) (frontier ++ [parent]) := by
    have decrease := split_call smaller
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length (inherited ++ children) (inherited ++ [parent]) := by
      intro inherited
      induction inherited with
      | nil => exact decrease
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  have codeFunded := fund (children := [originalCallWorld controls .fundamental argument.typeFormation.node captured])
    (fun child member => by cases List.mem_singleton.mp member; exact codeBelow)
  have pairFunded := fund (children := [originalCallWorld controls .expressionReindex argument.typeFormation.node captured,
      originalCallWorld controls .expressionReindex (.ref domain) captured])
    (fun child member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact formationBelow
      · cases List.mem_singleton.mp member; exact domainBelow)
  have pairSponsored : Sponsored frontier
      [originalCallWorld controls .expressionReindex argument.typeFormation.node captured,
       originalCallWorld controls .expressionReindex (.ref domain) captured] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow sponsored formationBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow sponsored domainBelow _ (List.mem_singleton_self _)
  obtain ⟨meaning, ⟨meaningReady⟩⟩ := worldCode controls diagonal captured frontier _ unaryBank codeFunded
    (singletonSponsoredBelow sponsored codeBelow)
    (.ofLocation (.assignedFormation (.appArgument location)) initial)
    frameData.leftDiagonal henv hscoped closed formed frame.substitutions.left seed seedResources seedReady
  let sandbox := diagonal.captureBase frame.substitutions.left
  let identity := frameData.leftDiagonal.generation frame.substitutions.left
  obtain ⟨identityReady⟩ := frameData.leftDiagonal.controlled frame.substitutions.left
  let leftDisplay := OriginalNestedDisplay.identity sandbox argument.typeFormation.node
    (.ofLocation (.assignedFormation (.appArgument location)) initial)
  let rightDisplay := OriginalNestedDisplay.identity sandbox (.ref domain)
    (.ofLocation (.appDomain location) initial)
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  have observedReady : ControlledStoredQuery controls frontier (.observation (.code meaning.certificate)) := {
    annotation := .code meaningReady.annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using meaningReady.within control active
    sponsored := meaningReady.sponsored }
  obtain ⟨replayed, ⟨replayedData⟩⟩ :=
    (replayBank _ pairFunded).observation sandbox sandbox.initialCaps leftDisplay rightDisplay
      (raw.comp commonLeft) (raw.comp commonLeft) controls controls rfl rfl captured captured frontier rfl
      pairSponsored sandbox.identityRealization leftData sandbox.identityRealization rightData
      (.code meaning.certificate) meaning.resources observedReady
  obtain ⟨frozenReady⟩ := replayed.answer.freezeBase_controlled replayedData.query
  obtain ⟨footprint, certificate, certificateReady, resources, _worlds⟩ :=
    replayed.answer.freezeBase.code_controlled henv controls frozenReady seed.formed
  exact ⟨footprint, certificate, resources, meaning.related, ⟨certificateReady⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
