import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay

/-! Recover an actual caller projection-field certificate from the actual
application domain. Both replay calls are proper children of this application:
first same-expression domain replay, then assigned comparison of the argument
with its exposed projection. No foreign canonical certificate is returned. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
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
  {argument : EndpointState sourceEnv U source (.proj name index value) A}
  {result : EndpointState sourceEnv U source (B.inst (.proj name index value)) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}

/-- The input is the domain certificate computed from the actual function
query. The result is attached to the physical prior projection's field at the
original caller resources, including when the argument has conversion prefixes. -/
theorem applicationPriorFieldWorld
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
    (henv : env.Ordered) (closed : available.AtomClosed)
    (head : ProjectionHead argument)
    {functionDomain : EndpointState sourceEnv U source A (.sort functionDomainLevel)}
    {functionBody : EndpointState sourceEnv U (A :: source) B (.sort functionBodyLevel)}
    {functionDomainWF : functionDomainLevel.WF U} {functionBodyWF : functionBodyLevel.WF U}
    (functionRoute : PrefixRoute sourceEnv U source (.forallE A B) function.typeFormation.node
      (.pi functionDomainWF functionBodyWF functionDomain functionBody))
    (seed : RichCert sourceEnv env U registry target functionDomain
      locals (raw.comp commonLeft) true (support : Profile n) seedFootprint)
    (seedResources : seedFootprint.Available available)
    (seedReady : ControlledStoredQuery controls frontier (.certificate seed))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target head.field
        locals (raw.comp commonLeft) true support footprint,
      footprint.Available available ∧
      TypeRelated env U registry target (A.subst (raw.comp commonLeft))
        (head.fieldType.subst (raw.comp commonLeft)) support ∧
      TypeConversion env U target (A.subst (raw.comp commonLeft))
        (head.fieldType.subst (raw.comp commonLeft)) ∧
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
  have functionLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := function.dependencyOrigin controls.ordered)
    (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered])
    (children := [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered]) (by simp) (frame.frame.dependencyEnvironment controls.ordered)) enlarged
  have domainLess := Nat.lt_trans
    (Nat.lt_of_lt_of_le (binder_domain_cost (functionDomain.dependencyOrigin controls.ordered)
      [functionBody.dependencyOrigin controls.ordered] [] (frame.frame.dependencyEnvironment controls.ordered))
      (Nat.le_trans (functionRoute.dependency_cost_le controls.ordered _)
        (function.typeFormation_dependency_cost_le controls.ordered _))) functionLess
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
  have formationBelow := lower argument.typeFormation.node .expressionReindex formationLess
  have domainBelow := lower functionDomain .expressionReindex domainLess
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
  have pairFunded := fund (children := [originalCallWorld controls .expressionReindex functionDomain captured,
      originalCallWorld controls .expressionReindex argument.typeFormation.node captured])
    (fun child member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact domainBelow
      · cases List.mem_singleton.mp member; exact formationBelow)
  have pairSponsored : Sponsored frontier
      [originalCallWorld controls .expressionReindex functionDomain captured,
       originalCallWorld controls .expressionReindex argument.typeFormation.node captured] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow sponsored domainBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow sponsored formationBelow _ (List.mem_singleton_self _)
  let sandbox := diagonal.captureBase frame.substitutions.left
  let identity := frameData.leftDiagonal.generation frame.substitutions.left
  obtain ⟨identityReady⟩ := frameData.leftDiagonal.controlled frame.substitutions.left
  let domainProvenance : EndpointProvenance (location.contextDerivation initial) functionDomain := {
    rootSource := _, rootExpression := _, rootType := _, root := root, initial := initial
    location := .piDomain (functionRoute.locate (.assignedFormation (.appFunction location)))
    context_eq := by
      change _ = (functionRoute.locate (.assignedFormation (.appFunction location))).contextDerivation initial
      rw [PrefixRoute.locate_contextDerivation]
      rfl }
  let leftDisplay := OriginalNestedDisplay.identity sandbox functionDomain domainProvenance
  let rightDisplay := OriginalNestedDisplay.identity sandbox argument.typeFormation.node
    (.ofLocation (.assignedFormation (.appArgument location)) initial)
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  have observedReady : ControlledStoredQuery controls frontier (.observation (.code seed)) := {
    annotation := .code seedReady.annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using seedReady.within control active
    sponsored := seedReady.sponsored }
  obtain ⟨replayed, ⟨replayedData⟩⟩ :=
    (replayBank _ pairFunded).observation sandbox sandbox.initialCaps leftDisplay rightDisplay
      (raw.comp commonLeft) (raw.comp commonLeft) controls controls rfl rfl captured captured frontier rfl
      pairSponsored sandbox.identityRealization leftData sandbox.identityRealization rightData
      (.code seed) seedResources observedReady
  obtain ⟨frozenReady⟩ := replayed.answer.freezeBase_controlled replayedData.query
  obtain ⟨footprint, certificate, certificateReady, resources, _worlds⟩ :=
    replayed.answer.freezeBase.code_controlled henv controls frozenReady seed.formed
  let exposed := EndpointState.proj head.registered head.levelsWF head.levelCount
    head.parameterCount head.indexCount head.selected head.fieldWF head.field head.major
    head.closed head.relevance
  have exposedLess := Nat.lt_of_le_of_lt (head.route.dependency_cost_le controls.ordered
    (frame.frame.dependencyEnvironment controls.ordered)) argumentLess
  have argumentBelow := lower argument .assignedComparison argumentLess
  have exposedBelow := lower exposed .assignedComparison exposedLess
  have assignedFunded := fund (children := [originalCallWorld controls .assignedComparison argument captured,
      originalCallWorld controls .assignedComparison exposed captured]) (fun child member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact argumentBelow
        · cases List.mem_singleton.mp member; exact exposedBelow)
  have assignedPaid : Sponsored frontier
      [originalCallWorld controls .assignedComparison argument captured,
       originalCallWorld controls .assignedComparison exposed captured] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow sponsored argumentBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow sponsored exposedBelow _ (List.mem_singleton_self _)
  let argumentDisplay := OriginalNestedDisplay.identity sandbox argument
    (.ofLocation (.appArgument location) initial)
  let exposedProvenance : EndpointProvenance (location.contextDerivation initial) exposed := {
    rootSource := _, rootExpression := _, rootType := _, root := root, initial := initial
    location := head.route.locate (.appArgument location)
    context_eq := by rw [PrefixRoute.locate_contextDerivation]; rfl }
  let exposedDisplay := OriginalNestedDisplay.identity sandbox exposed exposedProvenance
  let argumentData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := argumentDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  let exposedData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := exposedDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.leftDiagonal.generation_hereditary frame.substitutions.left⟩
  obtain ⟨compared, ⟨comparedData⟩⟩ :=
    (replayBank _ assignedFunded).assigned sandbox sandbox.initialCaps argumentDisplay exposedDisplay
      (raw.comp commonLeft) (raw.comp commonLeft) controls controls rfl rfl captured captured frontier rfl
      assignedPaid sandbox.identityRealization argumentData sandbox.identityRealization exposedData
      certificate resources certificateReady
  obtain ⟨comparedReady⟩ := compared.reply.answer.freezeBase_controlled comparedData.query
  obtain ⟨finalFootprint, finalCode, finalReady, finalResources, _⟩ :=
    compared.reply.answer.freezeBase.code_controlled henv controls comparedReady seed.formed
  refine ⟨finalFootprint, finalCode, finalResources, ?_, ?_, ⟨finalReady⟩⟩
  · simpa only [argumentDisplay, exposedDisplay, OriginalNestedDisplay.identity] using compared.related
  · simpa only [argumentDisplay, exposedDisplay, OriginalNestedDisplay.identity] using compared.path

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
