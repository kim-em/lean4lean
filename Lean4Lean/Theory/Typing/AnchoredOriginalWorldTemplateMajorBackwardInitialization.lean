import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateMajorInitialization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterBackward
import Lean4Lean.Theory.Typing.AnchoredOriginalConstantCoherence

/-! Empty-demand backward initialization at the SAME selected projection major.
The two arguments are arbitrary original terms. The opaque assigned comparison
certificate is not inspected: its selected frame supplies the actual formation
prefix, and the lower banks compute both argument packs and the genuine header. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

private theorem prefixCalls {strata : EquationStratification env}
    (frontier : List (World strata.rules.length))
    {child parent : World strata.rules.length}
    (below : WorldBelow strata.rules.length child parent) :
    CallBelow strata.rules.length (frontier ++ [child]) (frontier ++ [parent]) := by
  induction frontier with
  | nil => exact split_call (fun value member => by cases List.mem_singleton.mp member; exact below)
  | cons world rest ih => exact ih.cons world

section
variable {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {controls : OriginalWorldControls strata right.sourceEnv}
  {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
  {frontier : List (World strata.rules.length)} {profile : Profile n}
  {answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
    controls baseline frontier profile}

/-- The concrete application originals and its actual two backward steps. The
frame and world are transported along the prefix's context equality, retaining
the selected major reply itself. In particular `backward.A` and `domainExpression`
are the actual raw assigned types of the first and second source arguments. -/
structure WorldTemplateMajorBackwardInitialization
    (input : answer.FormationInput)
    (expressionEq : right.sourceType = .app (.app (.const name levels) a) p)
    (levelsWF : ∀ level ∈ levels, level.WF U) where
  domainExpression : VExpr
  bodyExpression : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainWF : domainLevel.WF U
  bodyWF : bodyLevel.WF U
  domain : EndpointRef right.sourceEnv U right.source domainExpression (.sort domainLevel)
  body : EndpointState right.sourceEnv U (domainExpression :: right.source) bodyExpression (.sort bodyLevel)
  function : EndpointState right.sourceEnv U right.source (.app (.const name levels) a)
    (.forallE domainExpression bodyExpression)
  argument : EndpointState right.sourceEnv U right.source p domainExpression
  result : EndpointState right.sourceEnv U right.source (bodyExpression.inst p) (.sort bodyLevel)
  route : PrefixRoute right.sourceEnv U right.source (.app (.app (.const name levels) a) p)
    (right.node.typeFormation.node.cast expressionEq rfl)
    (.app domainWF bodyWF (.ref domain) body function argument result)
  location : Located input.provenance.root (.app domainWF bodyWF (.ref domain) body function argument result)
  location_eq : route.locate (input.provenance.location.castExpression expressionEq) = location
  frame : OriginalRichFrame right.sourceEnv env U registry target
    (location.contextDerivation input.provenance.initial)
    answer.reply.reply.answer.reply.locals (right.raw.comp commonLeft) (right.raw.comp commonLeft)
    answer.reply.reply.answer.reply.available
  sameFrame : HEq frame answer.diagonalFrame
  captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)
  sameCaptured : HEq captured answer.diagonalCaptured
  frameData : WorldUnaryFrameData P controls frontier frame captured
  capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds
  info : VConstant
  lookup : env.constants name = some info
  backward : WorldTwoParameterBackward input.provenance.initial domain body function argument result
    domainWF bodyWF location frame input.substitutions P controls captured frontier
    (.empty : Profile 0) true (RichGradedResult.empty (n := 0)) info levelsWF

/-- Execute empty initialization at an actual two-application formation prefix.
The replay bank is the only additional induction hypothesis beyond FormationInput.
No observation or semantic answer is supplied for the selected family code. -/
theorem WorldTemplateAssignedReply.FormationInput.twoParameterBackwardWorld
    (input : answer.FormationInput)
    (expressionEq : right.sourceType = .app (.app (.const name levels) a) p)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental right.node.typeFormation.node answer.diagonalCaptured]))
    (sourceClosed : ∀ source, source ≤ env → P source) :
    Nonempty (WorldTemplateMajorBackwardInitialization input expressionEq levelsWF) := by
  obtain ⟨⟨E, F, u, v, hu, hv, domain, body, function, argument, result, location,
      prefixEq, _cost⟩, route, locationEq⟩ :=
    applicationPrefix (input.provenance.location.castExpression expressionEq)
  obtain ⟨domain, rfl⟩ := location.originalDomains.1
  dsimp only at route locationEq
  have contextEq : location.contextDerivation input.provenance.initial = right.context := by
    rw [← locationEq, PrefixRoute.locate_contextDerivation,
      Located.castExpression_contextDerivation, ← input.provenance.context_eq]
  have selectedCapacity : environmentCost (answer.diagonalFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [WorldTemplateAssignedReply.diagonalFrame,
      OriginalRichFrame.dependencyEnvironment_leftDiagonal] using answer.reply.reply.bounded controls.ordered
  have selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      answer.diagonalCaptured.worlds baseline.worlds := by
    simpa only [WorldTemplateAssignedReply.diagonalCaptured,
      OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using answer.data.covered
  have framed : ∃ frame : OriginalRichFrame right.sourceEnv env U registry target
      (location.contextDerivation input.provenance.initial)
      answer.reply.reply.answer.reply.locals (right.raw.comp commonLeft) (right.raw.comp commonLeft)
      answer.reply.reply.answer.reply.available,
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
      HEq frame answer.diagonalFrame ∧ HEq captured answer.diagonalCaptured ∧
      Nonempty (WorldUnaryFrameData P controls frontier frame captured) ∧
      environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds ∧
      (∀ {source expression assigned} (node : EndpointState right.sourceEnv U source expression assigned) phase,
        originalCallWorld controls phase node captured = originalCallWorld controls phase node answer.diagonalCaptured) := by
    rw [contextEq]
    exact ⟨answer.diagonalFrame, answer.diagonalCaptured, HEq.rfl, HEq.rfl, ⟨input.frameData⟩,
      selectedCapacity, selectedCovered, fun _ _ => rfl⟩
  obtain ⟨frame, captured, sameFrame, sameCaptured, ⟨frameData⟩, capacity, covered, worldsEq⟩ := framed
  let application := EndpointState.app hu hv (.ref domain) body function argument result
  have cost := route.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered)
  simp only [EndpointState.dependencyOrigin_cast] at cost
  have parentRelation : originalCallWorld controls .fundamental application captured =
      originalCallWorld controls .fundamental right.node.typeFormation.node captured ∨
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental application captured)
        (originalCallWorld controls .fundamental right.node.typeFormation.node captured) := by
    rcases Nat.eq_or_lt_of_le cost with same | smaller
    · left
      simp only [originalCallWorld, application, same]
    · exact .inr (original_child (richSchedule_strict smaller _ _) _ _ _ _ _)
  have paid : Sponsored frontier [originalCallWorld controls .fundamental application captured] := by
    rcases parentRelation with same | smaller
    · simpa only [same, worldsEq] using input.paid
    · apply singletonSponsoredBelow (parent := originalCallWorld controls .fundamental right.node.typeFormation.node captured) _ smaller
      simpa only [worldsEq] using input.paid
  have unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental application captured]) := by
    intro calls below
    apply input.bank calls
    rcases parentRelation with same | smaller
    · simpa only [same, worldsEq] using below
    · simpa only [worldsEq] using below.trans (prefixCalls frontier smaller)
  have replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental application captured]) := by
    intro calls below
    apply replayBank calls
    rcases parentRelation with same | smaller
    · simpa only [same, worldsEq] using below
    · simpa only [worldsEq] using below.trans (prefixCalls frontier smaller)
  let inner := applicationPrefix (.appFunction location)
  let constant := constantPrefix inner.view.function
  obtain ⟨info, sourceLookup⟩ := EndpointRef.constantLookup constant.reference rfl constant.primitive
  have lookup := input.sourceBelow.constants sourceLookup
  let certificate : RichCert right.sourceEnv env U registry target result
      answer.reply.reply.answer.reply.locals (right.raw.comp commonLeft) true (Profile.empty : Profile 0) [] :=
    .legacy (.seed .empty (.empty (.sort true)))
  have certificateReady : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := .legacy _ (.seed _ _ .empty)
    within := by
      intro control active
      simp only [StoredOriginalQuery.headDepth, certificate, RichCert.headDepth, SortableCert.headDepth,
        Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := fun _ member => nomatch member }
  let extraQuery : RichGradedResult right.sourceEnv env U registry target argument
      answer.reply.reply.answer.reply.locals (right.raw.comp commonLeft)
      answer.reply.reply.answer.reply.available (.empty : Profile 0) := .empty
  have extraReady : ControlledStoredQuery controls frontier (.observation extraQuery.observation) := {
    annotation := .legacy _ (.legacy _ .empty)
    within := by
      intro control active
      simp only [extraQuery, RichGradedResult.empty, StoredOriginalQuery.headDepth, RichObs.headDepth,
        SortableObs.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := fun _ member => nomatch member }
  have reflexive : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons level rest ih => exact .cons rfl ih
  have equivalent := reflexive levels
  obtain ⟨backward⟩ := OriginalRecordSource.twoParameterBackwardWorld input.provenance.initial domain body function
    argument result hu hv location frame input.substitutions controls captured frontier frameData captured
    (Nat.le_refl _) (fun world member => ⟨world, member, Or.inl rfl⟩) henv hscoped formed input.closed paid unary replay
    certificate (fun _ _ member => nomatch member) certificateReady extraQuery extraReady lookup levelsWF equivalent sourceClosed
  exact ⟨⟨E, F, u, v, hu, hv, domain, body, function, argument, result, route, location, locationEq,
    frame, sameFrame, captured, sameCaptured, frameData, capacity, covered, info, lookup, backward⟩⟩

end

/-- Restrict the actual outer projection replay bank to the selected major's
formation, then initialize both real source arguments. The immutable outer
baseline is used only for funding; no generated frame or observer is reselected. -/
theorem WorldTemplateAssignedReply.initializeProjectionMajorBackward
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (rightHead : ProjectionHead rightNode)
    {rightContext : ContextDerivation rightEnv U rightSource}
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayed = rightValue.subst rightRaw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : WorldTemplateAssignedReply (P := P) base caps leftDisplay
      (OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) displayedEq)
      commonLeft commonRight controls baseline frontier (profile : Profile n))
    (input : answer.FormationInput)
    (arguments : rightHead.parameters ++ rightHead.indices = [a, p])
    {leftEnv : VEnv} {leftSource : List VExpr} {leftExpression leftAssigned : VExpr}
    (leftNode : EndpointState leftEnv U leftSource leftExpression leftAssigned)
    (leftControls : OriginalWorldControls strata leftEnv)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline]))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source) :
    Nonempty (WorldTemplateMajorBackwardInitialization input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF) := by
  have capacity : environmentCost (answer.diagonalFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [WorldTemplateAssignedReply.diagonalFrame,
      OriginalRichFrame.dependencyEnvironment_leftDiagonal] using answer.reply.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      answer.diagonalCaptured.worlds baseline.worlds := by
    simpa only [WorldTemplateAssignedReply.diagonalCaptured,
      OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using answer.data.covered
  have proper : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured)
      (originalCallWorld controls .assignedComparison rightNode baseline) := by
    apply originalCallWorld_retargetBelow controls rightNode .assignedComparison
      answer.diagonalCaptured baseline capacity covered
    exact original_child (richSchedule_strict
      (Nat.lt_of_le_of_lt
        ((EndpointState.ref (.right rightHead.major)).typeFormation_dependency_cost_le controls.ordered _)
        (projectionMajor_cost_lt rightHead controls.ordered _)) _ _) _ _ _ _ _
  have smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental
        (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline]) := by
    have selectedBelow := from_right (calls := [originalCallWorld controls .fundamental
      (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
      (parent := originalCallWorld leftControls .assignedComparison leftNode leftWorld)
      (by intro child member; cases List.mem_singleton.mp member; exact proper)
    have inherited : ∀ extra : List (World strata.rules.length),
        CallBelow strata.rules.length
          (extra ++ [originalCallWorld controls .fundamental
            (EndpointState.ref (.right rightHead.major)).typeFormation.node answer.diagonalCaptured])
          (extra ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
            originalCallWorld controls .assignedComparison rightNode baseline]) := by
      intro extra
      induction extra with
      | nil => exact selectedBelow
      | cons world rest ih => exact ih.cons world
    exact inherited frontier
  exact input.twoParameterBackwardWorld
    (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF
    henv hscoped formed (fun calls below => replayBank calls (below.trans smaller)) sourceClosed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
