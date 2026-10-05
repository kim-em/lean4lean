import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadReplyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGenerationFramePack
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureBundle

/-! The own-capture activation's semantic step keeps the actual owner frame
selected by R. Its independently rooted declared domain is reached by a
second genuine R call in that exact frame's identity sandbox. Freezing this
reply keeps both the owner observer and declared certificate at the same
resources. This does not assert that rebuilding a capture around a changed
tail preserves the original owner-world reservation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem activationPrefix {count : Nat} {xs ys : List (World count)}
    (smaller : CallBelow count xs ys) (frontier : List (World count)) :
    CallBelow count (frontier ++ xs) (frontier ++ ys) := by
  induction frontier with
  | nil => exact smaller
  | cons _ _ ih => exact ih.cons _

private theorem sameGenerationFacts
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {firstFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {nextFrame : RawOriginalRichFrame sourceEnv env U registry target context nextLocals nextLeft nextRight nextAvailable}
    {controls : OriginalWorldControls strata sourceEnv}
    (first : WorldGenerated strata P base caps left right graph firstFrame controls)
    (second : WorldGenerated strata P base caps left right graph nextFrame controls)
    (same : first.framePack = second.framePack)
    (ready : second.Controlled frontier)
    (replayable : second.Replayable)
    (compatible : second.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : second.Hereditary frontier) :
    Nonempty (first.Controlled frontier) ∧ first.Replayable ∧
      first.UsesControlPrefix controls.cutoff controls.fuel ∧ Nonempty (first.Hereditary frontier) ∧
      environmentCost (firstFrame.dependencyEnvironment controls.ordered) =
        environmentCost (nextFrame.dependencyEnvironment controls.ordered) := by
  let Good : WorldGenerationFramePack strata P base caps left right graph controls → Prop :=
    fun ⟨_, _, _, _, frame, generated⟩ =>
      Nonempty (generated.Controlled frontier) ∧ generated.Replayable ∧
        generated.UsesControlPrefix controls.cutoff controls.fuel ∧
        Nonempty (generated.Hereditary frontier) ∧
        environmentCost (frame.dependencyEnvironment controls.ordered) =
          environmentCost (nextFrame.dependencyEnvironment controls.ordered)
  have facts : Good second.framePack := ⟨⟨ready⟩, replayable, compatible, ⟨hereditary⟩, rfl⟩
  exact Eq.mp (congrArg Good same.symm) facts

/-- The input is the concrete frame and observer selected by the incoming
owner R. All subsequent calls are funded from the original capture, not from
an asserted strict comparison between equal-capacity selected frames. The
domain is an independent original reference; no equality of original nodes
or completed domain interpretation is supplied. -/
theorem captureArgumentAlignmentWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (current : WorldEnvironmentProvenance strata U currentEnvironment)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (destinationCapacity : environmentCost ([Closure.bundle
      (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
      (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) currentEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) currentEnvironment) :: currentEnvironment)) ≤ environmentCost destinationEnvironment)
    (destinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (reservedCaptureWorldEnvironment controls domain argument baseline current).worlds destinationBaseline.worlds)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      generated.worlds baseline.worlds)
    (variableNode : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    (other : World strata.rules.length)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (sponsored : Sponsored frontier [other, originalCallWorld controls .expressionReindex variableNode
      destinationBaseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .expressionReindex variableNode
        destinationBaseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .expressionReindex variableNode
        destinationBaseline])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target argument locals
        (raw.comp commonLeft) (raw.comp commonRight) available profile,
      ∃ aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
          locals (raw.comp commonLeft) (raw.comp commonLeft) available true answer.support,
        Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) ∧
        Nonempty (ControlledStoredQuery controls frontier (.certificate aligned.certificate)) := by
  let parent := originalCallWorld controls .expressionReindex variableNode destinationBaseline
  have argumentPositive := Closure.cost_pos (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
  have domainPositive := Closure.cost_pos (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)
  have argumentBound : (Closure.close (argument.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)).cost := by
    change _ < _ + _
    omega
  have domainBound : (Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)).cost := by
    change _ < _ + _
    omega
  have formationBound := Nat.lt_of_le_of_lt
    (argument.typeFormation_dependency_cost_le controls.ordered baselineEnvironment) argumentBound
  let reserved : World strata.rules.length := .node
    (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
      controls.ordered.constantCount (richSchedule .expressionReindex
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
          (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)).cost)) baseline.worlds
  have reservedMember : reserved ∈
      (reservedCaptureWorldEnvironment controls domain argument baseline current).worlds := by
    exact List.mem_cons_self ..
  have lower {expression type : VExpr} (node : EndpointState sourceEnv U source expression type)
      (phase : RichPhase)
      (cost : (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost <
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
          (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node baseline) parent := by
    apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (originalCallWorld_boundedNode controls .expressionReindex variableNode
        (reservedCaptureWorldEnvironment controls domain argument baseline current) destinationBaseline
        destinationCapacity destinationCovered)
    apply Below.under reservedMember
    exact original_child (richSchedule_strict cost _ _) _ _ _ _ _
  have argBelow := lower argument .fundamental argumentBound
  have formationBelow := lower argument.typeFormation.node .expressionReindex formationBound
  have domainBelow := lower (.ref domain) .expressionReindex domainBound
  have fund {uses : List (World strata.rules.length)}
      (below : ∀ child ∈ uses, WorldBelow strata.rules.length child parent) :
      CallBelow strata.rules.length (frontier ++ uses) (frontier ++ [other, parent]) := by
    apply activationPrefix
    exact callBelow_of_sublist (List.sublist_cons_self other uses) ((split_call below).cons other)
  have paid {uses : List (World strata.rules.length)}
      (below : ∀ child ∈ uses, WorldBelow strata.rules.length child parent) : Sponsored frontier uses := by
    intro child member
    obtain ⟨sponsor, present, lowerParent⟩ := sponsored parent (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (below child member) lowerParent⟩
  have argumentLower : ∀ child ∈ [originalCallWorld controls .fundamental argument baseline],
      WorldBelow strata.rules.length child parent := by
    intro child member
    cases List.mem_singleton.mp member
    exact argBelow
  have pairLower : ∀ child ∈ [originalCallWorld controls .expressionReindex argument.typeFormation.node baseline,
      originalCallWorld controls .expressionReindex (.ref domain) baseline],
      WorldBelow strata.rules.length child parent := by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact formationBelow
    · cases List.mem_singleton.mp member
      exact domainBelow
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated ready replayable compatible hereditary
  obtain ⟨answer, answerReady, rightReady⟩ := (unary _ (fund argumentLower)).computational argument
    (.ofLocation location initial) controls frame.frame generated.environment baseline frontier capacity covered
    rfl (paid argumentLower) frameData closed formed frame.substitutions query resources queryReady
  obtain ⟨certificateReady⟩ := answerReady
  let sandbox := frame.frame.captureBase frame.substitutions
  let identity := frameData.generation frame.substitutions
  obtain ⟨identityReady⟩ := frameData.controlled frame.substitutions
  let leftDisplay := OriginalNestedDisplay.identity sandbox argument.typeFormation.node
    (.ofLocation (.assignedFormation location) initial)
  let rightDisplay := OriginalNestedDisplay.identity sandbox (.ref domain)
    (.ofLocation .here (location.contextDerivation initial))
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls baseline frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, capacity, covered,
      frameData.generation_hereditary frame.substitutions⟩
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls baseline frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, capacity, covered,
      frameData.generation_hereditary frame.substitutions⟩
  have observedReady : ControlledStoredQuery controls frontier (.observation (.code answer.certificate)) := {
    annotation := .code certificateReady.annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using certificateReady.within control active
    sponsored := certificateReady.sponsored }
  obtain ⟨reply, ⟨replyData⟩⟩ := (bank _ (fund pairLower)).observation sandbox sandbox.initialCaps
    leftDisplay rightDisplay (raw.comp commonLeft) (raw.comp commonRight) controls controls rfl rfl
    baseline baseline frontier rfl (paid pairLower) sandbox.identityRealization leftData
    sandbox.identityRealization rightData (.code answer.certificate) answer.resources observedReady
  obtain ⟨frozenReady⟩ := reply.answer.freezeBase_controlled replyData.query
  obtain ⟨outputFootprint, certificate, outputReady, outputResources, _worlds⟩ :=
    reply.answer.freezeBase.code_controlled henv controls frozenReady answer.certificate.formed
  exact ⟨answer, ⟨outputFootprint, certificate, outputResources, answer.typeCode⟩,
    ⟨certificateReady⟩, rightReady, ⟨outputReady⟩⟩

/-- The actual nominal owner is displayed by the same capture graph as the
selected tail. No original is reconstructed from its instantiated syntax. -/
noncomputable def captureHeadOwnerDisplay
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw) :
    OriginalNestedDisplay U common (a.subst raw) (A.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := a
  sourceType := A
  context := location.contextDerivation initial
  node := argument
  provenance := .ofLocation location initial
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

/-- Activate a fresh owner demand through the actual R bank, then produce
its value and independent declared-domain code at the SAME selected frame.
The old capture's immutable owner reservation pays for the first R call;
its bundle reservation pays for all subsequent F/domain-R calls. -/
theorem reindexWorldOwnCaptureOwner
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (destinationCapacity : environmentCost ([Closure.bundle
      (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
      (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered))
        (.close (domain.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered)) :: (frame.frame.dependencyEnvironment controls.ordered))) ≤ environmentCost destinationEnvironment)
    (destinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).worlds destinationBaseline.worlds)
    (variableNode : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    (left : OriginalNestedDisplay U common (a.subst raw) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (sameCutoff : leftControls.cutoff = controls.cutoff)
    (sameFuel : leftControls.fuel = controls.fuel)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := left) leftControls leftBaseline frontier leftFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft)
      (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query))
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline])
    (bank : WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline])) :
    ∃ selected : AmbientBoundedGeneratedQueryReply base caps
        (captureHeadOwnerDisplay initial argument location graph) commonLeft commonRight profile
        (environmentCost baselineEnvironment),
      ∃ data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier selected,
        ∃ answer : RichComputationalValue sourceEnv env U registry target argument selected.answer.reply.locals
            (raw.comp commonLeft) (raw.comp commonRight) selected.answer.reply.available selected.answer.reply.query.raw,
          ∃ aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
              selected.answer.reply.locals (raw.comp commonLeft) (raw.comp commonLeft)
              selected.answer.reply.available true answer.support,
            Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
            Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) ∧
            Nonempty (ControlledStoredQuery controls frontier (.certificate aligned.certificate)) := by
  let ownerDisplay := captureHeadOwnerDisplay initial argument location graph
  let current := reservedCaptureWorldEnvironment controls domain argument baseline generated.environment
  let leftCall := originalCallWorld leftControls .expressionReindex left.node leftBaseline
  let variableCall := originalCallWorld controls .expressionReindex variableNode destinationBaseline
  let ownerCall := originalCallWorld controls .expressionReindex argument baseline
  have ownerMember : ownerCall ∈ current.worlds := by
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have ownerBelow : WorldBelow strata.rules.length ownerCall variableCall :=
    BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (originalCallWorld_boundedNode controls .expressionReindex variableNode current destinationBaseline
        destinationCapacity destinationCovered) (.child ownerMember)
  have smaller : CallBelow strata.rules.length (frontier ++ [leftCall, ownerCall])
      (frontier ++ [leftCall, variableCall]) := by
    apply activationPrefix
    exact (split_call (calls := [ownerCall]) (fun value member => by
      cases List.mem_singleton.mp member
      exact ownerBelow)).cons leftCall
  have childSponsored : Sponsored frontier [leftCall, ownerCall] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact sponsored _ (List.mem_cons_self ..)
    · cases List.mem_singleton.mp member
      obtain ⟨sponsor, present, lower⟩ := sponsored variableCall
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans ownerBelow lower⟩
  let ownerData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := ownerDisplay) controls baseline frontier frame :=
    ⟨generated, replayable, ready, compatible, hereditary.tablesClosed.closed, capacity, covered, hereditary⟩
  obtain ⟨selected, ⟨data⟩⟩ := (bank _ smaller).observation base caps left ownerDisplay
    commonLeft commonRight leftControls controls sameCutoff sameFuel leftBaseline baseline frontier rfl
    childSponsored leftFrame leftData frame ownerData query resources queryReady
  obtain ⟨answer, aligned, certificateReady, rightReady, alignedReady⟩ :=
    captureArgumentAlignmentWorld initial argument location domain controls selected.answer.reply.realization
      data.generation frontier data.controlled data.replayable data.compatible data.hereditary baseline
      generated.environment destinationBaseline destinationCapacity destinationCovered (selected.bounded controls.ordered) data.covered variableNode leftCall
      henv hscoped formed selected.answer.reply.closed selected.answer.reply.query.observation
      selected.answer.reply.query.resources data.query sponsored bank unary
  exact ⟨selected, data, answer, aligned, certificateReady, rightReady, alignedReady⟩

private theorem captureActivatedReply
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (current : WorldEnvironmentProvenance strata U currentEnvironment)
    (currentCapacity : environmentCost currentEnvironment ≤ environmentCost baselineEnvironment)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (answer : RichComputationalValue sourceEnv env U registry target argument locals
      (raw.comp commonLeft) (raw.comp commonRight) available profile)
    (aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
      locals (raw.comp commonLeft) (raw.comp commonLeft) available true answer.support)
    (alignedReady : ControlledStoredQuery controls frontier (.certificate aligned.certificate)) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance) commonLeft commonRight profile
        (environmentCost ([Closure.bundle
          (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
          (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
          (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) currentEnvironment)
            (.close (domain.dependencyOrigin controls.ordered) currentEnvironment) :: currentEnvironment))),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls
        (reservedCaptureWorldEnvironment controls domain argument baseline current) frontier reply) ∧
      reply.answer.reply.query.footprint = [(0, Need.mk reply.answer.reply.query.rank reply.answer.reply.query.raw)] := by
  let actual := WorldGenerated.capture generated baseline capacity domain initial argument location rfl
    query resources (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _)
    aligned.certificate aligned.resources answer.typed
    (answer.related.convert henv answer.typed aligned.related) (captureNeeds profile)
    (fun need member => (captureNeeds_covered profile need member).1)
    (fun need member => (captureNeeds_covered profile need member).2)
  let actualReady : actual.Controlled frontier := {
    annotation := .cons queryReady.annotation (.cons alignedReady.annotation ready.annotation)
    within := by
      intro control active
      change max (query.headDepth _) (max (aligned.certificate.headDepth _) (generated.retainedDepth _)) ≤ _
      exact Nat.max_le.mpr ⟨queryReady.within control active,
        Nat.max_le.mpr ⟨alignedReady.within control active, ready.within control active⟩⟩
    sponsored := queryReady.sponsored.merge (alignedReady.sponsored.merge ready.sponsored) }
  let actualHereditary : actual.Hereditary frontier := {
    tablesClosed := ⟨hereditary.tablesClosed, atomizedNeeds_closed [⟨n, profile⟩]⟩
    bases := hereditary.bases
    ready := hereditary.ready }
  obtain ⟨answerReply, next, retained, worlds, annotation, noWorlds, noDepth,
      rankEq, rawEq, footprintEq, same⟩ :=
    generatedOwnCaptureWorldReplyAt initial henv hscoped generated.erase.ambientGenerated.ambient.1.below
      controls domain argument location frame generated baseline capacity variableNode variableProvenance
      hereditary.tablesClosed.closed formed query resources answer aligned
  obtain ⟨⟨nextReady⟩, nextReplayable, nextCompatible, ⟨nextHereditary⟩, environment⟩ :=
    sameGenerationFacts next actual same actualReady ⟨replayable, covered⟩ compatible actualHereditary
  have outputCapacity : environmentCost (answerReply.reply.realization.frame.dependencyEnvironment controls.ordered) =
      environmentCost ([Closure.bundle
        (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) currentEnvironment)
          (.close (domain.dependencyOrigin controls.ordered) currentEnvironment) :: currentEnvironment)) := by
    exact environment.trans ((captureBundleWorld_retained_capacity _ _ _ _ capacity).trans
      (captureBundleWorld_retained_capacity _ _ _ _ currentCapacity).symm)
  let reply : AmbientBoundedGeneratedQueryReply base caps _ commonLeft commonRight profile _ := {
    answer := answerReply
    bounded := fun _ => Nat.le_of_eq outputCapacity
    generation := next.erase.ambientGenerated }
  let observationReady : ControlledStoredQuery controls frontier (.observation answerReply.reply.query.observation) := {
    annotation := annotation
    within := by
      intro control _
      change answerReply.reply.query.observation.headDepth _ ≤ _
      rw [noDepth]
      exact Nat.zero_le _
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [noWorlds]
      intro _ member
      cases member }
  have outputCovered : Covered (@EquationControlMeasure.Less strata.rules.length) next.worlds
      (reservedCaptureWorldEnvironment controls domain argument baseline current).worlds := by
    rw [worlds]
    exact captureBundleWorld_retained_covered controls domain argument generated.environment baseline capacity covered
      ([originalCallWorld controls .expressionReindex argument current,
        originalCallWorld controls .fundamental (.ref domain) current] ++ current.worlds)
  have makeNeed {firstRank secondRank : Nat} {first : Profile firstRank} {second : Profile secondRank}
      (equal : firstRank = secondRank) (same : HEq first second) :
      Need.mk firstRank first = Need.mk secondRank second := by
    cases equal
    exact congrArg (Need.mk _) (eq_of_heq same)
  have needEq := makeNeed rankEq rawEq
  refine ⟨reply, ⟨⟨next, nextReplayable, nextReady, nextCompatible, observationReady, outputCovered, nextHereditary⟩⟩, ?_⟩
  change answerReply.reply.query.footprint = [(0, Need.mk answerReply.reply.query.rank answerReply.reply.query.raw)]
  rw [needEq]
  exact footprintEq

/-- Productive reconstruction of the destination's ordinary capture head.
Incoming R, owner F, and independent declared-domain R are all genuine
proper calls. The same selected owner frame and aligned certificate create
an ordinary variable observer with explicit needs; its immutable capture
reservation and hereditary generation are retained on the exact reply. -/
theorem reindexWorldOwnCaptureHead
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (destinationCapacity : environmentCost ([Closure.bundle
      (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
      (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered))
        (.close (domain.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered)) :: (frame.frame.dependencyEnvironment controls.ordered))) ≤ environmentCost destinationEnvironment)
    (destinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).worlds destinationBaseline.worlds)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (left : OriginalNestedDisplay U common (a.subst raw) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (sameCutoff : leftControls.cutoff = controls.cutoff)
    (sameFuel : leftControls.fuel = controls.fuel)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := left) leftControls leftBaseline frontier leftFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft)
      (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query))
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline])
    (bank : WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode
          destinationBaseline])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance) commonLeft commonRight profile (environmentCost destinationEnvironment),
      Nonempty (WorldCaptureHeadReplyData (P := P) controls
        (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment)
        destinationBaseline frontier reply) := by
  obtain ⟨selected, data, answer, aligned, _certificateReady, _rightReady, ⟨alignedReady⟩⟩ :=
    reindexWorldOwnCaptureOwner initial argument location domain controls frame generated frontier ready replayable
      compatible hereditary baseline capacity covered destinationBaseline destinationCapacity destinationCovered variableNode left leftControls sameCutoff sameFuel
      leftBaseline leftFrame leftData henv hscoped formed query resources queryReady sponsored bank unary
  obtain ⟨rawReply, ⟨rawData⟩, rawFootprint⟩ := captureActivatedReply initial argument location domain controls
    selected.answer.reply.realization data.generation frontier data.controlled data.replayable data.compatible
    data.hereditary baseline (selected.bounded controls.ordered) data.covered generated.environment capacity
    variableNode variableProvenance henv hscoped formed selected.answer.reply.query.observation
    selected.answer.reply.query.resources data.query answer aligned alignedReady
  let adapted := rawReply.mapQuery
    (rawReply.answer.reply.query.adaptRequest henv hscoped formed selected.answer.reply.query.bound
      selected.answer.reply.query.adapter)
  let reply : AmbientBoundedGeneratedQueryReply base caps _ commonLeft commonRight profile
      (environmentCost destinationEnvironment) := {
    answer := adapted.answer
    bounded := fun ordered => Nat.le_trans (adapted.bounded ordered) destinationCapacity
    generation := adapted.generation }
  exact ⟨reply, ⟨{
    generation := rawData.generation, replayable := rawData.replayable,
    controlled := rawData.controlled, compatible := rawData.compatible,
    query := rawData.query,
    covered := Covered.trans EquationControlMeasure.less_trans rawData.covered destinationCovered,
    hereditary := rawData.hereditary,
    localCapacity := rawReply.bounded, localCovered := rawData.covered, footprint := rawFootprint }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
