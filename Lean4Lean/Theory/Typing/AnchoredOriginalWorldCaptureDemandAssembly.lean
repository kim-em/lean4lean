import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadActivation

/-! Assemble the exact captured resource from the actual owner answers.
The public activation producers compute these answers through their proper
banks; this constructor only retains the resulting frame and finite demand. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem captureWorldDemandOfOwnerAnswer
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
    (ready : generated.Controlled frontier) (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (current : WorldEnvironmentProvenance strata U currentEnvironment)
    (currentCapacity : environmentCost currentEnvironment ≤ environmentCost baselineEnvironment)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (query : RichGradedResult sourceEnv env U registry target argument locals (raw.comp commonLeft) available requested)
    (queryReady : ControlledStoredQuery controls frontier (.observation query.observation))
    (answer : RichComputationalValue sourceEnv env U registry target argument locals
      (raw.comp commonLeft) (raw.comp commonRight) available query.raw)
    (aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
      locals (raw.comp commonLeft) (raw.comp commonLeft) available true answer.support)
    (alignedReady : ControlledStoredQuery controls frontier (.certificate aligned.certificate)) :
    Nonempty (WorldVariableDemandReply P base caps
      (.capture graph domain graph argument (.ofLocation location initial)) commonLeft commonRight controls
      (reservedCaptureWorldEnvironment controls domain argument baseline current) frontier 0 requested) := by
  have related := answer.related.convert henv answer.typed aligned.related
  let nextFrame := (frame.frame.capture domain initial argument location rfl query.observation
    query.resources aligned.certificate aligned.resources answer.typed related (captureNeeds query.raw)
    (fun need member => (captureNeeds_covered query.raw need member).1)
    (fun need member => (captureNeeds_covered query.raw need member).2)).reserve
      [.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)]
  let nextWorld := WorldGenerated.capture generated baseline (capacity)
    domain initial argument location rfl query.observation query.resources
    (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _)
    aligned.certificate aligned.resources answer.typed related (captureNeeds query.raw)
    (fun need member => (captureNeeds_covered query.raw need member).1)
    (fun need member => (captureNeeds_covered query.raw need member).2)
  let nextReady : nextWorld.Controlled frontier := {
    annotation := .cons queryReady.annotation (.cons alignedReady.annotation ready.annotation)
    within := fun control active => Nat.max_le.mpr ⟨queryReady.within control active,
      Nat.max_le.mpr ⟨alignedReady.within control active, ready.within control active⟩⟩
    sponsored := queryReady.sponsored.merge (alignedReady.sponsored.merge ready.sponsored) }
  let nextHereditary : nextWorld.Hereditary frontier := {
    tablesClosed := ⟨hereditary.tablesClosed, atomizedNeeds_closed [⟨query.rank, query.raw⟩]⟩
    bases := hereditary.bases
    ready := hereditary.ready }
  have below := generated.erase.ambientGenerated.ambient.1.below
  have rawPair := (argument.sound.defeq.mono below).substDF henv frame.substitutions.wf
    formed frame.substitutions
  have nextSubstitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) :=
    .cons frame.substitutions (domain.sound.defeq.mono below) rawPair
  obtain ⟨realization, actual, actualReplayable, ⟨actualReady⟩, actualCompatible,
      ⟨actualHereditary⟩, actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail nextFrame nextWorld nextSubstitutions ⟨replayable, covered⟩
      nextReady compatible nextHereditary
  refine ⟨{
    locals := Locals.push locals
    available := available.push (captureNeeds query.raw)
    realization := realization
    generation := actual
    replayable := actualReplayable
    controlled := actualReady
    compatible := actualCompatible
    hereditary := actualHereditary
    capacity := ?_
    covered := ?_
    demand := {
      rank := query.rank
      bound := query.bound
      raw := query.raw
      adapter := query.adapter
      member := List.mem_append_left _ (List.mem_singleton_self _)
      live := query.live } }⟩
  · intro ordered
    rw [actualEnvironment ordered]
    exact Nat.le_of_eq ((captureBundleWorld_retained_capacity _ _ _ _ (capacity)).trans
      (captureBundleWorld_retained_capacity _ _ _ _ currentCapacity).symm)
  · rw [actualWorlds]
    exact captureBundleWorld_retained_covered controls domain argument generated.environment baseline
      (capacity) covered
      ([originalCallWorld controls .expressionReindex argument current,
        originalCallWorld controls .fundamental (.ref domain) current] ++ current.worlds)

theorem captureWorldDemandOfOwnerFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier) (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (current : WorldEnvironmentProvenance strata U currentEnvironment)
    (currentCapacity : environmentCost currentEnvironment ≤ environmentCost baselineEnvironment)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (query : RichGradedResult sourceEnv env U registry target argument locals σ available requested)
    (queryReady : ControlledStoredQuery controls frontier (.observation query.observation))
    (answer : RichComputationalValue sourceEnv env U registry target argument locals
      σ τ available query.raw)
    (aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
      locals σ σ available true answer.support)
    (alignedReady : ControlledStoredQuery controls frontier (.certificate aligned.certificate)) :
    Nonempty (WorldVariableDemandReply P base caps
      (.capture graph domain graph argument (.ofLocation location initial)) commonLeft commonRight controls
      (reservedCaptureWorldEnvironment controls domain argument baseline current) frontier 0 requested) := by
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  exact captureWorldDemandOfOwnerAnswer initial argument location domain controls ⟨frame, substitutions⟩
    generated frontier ready replayable compatible hereditary baseline capacity covered current currentCapacity
    henv formed query queryReady answer aligned alignedReady

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
