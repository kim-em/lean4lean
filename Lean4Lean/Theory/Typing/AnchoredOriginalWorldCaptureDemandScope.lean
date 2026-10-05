import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureDemandAssembly
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandScope

/-! Execute an own-capture leaf below an arbitrary common-scope insertion.
The incoming query remains at its actual larger common scope. Unweakening
retains the selected frame and all actual answers, then rebuilding precedes
weakening the whole capture map, preserving its exact syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem reindexWorldOwnCaptureDemandUnder
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
    {ρ : Lift} (insertion : Ctx.Lift' ρ common nextCommon)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun i => nextCaps (ρ.liftVar i)) = caps)
    (left : OriginalNestedDisplay U nextCommon (a.subst (raw.lift_r ρ)) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (sameCutoff : leftControls.cutoff = controls.cutoff)
    (sameFuel : leftControls.fuel = controls.fuel)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals nextLeft nextRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := left) leftControls leftBaseline frontier leftFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp nextLeft)
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
    Nonempty (WorldVariableDemandReply P base caps
      (.capture graph domain graph argument (.ofLocation location initial))
      commonLeft commonRight controls
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment) frontier 0 profile) := by
  cases leftTail
  cases rightTail
  cases capsTail
  let weakWorld := generated.weaken insertion rfl rfl rfl
  let weakReady : weakWorld.Controlled frontier := ⟨ready.annotation, ready.within, ready.sponsored⟩
  let weakHereditary : weakWorld.Hereditary frontier :=
    ⟨hereditary.tablesClosed, hereditary.bases, hereditary.ready⟩
  obtain ⟨weakFrame, actual, actualReplayable, ⟨actualReady⟩, actualCompatible,
      ⟨actualHereditary⟩, actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail frame.frame weakWorld frame.substitutions replayable weakReady compatible weakHereditary
  have actualCapacity : environmentCost (weakFrame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [actualEnvironment controls.ordered]
    exact capacity
  have actualCovered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds := by
    rw [actualWorlds]
    exact covered
  have actualDestinationCapacity : environmentCost
      (reservedCaptureWorldEnvironment controls domain argument baseline actual.environment).closures ≤ environmentCost destinationEnvironment := by
    have eq := (captureBundleWorld_retained_capacity (argument.dependencyOrigin controls.ordered)
      (domain.dependencyOrigin controls.ordered) _ _ actualCapacity).trans
      (captureBundleWorld_retained_capacity (argument.dependencyOrigin controls.ordered)
        (domain.dependencyOrigin controls.ordered) _ _ capacity).symm
    exact Nat.le_trans (Nat.le_of_eq eq) destinationCapacity
  have actualDestinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (reservedCaptureWorldEnvironment controls domain argument baseline actual.environment).worlds destinationBaseline.worlds :=
    Covered.trans EquationControlMeasure.less_trans
      (captureBundleWorld_retained_covered controls domain argument actual.environment baseline actualCapacity actualCovered
        ([originalCallWorld controls .expressionReindex argument generated.environment,
          originalCallWorld controls .fundamental (.ref domain) generated.environment] ++ generated.worlds))
      destinationCovered
  obtain ⟨selected, data, answer, aligned, _certificateReady, _rightReady, ⟨alignedReady⟩⟩ :=
    reindexWorldOwnCaptureOwner initial argument location domain controls weakFrame actual frontier actualReady
      actualReplayable actualCompatible actualHereditary baseline actualCapacity actualCovered destinationBaseline
      actualDestinationCapacity actualDestinationCovered variableNode left leftControls sameCutoff sameFuel
      leftBaseline leftFrame leftData henv hscoped formed query resources queryReady sponsored bank unary
  obtain ⟨previous, previousEnvironment, previousQueries, previousReplayable, previousCompatible,
      previousBases, previousTables, previousReady, previousReadyWorlds⟩ :=
    data.generation.unweakenControlled data.controlled
  let previousHereditary : previous.Hereditary frontier :=
    ⟨previousTables.mpr data.hereditary.tablesClosed,
      data.hereditary.bases.cast previousBases.symm,
      data.hereditary.bases.ready_cast previousBases.symm data.hereditary.ready⟩
  have previousCovered : Covered (@EquationControlMeasure.Less strata.rules.length) previous.worlds baseline.worlds := by
    change Covered _ previous.environment.worlds baseline.worlds
    rw [previousEnvironment]
    exact data.covered
  obtain ⟨demand⟩ := captureWorldDemandOfOwnerFrame initial argument location domain controls
    selected.answer.reply.realization.frame selected.answer.reply.realization.substitutions previous frontier previousReady
    (previousReplayable.mpr data.replayable) ((previousCompatible _ _).mpr data.compatible) previousHereditary
    baseline (selected.bounded controls.ordered) previousCovered generated.environment capacity henv formed
    selected.answer.reply.query data.query answer aligned alignedReady
  exact ⟨demand⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
