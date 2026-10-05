import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureDemandAssembly

/-! An own-capture leaf returns its actual selected resource before attaching
any variable observer. All semantic calls are paid by the actual outer
original caller, which may lie above several binder/capture prefixes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem reindexWorldOwnCaptureDemand
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
    Nonempty (WorldVariableDemandReply P base caps
      (.capture graph domain graph argument (.ofLocation location initial)) commonLeft commonRight controls
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment) frontier 0 profile) := by
  obtain ⟨selected, data, answer, aligned, _certificateReady, _rightReady, ⟨alignedReady⟩⟩ :=
    reindexWorldOwnCaptureOwner initial argument location domain controls frame generated frontier ready replayable
      compatible hereditary baseline capacity covered destinationBaseline destinationCapacity destinationCovered
      variableNode left leftControls sameCutoff sameFuel leftBaseline leftFrame leftData
      henv hscoped formed query resources queryReady sponsored bank unary
  exact captureWorldDemandOfOwnerAnswer initial argument location domain controls
    selected.answer.reply.realization data.generation frontier data.controlled data.replayable data.compatible
    data.hereditary baseline (selected.bounded controls.ordered) data.covered generated.environment capacity
    henv formed selected.answer.reply.query data.query answer aligned alignedReady

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
