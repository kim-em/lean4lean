import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyOwnerCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationInput

/-! The active application capture is constructed from the same selected
source frame and packed raw argument query. Its owner admission comes from
the selected reply's hereditary coverage, independently of numeric cost. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private located_worlds_nil from Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (sourceDomain : EndpointRef sourceEnv U source sourceA (.sort sourceU))
  (sourceBody : EndpointState sourceEnv U (sourceA :: source) sourceB (.sort sourceV))
  (function : EndpointState sourceEnv U source f (.forallE sourceA sourceB))
  (argument : EndpointState sourceEnv U source a sourceA)
  (result : EndpointState sourceEnv U source (sourceB.inst a) (.sort sourceV))
  (sourceHu : sourceU.WF U) (sourceHv : sourceV.WF U)
  (sourceLocation : Located major (.app sourceHu sourceHv (.ref sourceDomain) sourceBody function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (sourceLocation.contextDerivation initial) ownerRaw)
  (selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
  {domain : EndpointRef headerEnv U headerSource A (.sort u)}

noncomputable def GeneratedApplicationPackedRequest.pendingAt
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (sourceLocation.dependencyEnvironment ordered ownerInitial))
    (packed : GeneratedApplicationPackedRequest sourceDomain sourceBody argument sourceHu sourceHv
      env registry target selected.locals (ownerRaw.comp commonLeft) selected.available true (profile : Profile n))
    (headerLocals : List Nat) (headerLeft : Subst) (headerAvailable : Valuation) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals headerLeft headerAvailable ownerInitial a packed.request.key.anchor
        (a.subst (ownerRaw.comp commonRight)) where
  owner := .inr ⟨source, a, sourceA, argument, .appArgument sourceLocation⟩
  ownerLocals := selected.locals
  ownerLeft := ownerRaw.comp commonLeft
  ownerRight := ownerRaw.comp commonRight
  ownerAvailable := selected.available
  ownerClosed := selected.closed
  initialContext := initial
  frame := selected.realization.frame
  substitutions := selected.realization.substitutions
  frame_environment_le := sourceBound
  depth := 0
  sourcePrefix := []
  source_eq := rfl
  depth_eq := rfl
  expression_eq := by simp [HeaderOwner.expression]
  left_eq := packed.request.anchor_eq.symm
  right_eq := rfl
  rank := packed.argumentQuery.rank
  input := packed.argumentQuery.raw
  footprint := packed.argumentQuery.footprint
  query := packed.argumentQuery.observation
  queryAvailable := packed.argumentQuery.resources

noncomputable def GeneratedApplicationPackedRequest.pendingScope
    {commonCaps : CaptureCaps}
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (sourceLocation.dependencyEnvironment ordered ownerInitial))
    (packed : GeneratedApplicationPackedRequest sourceDomain sourceBody argument sourceHu sourceHv
      env registry target selected.locals (ownerRaw.comp commonLeft) selected.available true (profile : Profile n))
    (headerLocals : List Nat) (headerLeft : Subst) (headerAvailable : Valuation) :
    CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps
      (packed.pendingAt (domain := domain) (field := field) initial sourceDomain sourceBody function argument result
        sourceHu sourceHv sourceLocation sourceGraph selected sourceBound headerLocals headerLeft headerAvailable).depth
      ((packed.pendingAt (domain := domain) (field := field) initial sourceDomain sourceBody function argument result
        sourceHu sourceHv sourceLocation sourceGraph selected sourceBound headerLocals headerLeft headerAvailable).owner.context initial) where
  scope := common
  raw := ownerRaw
  left := commonLeft
  right := commonRight
  graph := sourceGraph
  insertion := .refl
  raw_eq := by simp [GeneratedApplicationPackedRequest.pendingAt, Subst.liftN]
  leftTail := rfl
  rightTail := rfl
  caps := commonCaps
  capsTail := rfl


/-- Assemble the actual application capture from a selected source packet.
The caller supplies no pending owner or owner-coverage proof: both are computed
from the original argument occurrence and the selected source admission. -/
theorem GeneratedApplicationPackedRequest.captureWorld
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (headerInitial : ContextDerivation headerEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation headerInitial) raw)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata headerEnv)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (sourceLocation.dependencyEnvironment ordered ownerInitial))
    (noBinders : sourceLocation.binderPrefix = [])
    (sourceBaseline : WorldEnvironmentProvenance strata U sourceEnvironment)
    (sourceData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := OriginalNestedDisplay.ofOccurrence initial sourceLocation sourceGraph)
      ownerControls sourceBaseline frontier selected.realization)
    (packed : GeneratedApplicationPackedRequest sourceDomain sourceBody argument sourceHu sourceHv
      env registry target selected.locals (ownerRaw.comp commonLeft) selected.available true (profile : Profile m))
    (packedReady : packed.Controlled controls frontier)
    (whole : AmbientBoundedParameterReply base commonCaps ((VExpr.forallE sourceA sourceB).subst (ownerRaw.comp commonLeft))
      (OriginalNestedDisplay.ofOccurrence headerInitial location graph) commonLeft commonRight
      (Profile.pi (sourceA.subst (ownerRaw.comp commonLeft)) (sourceB.subst (ownerRaw.comp commonLeft).lift) packed.request.support [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]) capacity)
    (tailWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph
      whole.reply.answer.reply.realization.frame.raw controls)
    (tailReplayable : tailWorld.Replayable)
    (tailReady : tailWorld.Controlled frontier)
    (tailHereditary : tailWorld.Hereditary frontier)
    (tailCompatible : tailWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target whole.reply.answer.reply.locals
      (raw.comp commonLeft) whole.reply.answer.reply.available true (.ref domain) body packed.request.key (raiseProfile packed.request.rank packed.request.bound profile))
    (rowReady : ControlledStoredQuery controls frontier (.certificate row.body))
    (wholeQueryReady : ControlledStoredQuery controls frontier (.observation whole.reply.answer.reply.query.observation))
    (sorted : (Profile.pi (sourceA.subst (ownerRaw.comp commonLeft)) (sourceB.subst (ownerRaw.comp commonLeft).lift) packed.request.support [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]).HasType (.sort true))
    (value : RichSupportedValue sourceEnv env U registry target argument selected.locals
      (ownerRaw.comp commonLeft) (ownerRaw.comp commonRight) selected.available packed.request.key.input)
    (valueReady : ControlledStoredQuery controls frontier (.certificate value.certificate))
    (sameSupport : value.support = packed.request.support)
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      seedLocals (raw.comp commonLeft) seedAvailable ownerInitial a packed.request.key.anchor (a.subst (ownerRaw.comp commonRight)))
    (seedScope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext))
    (seedControls : OriginalWorldControls strata sourceEnv)
    (seedWorld : WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
      seedScope.graph seed.frame.raw seedControls)
    (seedReplayable : seedWorld.Replayable)
    (seedReady : seedWorld.Controlled frontier)
    (seedHereditary : seedWorld.Hereditary frontier)
    (seedCompatible : seedWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (seedQueryReady : ControlledStoredQuery controls frontier (.observation seed.query))
    (seedSame : seedControls.HasPrefix controls.cutoff controls.fuel)
    (domainProvenance : EndpointProvenance (location.contextDerivation headerInitial) (.ref domain))
    (originalPrior : OriginalCaptureRealization graph env registry target
      originalLocals commonLeft commonRight originalAvailable)
    (priorWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph originalPrior.frame.raw controls)
    (priorReplayable : priorWorld.Replayable)
    (priorReady : priorWorld.Controlled frontier)
    (priorHereditary : priorWorld.Hereditary frontier)
    (priorCompatible : priorWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (history : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope graph domainProvenance
      originalPrior ordered headerOrdered)
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (baselines : WorldEnvironmentProvenance strata U (seed.frame.dependencyEnvironment ordered) ×
      WorldEnvironmentProvenance strata U (originalPrior.frame.dependencyEnvironment headerOrdered))
    (baselineCoverage : Covered (@EquationControlMeasure.Less strata.rules.length) seedWorld.worlds baselines.1.worlds ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) priorWorld.worlds baselines.2.worlds)
    (tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) tailWorld.worlds baselines.2.worlds)
    (seedArgument : seed.owner.Argument)
    (seedCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      baselines.1.worlds (seed.owner.worldEnvironment seedControls initialProvenance).worlds)
    (sourceAdmission : Covered (@EquationControlMeasure.Less strata.rules.length)
      sourceBaseline.worlds initialProvenance.worlds)
    (routeInputs : history.route.WorldInputs strata)
    (historyWellFormed : history.route.WellFormed)
    (historyControls : ∀ i : Fin history.route.frames.length,
      OriginalWorldControls strata (history.route.frames[i]).sourceEnv)
    (historyWorld : ∀ i : Fin history.route.frames.length,
      WorldGenerated strata P base seedScope.caps seedScope.left seedScope.right
        (history.route.frames[i]).graph (history.route.frames[i]).frame.realization.frame.raw (historyControls i))
    (routeReplayable : ∀ i, (historyWorld i).Replayable)
    (boundary : history.route.WorldBoundary routeInputs seedControls controls
      baselines.1 baselines.2)
    (coherent : boundary.FrameOccurrenceCoherent historyControls historyWorld)
    (routeReady : ∀ i, (historyWorld i).Controlled frontier)
    (routeHereditary : ∀ i, (historyWorld i).Hereditary frontier)
    (routeCompatible : ∀ i, (historyWorld i).UsesControlPrefix controls.cutoff controls.fuel)
    (routeSame : ∀ i, (historyControls i).HasPrefix controls.cutoff controls.fuel)
    (ownerSame : ownerControls.HasPrefix controls.cutoff controls.fuel)
    (routeAmbient : history.route.Ambient)
    (routeSources : history.route.AllSources P)
    (capacity_eq : capacity = environmentCost (originalPrior.frame.dependencyEnvironment headerOrdered)) :
    let pending := packed.pendingAt (field := field) (domain := domain) initial sourceDomain sourceBody function argument result
      sourceHu sourceHv sourceLocation sourceGraph selected sourceBound whole.reply.answer.reply.locals
      (raw.comp commonLeft) whole.reply.answer.reply.available
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
        ownerInitial a packed.request.key.anchor (a.subst (ownerRaw.comp commonRight)),
      ∃ reply : CappedGeneratedQueryReply base commonCaps
          (capturedPiBodyDisplay headerInitial location graph sourceGraph argument (.ofLocation (.appArgument sourceLocation) initial))
          commonLeft commonRight (raiseProfile packed.request.rank packed.request.bound profile),
        ∃ generation : WorldGenerated strata P base commonCaps commonLeft commonRight
          (capturedPiBodyDisplay headerInitial location graph sourceGraph argument (.ofLocation (.appArgument sourceLocation) initial)).graph
          reply.reply.realization.frame.raw controls,
          generation.Replayable ∧
          Nonempty (generation.Controlled frontier) ∧
          generation.UsesControlPrefix controls.cutoff controls.fuel ∧
          Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
          reply.reply.available = whole.reply.answer.reply.available.push entries.needs ∧
          reply.reply.locals = Locals.push whole.reply.answer.reply.locals ∧
          (∀ hf : headerEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment hf =
            ((whole.reply.answer.reply.realization.frame.group domain ordered ownerInitial entries).reserve
              (groupCaptureHistoryReserve field major domain ordered headerOrdered ownerInitial
                (originalPrior.frame.dependencyEnvironment headerOrdered) history.route.reserve)).dependencyEnvironment hf) ∧
          generation.worlds =
            ((WorldEnvironmentProvenance.groupHistory field major domain ownerControls controls initialProvenance
              baselines.2 (history.route.worldReserve routeInputs)).append
              (WorldEnvironmentProvenance.group ownerControls controls initialProvenance tailWorld.environment entries)).worlds ∧
          Nonempty (GeneratedArgumentCaptureTrace selected.realization.frame pending packed.request.key.input entries) ∧
          (∀ entry ∈ entries, entry.answer.value.support.sortFlags = packed.request.support.sortFlags) ∧
          (∀ entry ∈ entries, Nonempty (ControlledStoredQuery controls frontier
            (.certificate entry.answer.aligned.certificate))) ∧ Nonempty (generation.Hereditary frontier) := by
  let pending := packed.pendingAt (field := field) (domain := domain) initial sourceDomain sourceBody function argument result
    sourceHu sourceHv sourceLocation sourceGraph selected sourceBound whole.reply.answer.reply.locals
    (raw.comp commonLeft) whole.reply.answer.reply.available
  let pendingScope := packed.pendingScope (field := field) (domain := domain) (commonCaps := commonCaps)
    initial sourceDomain sourceBody function argument result sourceHu sourceHv sourceLocation sourceGraph selected
    sourceBound whole.reply.answer.reply.locals (raw.comp commonLeft) whole.reply.answer.reply.available
  have pendingCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      sourceData.generation.worlds (pending.owner.worldEnvironment ownerControls initialProvenance).worlds := by
    change Covered (@EquationControlMeasure.Less strata.rules.length) sourceData.generation.worlds
      (initialProvenance.located ownerControls (.appArgument sourceLocation)).worlds
    rw [located_worlds_nil ownerControls (.appArgument sourceLocation) initialProvenance noBinders]
    exact Covered.trans EquationControlMeasure.less_trans sourceData.covered sourceAdmission
  have pendingCompatible : sourceData.generation.UsesControlPrefix controls.cutoff controls.fuel := by
    rw [← ownerSame.1, ← ownerSame.2]
    exact sourceData.compatible
  exact whole.captureArgumentHistoryReplyOfRowWorld headerInitial location graph controls ownerControls frontier
    tailWorld tailReplayable tailReady tailHereditary tailCompatible henv hscoped ordered headerOrdered sourceBelow headerBelow formed
    row rowReady wholeQueryReady sorted selected.realization.frame sourceData.generation sourceGraph argument
    (.ofLocation (.appArgument sourceLocation) initial) rfl pending (.refl (base := selected.realization.frame.raw))
    pendingScope sourceData.generation sourceData.replayable sourceData.controlled sourceData.hereditary pendingCompatible
    packedReady.argument packed.argumentQuery.bound packed.argumentQuery.adapter value valueReady sameSupport rfl
    seed seedScope seedControls seedWorld seedReplayable seedReady seedHereditary seedCompatible seedQueryReady seedSame
    domainProvenance originalPrior priorWorld priorReplayable priorReady priorHereditary priorCompatible history
    initialProvenance baselines baselineCoverage tailCovered seedArgument seedCovered pendingCovered routeInputs historyWellFormed historyControls historyWorld routeReplayable
    boundary coherent routeReady routeHereditary routeCompatible routeSame ownerSame
    sourceData.generation.erase.ambientGenerated.ambient.1 sourceData.generation.erase.sources.1
    routeAmbient routeSources capacity_eq

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
