import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyDispatcher

/-! The total variable dispatcher returns an actual query at the original
right endpoint, with its same selected positive generation and hereditary
metadata. The original endpoint supplies its own index-scope proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable def originalVariableDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node) :
    OriginalNestedDisplay U common (raw index) (assigned.subst raw) :=
  ⟨sourceEnv, source, .bvar index, assigned, context, node, provenance, raw, graph, rfl, rfl⟩

/-- Complete the variable R constructor under the actual lower F/R/C bank.
The requested observer may contain arbitrary shared recipes. The output has
its exact original destination, a finite ordinary-variable observer, and the
same generation that proves both its local and outer admissibility. -/
theorem reindexWorldVariable
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := originalVariableDisplay graph node provenance) controls baseline frontier frame)
    (left : OriginalNestedDisplay U common (raw index) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (sameCutoff : leftControls.cutoff = controls.cutoff)
    (sameFuel : leftControls.fuel = controls.fuel)
    (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      leftControls leftBaseline frontier leftFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp commonLeft) profile footprint)
    (resources : footprint.Available leftAvailable)
    (queryReady : ControlledStoredQuery leftControls frontier (.observation query))
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex node baseline])
    (bank : WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex node baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex node baseline])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps (originalVariableDisplay graph node provenance)
        commonLeft commonRight profile (environmentCost baselineEnvironment),
      ∃ output : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply,
        (∀ ordered : sourceEnv.Ordered,
          environmentCost (reply.answer.reply.realization.frame.dependencyEnvironment ordered) ≤
            environmentCost (frame.frame.dependencyEnvironment controls.ordered)) ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) output.generation.worlds data.generation.worlds := by
  have inRange : index < source.length :=
    node.sound.defeq.closedN controls.ordered (CtxWF.closed controls.ordered context.forget.defeq)
  let incoming : OriginalNestedDisplay U common ((raw index).lift' .refl) leftAssigned := {
    left with expression_eq := by simpa only [lift'_refl] using left.expression_eq }
  let incomingData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := incoming) leftControls leftBaseline frontier leftFrame := {
    generation := leftData.generation, replayable := leftData.replayable, controlled := leftData.controlled
    compatible := leftData.compatible, closed := leftData.closed, capacity := leftData.capacity
    covered := leftData.covered, hereditary := leftData.hereditary }
  obtain ⟨answer⟩ := data.generation.reindexVariableDependency index frontier inRange
    data.replayable data.compatible data.controlled data.hereditary frame.frame.valid frame.substitutions
    baseline data.capacity data.covered node Ctx.Lift'.refl rfl rfl rfl incoming leftControls
    sameCutoff sameFuel leftBaseline leftFrame incomingData henv hscoped formed query resources queryReady sponsored bank unary
  let localReply := answer.atNode henv hscoped formed node provenance
  let localData := answer.atNode_data henv hscoped formed node provenance
  let reply : AmbientBoundedGeneratedQueryReply base caps (originalVariableDisplay graph node provenance)
      commonLeft commonRight profile (environmentCost baselineEnvironment) := {
    answer := localReply.answer
    bounded := fun ordered => Nat.le_trans (localReply.bounded ordered) data.capacity
    generation := localReply.generation }
  let output : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply := {
    generation := localData.generation, replayable := localData.replayable
    controlled := localData.controlled, compatible := localData.compatible, query := localData.query
    hereditary := localData.hereditary
    covered := Covered.trans EquationControlMeasure.less_trans localData.covered data.covered }
  exact ⟨reply, output, localReply.bounded, localData.covered⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
