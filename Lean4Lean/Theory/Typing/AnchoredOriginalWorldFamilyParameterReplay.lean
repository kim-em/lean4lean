import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateParameterWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

/-! Requery a parameter at its actual original occurrence. The caller
explicitly chooses its entire current source frame as an identity sandbox.
Consequently a query-selected owner or reply freezes to those exact
resources. This theorem does not assert that arbitrary scoped groups are
identity graphs, nor infer world coverage from numerical frame capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- Identity caps return this exact observer to the original caller table.
Only its local-list index is transported; its original node and retained
opening annotation are unchanged. -/
theorem CappedCaptureGenerated.freezeControlledObserver
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {frame : RawOriginalRichFrame base.sourceEnv env U registry target base.context
      locals base.left base.right available}
    (generated : CappedCaptureGenerated base base.initialCaps base.left base.right
      (.identity base.context) frame)
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    (query : RichObs base.sourceEnv env U registry target node locals base.left profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.observation query)) :
    ∃ actual : RichObs base.sourceEnv env U registry target node base.locals base.left profile footprint,
      HEq actual query ∧ footprint.Available base.available ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation actual)) := by
  have localEq : locals = base.locals := generated.generated.locals_eq
  subst locals
  exact ⟨query, HEq.rfl,
    fun index need member => generated.availableBound index need (resources index need member), ⟨ready⟩⟩

/-- Freezing a returned identity reply preserves controls on the SAME
raw observer, including its original grade and foreign opening sites. -/
theorem CappedGeneratedQueryReply.freezeBase_controlled
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    {provenance : EndpointProvenance base.context node}
    (reply : CappedGeneratedQueryReply base base.initialCaps
      (OriginalNestedDisplay.identity base node provenance) base.left base.right requested)
    (ready : ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) :
    Nonempty (ControlledStoredQuery controls frontier (.observation reply.freezeBase.observation)) := by
  rcases reply with ⟨⟨locals, available, realization, generated, query, closed⟩, capped⟩
  have localEq : locals = base.locals := generated.locals_eq
  subst locals
  exact ⟨ready⟩

/-- The selected source query is replayed at the actual nominal argument
using a proper original R pair. The returned frame is frozen before the
finite Need adapter is applied, so no new caller resources or sponsors are
assumed. The only semantic clause is the qualified original R induction
hypothesis at these two concrete occurrences. -/
theorem ProjectionHead.replayParameterControlled
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {outer : EndpointState base.sourceEnv U base.source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    (field : EndpointRef base.sourceEnv U base.source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    {owner : EndpointState base.sourceEnv U base.source expression ownerType}
    {argument : EndpointState base.sourceEnv U base.source expression argumentType}
    (ownerLocation : Located field owner)
    (argumentLocation : Located (.right head.major) argument)
    (argumentProvenance : EndpointProvenance base.context argument)
    (controls : OriginalWorldControls strata base.sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (base.frame.dependencyEnvironment controls.ordered))
    (other : World strata.rules.length)
    (frontier : List (World strata.rules.length))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {selected : RawOriginalRichFrame base.sourceEnv env U registry target base.context
      selectedLocals base.left base.right selectedAvailable}
    (selectedGenerated : WorldGenerated strata P base base.initialCaps base.left base.right
      (.identity base.context) selected controls)
    (query : RichObs base.sourceEnv env U registry target owner selectedLocals base.left
      (input : Profile k) footprint)
    (resources : footprint.Available selectedAvailable)
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (need : Need) (queryBound : need.rank ≤ k)
    (adapter : GeneralNormalProfileAdapter env U registry target input (raiseProfile k queryBound need.profile))
    (reindex :
      CallBelow strata.rules.length
        (frontier ++ [originalCallWorld controls .expressionReindex owner captured,
          originalCallWorld controls .expressionReindex argument captured])
        (frontier ++ [originalCallWorld controls .assignedComparison outer captured, other]) →
      ∀ {incomingFootprint}
        (incoming : RichObs base.sourceEnv env U registry target owner base.locals base.left input incomingFootprint),
      incomingFootprint.Available base.available →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ reply : CappedGeneratedQueryReply base base.initialCaps
        (OriginalNestedDisplay.identity base argument argumentProvenance) base.left base.right input,
        Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation))) :
    ∃ result : RichGradedResult base.sourceEnv env U registry target argument
      base.locals base.left base.available need.profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  obtain ⟨incoming, sameQuery, available, ⟨incomingReady⟩⟩ :=
    selectedGenerated.erase.capped.freezeControlledObserver query resources queryReady
  have smaller := (ProjectionHead.parameterSourceFunding head field fieldEq ownerLocation argumentLocation controls captured other).2.1
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .expressionReindex owner captured,
        originalCallWorld controls .expressionReindex argument captured])
      (frontier ++ [originalCallWorld controls .assignedComparison outer captured, other]) := by
    clear queryReady reindex incomingReady
    induction frontier with
    | nil => exact smaller
    | cons sponsor rest ih => exact ih.cons sponsor
  obtain ⟨reply, ⟨replyReady⟩⟩ := reindex funded incoming available incomingReady
  obtain ⟨frozenReady⟩ := reply.freezeBase_controlled replyReady
  exact ⟨reply.freezeBase.adaptRequest henv hscoped formed queryBound adapter, ⟨frozenReady⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
