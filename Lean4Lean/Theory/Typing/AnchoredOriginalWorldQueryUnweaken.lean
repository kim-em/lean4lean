import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnweaken
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank

/-! Leave an owner's temporary scope with the same selected world-qualified
reply. Resource queries and all dormant history annotations are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem replyOfFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (display : OriginalNestedDisplay U common expression assigned)
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight display.graph frame.raw controls)
    (replayable : generated.Replayable)
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (query : RichGradedResult display.sourceEnv env U registry target display.node locals σ available requested)
    (queryReady : ControlledStoredQuery controls frontier (.observation query.observation))
    (bounded : ∀ ordered : display.sourceEnv.Ordered,
      environmentCost (frame.dependencyEnvironment ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested
        (environmentCost baselineEnvironment),
      ∃ data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply,
        HEq reply.answer.reply.query query ∧
        HEq data.generation.environment generated.environment ∧
        data.controlled.annotation.worlds = ready.annotation.worlds ∧
        data.query.annotation.worlds = queryReady.annotation.worlds ∧
        data.generation.baseUses = generated.baseUses ∧
        (data.generation.TablesClosed ↔ generated.TablesClosed) := by
  obtain ⟨left, right⟩ := generated.erase.ambientGenerated.capped.generated.realizations
  subst σ
  subst τ
  let reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested
      (environmentCost baselineEnvironment) :=
    ⟨⟨⟨⟨locals, available, ⟨frame, substitutions⟩,
      generated.erase.ambientGenerated.capped.generated, query, closed⟩,
      generated.erase.ambientGenerated.capped⟩, bounded⟩, generated.erase.ambientGenerated⟩
  let data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply := {
    generation := generated, replayable := replayable, controlled := ready,
    compatible := compatible, query := queryReady, covered := covered, hereditary := hereditary }
  exact ⟨reply, data, HEq.rfl, HEq.rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- Apply the actual unweaken producer, preserving both the retained frame
annotations and the exact selected observer's query-owned dependencies. -/
theorem WorldGeneratedQueryReplyData.unweaken
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {commonCaps nextCaps : CaptureCaps}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = commonCaps)
    (reply : AmbientBoundedGeneratedQueryReply base nextCaps (display.weaken insertion)
      nextLeft nextRight requested (environmentCost baselineEnvironment))
    (data : WorldGeneratedQueryReplyData (P := P) (display := display.weaken insertion) controls baseline frontier reply) :
    ∃ previous : AmbientBoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested
        (environmentCost baselineEnvironment),
      ∃ previousData : WorldGeneratedQueryReplyData (P := P) controls baseline frontier previous,
        HEq previous.answer.reply.query reply.answer.reply.query ∧
        HEq previousData.generation.environment data.generation.environment ∧
        previousData.controlled.annotation.worlds = data.controlled.annotation.worlds ∧
        previousData.query.annotation.worlds = data.query.annotation.worlds ∧
        previousData.generation.baseUses = data.generation.baseUses ∧
        (previousData.generation.TablesClosed ↔ data.generation.TablesClosed) := by
  cases leftTail
  cases rightTail
  cases capsTail
  obtain ⟨generated, environment, _queries, replayable, compatible, bases, tables, ready, readyWorlds⟩ :=
    data.generation.unweakenControlled data.controlled
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds := by
    change Covered _ generated.environment.worlds baseline.worlds
    rw [environment]
    exact data.covered
  let hereditary : generated.Hereditary frontier :=
    ⟨tables.mpr data.hereditary.tablesClosed,
      data.hereditary.bases.cast bases.symm,
      data.hereditary.bases.ready_cast bases.symm data.hereditary.ready⟩
  obtain ⟨previous, previousData, query, annotation, retained, owned, previousBases, previousTables⟩ :=
    replyOfFrame display controls baseline frontier reply.answer.reply.realization.frame generated
      (replayable.mpr data.replayable) ready (compatible _ _ |>.mpr data.compatible) hereditary
      reply.answer.reply.realization.substitutions reply.answer.reply.closed reply.answer.reply.query data.query
      reply.bounded covered
  exact ⟨previous, previousData, query, annotation.trans (heq_of_eq environment), retained.trans readyWorlds, owned,
    previousBases.trans bases, previousTables.trans tables⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
