import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHeadQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryUnweaken
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldResourceClosure

/-! Scoped capture replay uses the actual stored owner R reservation. Scope
entry/exit keep the same actual frames and retained histories; the strict
recursive call replaces the variable parent by its retained owner child. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem callFrameOfRaw
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)} {caps : CaptureCaps}
    (display : OriginalNestedDisplay U common expression assigned)
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frame : OriginalRichFrame display.sourceEnv env U registry target display.context locals σ τ available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight display.graph frame.raw controls)
    (replayable : generated.Replayable) (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (substitutions : Ctx.SubstEq env U target σ τ display.source)
    (closed : available.AtomClosed)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds) :
    ∃ realization : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available,
      Nonempty (WorldCallFrameData (P := P) (base := base) (caps := caps) (display := display) controls baseline frontier realization) := by
  obtain ⟨left, right⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, ⟨⟨generated, replayable, ready, compatible, closed, capacity, covered, hereditary⟩⟩⟩

/-- The temporary common scope changes the display map, not the actual
original frame, stored queries, or its replayable histories. -/
theorem WorldCallFrameData.weakenForOwner
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {realization : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available}
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier realization)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun index => nextCaps (ρ.liftVar index)) = caps) :
    ∃ nextFrame : OriginalCaptureRealization (display.weaken insertion).graph env registry target
        locals nextLeft nextRight available,
      Nonempty (WorldCallFrameData (P := P) (base := base) (caps := nextCaps) (display := display.weaken insertion)
        controls baseline frontier nextFrame) := by
  let generated := WorldGenerated.weaken data.generation insertion leftTail rightTail capsTail
  exact callFrameOfRaw (display.weaken insertion) controls baseline realization.frame generated
    data.replayable
    { annotation := data.controlled.annotation, within := data.controlled.within, sponsored := data.controlled.sponsored }
    data.compatible (data.hereditary.weaken insertion leftTail rightTail capsTail) realization.substitutions data.closed data.capacity data.covered

/-- Keep the caller frontier and destination unchanged. The owner site is a
literal retained child of the source parent, at its actual R phase. -/
theorem WorldCapturedHeadQuery.callBelow
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {callerControls : OriginalWorldControls strata callerEnv}
    {callerNode : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (caller : WorldEnvironmentProvenance strata U callerEnvironment)
    (head : WorldCapturedHeadQuery strata P base caps common commonLeft commonRight expression need capacity cutoff fuel
      frontier caller.worlds)
    (destination : World strata.rules.length) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld head.controls .expressionReindex head.display.node head.baseline, destination])
      (frontier ++ [originalCallWorld callerControls .expressionReindex callerNode caller, destination]) := by
  have smaller : WorldBelow strata.rules.length
      (originalCallWorld head.controls .expressionReindex head.display.node head.baseline)
      (originalCallWorld callerControls .expressionReindex callerNode caller) :=
    .child head.baselineMember
  have step : CallBelow strata.rules.length
      [originalCallWorld head.controls .expressionReindex head.display.node head.baseline, destination]
      [originalCallWorld callerControls .expressionReindex callerNode caller, destination] :=
    .single (.head (tail := [destination]) (replacement := [_]) (by
      intro world member
      cases List.mem_singleton.mp member
      exact smaller))
  have prepend : ∀ before : List (World strata.rules.length),
      CallBelow strata.rules.length
        (before ++ [originalCallWorld head.controls .expressionReindex head.display.node head.baseline, destination])
        (before ++ [originalCallWorld callerControls .expressionReindex callerNode caller, destination]) := by
    intro before
    induction before with
    | nil => exact step
    | cons _ _ ih => exact ih.cons _
  exact prepend frontier

/-- Replay the exact selected head under a computed original pair guard.
The caller may admit the enclosing selected frame by coverage; no literal
subset relation between its worlds and the retained baseline is required. -/
theorem WorldCapturedHeadQuery.replayWorldAt
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier envelope : List (World strata.rules.length)}
    {cutoff : Nat} {fuel : Nat → Nat}
    (head : WorldCapturedHeadQuery strata P base caps common commonLeft commonRight expression need capacity
      cutoff fuel frontier envelope)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common expression assigned)
    (controls : OriginalWorldControls strata destination.sourceEnv)
    (sameCutoff : cutoff = controls.cutoff)
    (sameFuel : fuel = controls.fuel)
    (baseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (frame : OriginalCaptureRealization destination.graph env registry target locals commonLeft commonRight available)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := destination) controls baseline frontier frame)
    (parent : List (World strata.rules.length))
    (sponsored : Sponsored frontier
      [originalCallWorld head.controls .expressionReindex head.display.node head.baseline,
       originalCallWorld controls .expressionReindex destination.node baseline])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld head.controls .expressionReindex head.display.node head.baseline,
        originalCallWorld controls .expressionReindex destination.node baseline]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps destination commonLeft commonRight need.profile
        (environmentCost destinationEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply) := by
  obtain ⟨sourceAvailable, source, generated, included, sourceClosed, environment, worlds, queries,
      replayable, compatible, _baseUses, _tablesClosed, ready, readyWorlds⟩ :=
    head.realization.closeResourcesWorld head.generated baseClosed head.ready
  let sourceData : WorldCallFrameData (P := P) (base := base) (caps := head.caps) (display := head.display)
      head.controls head.baseline frontier source := {
    generation := generated
    replayable := replayable head.replayable
    controlled := ready
    compatible := compatible _ _ (by
      have matched := head.compatible.controls_match
      simpa only [matched.1, matched.2] using head.compatible)
    closed := sourceClosed
    capacity := by rw [environment]; exact head.frameCapacity
    covered := by rw [worlds]; exact head.frameCovered
    hereditary := ⟨_tablesClosed head.hereditary.tablesClosed,
      head.hereditary.bases.cast _baseUses.symm,
      head.hereditary.bases.ready_cast _baseUses.symm head.hereditary.ready⟩ }
  obtain ⟨next, ⟨nextData⟩⟩ := data.weakenForOwner head.insertion head.leftTail head.rightTail head.capsTail
  have matched := head.compatible.controls_match
  obtain ⟨answer, ⟨answerData⟩⟩ := (bank _ smaller).observation base head.caps head.display
    (destination.weaken head.insertion) head.left head.right head.controls controls
    (matched.1.trans sameCutoff) (matched.2.trans sameFuel) head.baseline baseline frontier rfl sponsored
    source sourceData next nextData head.query
    (fun i need member => included i need (head.resources i need member)) head.queryReady
  let adapted := answer.mapQuery
    (answer.answer.reply.query.adaptRequest henv hscoped formed head.bound head.adapter)
  let adaptedData : WorldGeneratedQueryReplyData (P := P)
      (display := destination.weaken head.insertion) controls baseline frontier adapted := {
    generation := answerData.generation
    replayable := answerData.replayable
    controlled := answerData.controlled
    compatible := answerData.compatible
    query := answerData.query
    covered := answerData.covered
    hereditary := answerData.hereditary }
  obtain ⟨reply, replyData, _query, _worlds, _retained, _owned, _baseUses, _tablesClosed⟩ :=
    adaptedData.unweaken head.insertion head.leftTail head.rightTail head.capsTail adapted
  exact ⟨reply, ⟨replyData⟩⟩

/-- Actual selected owner replay. No completed transfer is supplied: the
original R bank is called at the strict child budget computed above, then its
actual returned query is adapted and unweakened with unchanged provenance. -/
theorem WorldCapturedHeadQuery.replayWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {callerControls : OriginalWorldControls strata callerEnv}
    {callerNode : EndpointState callerEnv U callerSource callerExpression callerAssigned}
    (caller : WorldEnvironmentProvenance strata U callerEnvironment)
    (head : WorldCapturedHeadQuery strata P base caps common commonLeft commonRight expression need capacity
      callerControls.cutoff callerControls.fuel frontier caller.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common expression assigned)
    (controls : OriginalWorldControls strata destination.sourceEnv)
    (sameCutoff : callerControls.cutoff = controls.cutoff)
    (sameFuel : callerControls.fuel = controls.fuel)
    (baseline : WorldEnvironmentProvenance strata U destinationEnvironment)
    (frame : OriginalCaptureRealization destination.graph env registry target locals commonLeft commonRight available)
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := destination) controls baseline frontier frame)
    (sponsored : Sponsored frontier
      [originalCallWorld callerControls .expressionReindex callerNode caller,
       originalCallWorld controls .expressionReindex destination.node baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld callerControls .expressionReindex callerNode caller,
        originalCallWorld controls .expressionReindex destination.node baseline])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps destination commonLeft commonRight need.profile
        (environmentCost destinationEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply) := by
  have matched := head.compatible.controls_match
  have ownerBelow : WorldBelow strata.rules.length
      (originalCallWorld head.controls .expressionReindex head.display.node head.baseline)
      (originalCallWorld callerControls .expressionReindex callerNode caller) := .child head.baselineMember
  have childSponsored : Sponsored frontier
      [originalCallWorld head.controls .expressionReindex head.display.node head.baseline,
       originalCallWorld controls .expressionReindex destination.node baseline] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨parent, member, below⟩ := sponsored _ (List.mem_cons_self ..)
      exact ⟨parent, member, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        (@EquationControlMeasure.less_trans strata.rules.length) ownerBelow below⟩
    · exact sponsored _ (List.mem_cons_of_mem _ member)
  exact head.replayWorldAt henv hscoped formed baseClosed destination controls sameCutoff sameFuel baseline frame data
    _ childSponsored
    (WorldCapturedHeadQuery.callBelow (callerControls := callerControls) (callerNode := callerNode) caller head
      (originalCallWorld controls .expressionReindex destination.node baseline)) bank

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
