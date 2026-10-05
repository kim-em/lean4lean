import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedConstantSite
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedConstantPruning
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNestedConstantReturn

/-! Reverse a real retained-program trace. Before the first canonical return
we keep the original function query and its hereditary depth bound. Afterwards
only its actual graded result and current controls are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

structure RetainedRawConstant
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (name : Name) (levels : List VLevel) (key : Key n) (output : Atom n) where
  sourceLevels : List VLevel
  path : RetainedConstantPath name sourceLevels state.expression
  equal : EqUpToLevels U (.const name sourceLevels) (.const name levels)
  assigned : VExpr
  site : EndpointRef state.sourceEnv U [] (.const name sourceLevels) assigned
  query : RichObs state.sourceEnv env U registry target (.ref site) [] state.right (Profile.fn key output) []
  ready : ControlledStoredQuery state.controls frontier (.observation query)
  depth : ∀ policy, query.headDepth policy ≤ state.program.certificate.headDepth policy
  live : Profile.Live env U registry target (Profile.fn key output)

structure RetainedGradedConstant
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (name : Name) (levels : List VLevel) (key : Key n) (output : Atom n) where
  assigned : VExpr
  site : EndpointRef state.sourceEnv U [] (.const name levels) assigned
  result : RichGradedResult state.sourceEnv env U registry target (.ref site) [] state.right (fun _ => [])
    (Profile.fn key output)
  ready : ControlledStoredQuery state.controls frontier (.observation result.observation)

abbrev RetainedConstantReturn
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (name : Name) (levels : List VLevel) (key : Key n) (output : Atom n) : Type :=
  RetainedRawConstant state name levels key output ⊕ RetainedGradedConstant state name levels key output

private theorem constantReturnSameSource
    {before next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (sourceEq : next.sourceEnv = before.sourceEnv)
    (controlsEq : HEq next.controls before.controls)
    (depth : ∀ policy, next.program.certificate.headDepth policy ≤ before.program.certificate.headDepth policy)
    (paths : ∀ sourceLevels, RetainedConstantPath name sourceLevels next.expression →
      RetainedConstantPath name sourceLevels before.expression)
    (answer : RetainedConstantReturn next name levels key output)
    (henv : env.Ordered) :
    Nonempty (RetainedConstantReturn before name levels key output) := by
  rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
    selected, member, demand, paid, bank⟩
  rcases next with ⟨nextEnv, nextSource, nextContext, nextExpression, nextAssigned, nextNode,
    nextProvenance, nextControls, nextLocals, nextLeft, nextRight, nextAvailable, nextFrame,
    nextCaptured, nextData, nextClosed, nextSubstitutions, nextBelow, nextRelevant, nextRank,
    nextProfile, nextFootprint, nextProgram, nextAnnotation, nextWithin, nextSponsored,
    nextResources, nextSelected, nextMember, nextDemand, nextPaid, nextBank⟩
  dsimp only at sourceEq controlsEq
  cases sourceEq
  cases eq_of_heq controlsEq
  rcases answer with answer | answer
  · obtain ⟨query, ready, _, smaller⟩ := answer.ready.pruneConstantFunction (.ref answer.site) [] right
    exact ⟨.inl {
      sourceLevels := answer.sourceLevels, path := paths _ answer.path, equal := answer.equal
      assigned := answer.assigned, site := answer.site, query := query, ready := ready
      depth := fun policy => Nat.le_trans (smaller policy) (Nat.le_trans (answer.depth policy) (depth policy))
      live := answer.live }⟩
  · obtain ⟨result, ready, _, _, _, _⟩ := answer.result.pruneConstantFunctionWorld answer.ready henv
      (.ref answer.site) [] right (fun _ => [])
    exact ⟨.inr { assigned := answer.assigned, site := answer.site, result := result, ready := ready }⟩

private theorem originalControls_eq
    {left right : OriginalWorldControls strata sourceEnv}
    (cutoff : left.cutoff = right.cutoff) (fuel : left.fuel = right.fuel) : left = right := by
  cases left
  cases right
  simp_all

/-- A charged return restores the actual saved mask. Its first level call is
paid by the original retained function depth, never by a returned F query. -/
theorem RetainedChargedTransitionWitness.returnConstant
    {before next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedChargedTransitionWitness before next)
    (answer : RetainedConstantReturn next name levels key output)
    (goalPath : RetainedConstantPath name levels goalFunction)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source ≤ env, P source) :
    Nonempty (RetainedConstantReturn before name levels key output) := by
  cases edge with
  | @intro _ _ _ _ _ recipe annotation sources resources worlds depth smaller demand member path demandEq opening =>
    rcases opening with ⟨input, pending, same, child, childControls, provenance, childWorlds,
      childSmaller, cutoffEq, fuelEq, data, childReady, readyEq, paid, bank, selected, present, nextDemand, readback, pushed⟩
    cases same
    let callerReady : ControlledStoredQuery before.controls frontier
        (.certificate (RichCert.recipe (node := before.node) recipe)) := {
      annotation := .recipe annotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichCert.stratifiedDepth] using
          Nat.le_trans (depth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)) (before.within control active)
      sponsored := fun world member => before.sponsored world (worlds member) }
    obtain ⟨assigned, ⟨destination⟩⟩ := before.constantSiteAtGoalLevels goalPath levelsWF
    rcases answer with answer | answer
    · let origin := constantOriginAt input.owner (.ref answer.site)
      obtain ⟨query, ready, _, queryDepth⟩ := answer.ready.pruneConstantFunction (.ref origin.site) [] input.realization
      let packet := CanonicalConstSitePacket.ofOrigin origin input.realization query
        (fun _ _ member => nomatch member)
      have bounded : WithinAbove before.controls.cutoff before.controls.fuel packet.chargeDepth := by
        intro control active
        have rootBound : headDepth input.owner.selected.ordinal
            (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control) control ≤
            before.controls.fuel control := by
          have bound := Nat.le_trans
            (pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control))
            (Nat.le_trans (depth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control))
              (before.within control active))
          simpa only [RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
            input.owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using bound
        have inputDepth := Nat.le_trans (queryDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control))
          (answer.depth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control))
        change headDepth input.owner.selected.ordinal
          (fun control => query.stratifiedDepth (input.strata.headOrdinal registry) control) control ≤ _
        apply Nat.le_trans _ rootBound
        change headDepth input.owner.selected.ordinal
          (fun control => query.headDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)) control ≤ _
        simp only [headDepth]
        split
        · exact Nat.le_refl _
        · exact Nat.add_le_add_right inputDepth _
      obtain ⟨result, ⟨ready⟩⟩ := packet.reindexFunctionLevelsWorld answer.equal ready.annotation formed
        before.node before.controls before.captured frontier before.paid
        (sourceClosed _ input.owner.selected.origin.sourceBelow) ready.sponsored bounded before.bank
        (.ref destination) [] before.right (fun _ => [])
      exact ⟨.inr { assigned := assigned, site := destination, result := result, ready := ready }⟩
    · let constant := EndpointState.ref answer.site
      let origin := constantOriginAt input.owner constant
      obtain ⟨result, ready, _, _, _, _⟩ := answer.result.pruneConstantFunctionWorld answer.ready henv
        (.ref origin.site) [] input.realization (fun _ => [])
      have controlsEq : childControls = canonicalQueryControls input.owner.selected
          (fun control => input.certificate.stratifiedDepth
            (input.strata.headOrdinal registry) control) :=
        originalControls_eq cutoffEq fuelEq
      have childReady : ControlledStoredQuery
          (canonicalQueryControls input.owner.selected
            (fun control => input.certificate.stratifiedDepth
              (input.strata.headOrdinal registry) control))
          frontier (.observation result.observation) := by
        simpa only [RetainedChargedOpening.next, controlsEq] using ready
      obtain ⟨result, ready, _, _, _⟩ := pending.returnConstantWorld
        before.controls before.captured frontier callerReady before.paid constant result childReady
        (.ref destination) [] before.right (fun _ => [])
      exact ⟨.inr { assigned := assigned, site := destination, result := result, ready := ready }⟩


theorem RetainedBodyTransitionWitness.returnConstant
    {before next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedBodyTransitionWitness before next)
    (answer : RetainedConstantReturn next name levels key output)
    (henv : env.Ordered) :
    Nonempty (RetainedConstantReturn before name levels key output) := by
  cases edge with
  | native expressionEq path selected admitted pending row execution continuation member readback normalized worlds depth =>
    apply constantReturnSameSource (before := before)
      (next := execution.programState pending continuation member before.sourceBelow) rfl HEq.rfl depth _ answer henv
    intro sourceLevels nextPath
    rw [expressionEq]
    exact .body nextPath
  | legacy expressionEq path selected admitted selection execution same continuation member readback normalized worlds depth =>
    apply constantReturnSameSource (before := before)
      (next := selection.programState execution same continuation member before.sourceBelow) rfl HEq.rfl _ _ answer henv
    · intro policy
      simpa only [WorldLegacyPiSizedSelection.programState, RetainedTypedProgram.certificate,
        RichCert.headDepth] using depth policy
    · intro sourceLevels nextPath
      rw [expressionEq]
      exact .body nextPath

theorem RetainedDomainTransitionWitness.returnConstant
    {before next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedDomainTransitionWitness before next)
    (answer : RetainedConstantReturn next name levels key output)
    (henv : env.Ordered) :
    Nonempty (RetainedConstantReturn before name levels key output) := by
  cases edge with
  | intro opening smaller =>
    apply constantReturnSameSource (before := before) (next := opening.next) _ _ _ _ answer henv
    all_goals
      rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
      locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
      relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
      selected, member, demand, paid, bank⟩
      rcases opening with ⟨A, B, expressionEq, u, v, hu, hv, domainNode, bodyNode, route,
      nextRank, nextProfile, nextFootprint, nextProgram, nextAnnotation, nextWithin, nextSponsored,
      nextResources, worlds, depth, nextSelected, nextMember, requestedRank, requested,
      prototypeDomain, prototypeBody, support, rows, inputPath, domainMember, outputPath,
      continuation, normalized, readback⟩
      cases expressionEq
    · rfl
    · exact HEq.rfl
    · exact depth
    · exact fun _ nextPath => .domain nextPath

/-- This fold follows the exact selected source trace. A charged edge always
returns an aligned graded result; structural edges preserve the current mode. -/
theorem RetainedProgramTrace.returnConstant
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    {terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before terminal)
    (answer : RetainedConstantReturn terminal.state name levels key output)
    (goalPath : RetainedConstantPath name levels goalFunction)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source ≤ env, P source) :
    Nonempty (RetainedConstantReturn before name levels key output) := by
  induction trace with
  | terminal witness =>
    cases witness with
    | intro opening => exact ⟨answer⟩
  | step smaller edge rest ih =>
    obtain ⟨next⟩ := ih answer
    cases edge with
    | body witness => exact witness.returnConstant next henv
    | domain witness => exact witness.returnConstant next henv
    | charged witness => exact witness.returnConstant next goalPath levelsWF henv formed sourceClosed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
