import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstLevelBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantValuePruning
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstSharedReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank

/-! Level alignment opens a genuine closed equality in the retained owner's
source. Its arbitrary finite original cost is paid by the canonical opening;
the returned graded function keeps the actual lower answer and annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace CanonicalConstSitePacket

theorem LevelBridge.executeWorld
    {packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)}
    (bridge : packet.LevelBridge nextLevels)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (annotation : WorldObsProvenance strata packet.query)
    (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (source : P packet.owner.selected.origin.source)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    ∃ answer : OriginalDirectionalEqualityResult bridge.original true env registry target
        [] packet.realization packet.realization (fun _ => []) (Profile.fn key output),
    ∃ ready : ControlledStoredQuery packet.siteControls frontier (.observation answer.rightQuery.observation),
      WithinAbove controls.cutoff controls.fuel
        (bridge.packet equal answer.rightQuery.observation answer.rightQuery.resources).chargeDepth := by
  obtain ⟨query, queryAnnotation, worlds, depth⟩ :=
    annotation.pruneConstantFunction (.ref (.left bridge.original)) [] packet.realization
  let childControls := packet.siteControls
  let childFrame : OriginalRichFrame packet.owner.selected.origin.source env U registry target .nil
      [] packet.realization packet.realization (fun _ => []) := .nil
  let childEnvironment : WorldEnvironmentProvenance strata U
      (childFrame.dependencyEnvironment childControls.ordered) := .nil
  let childWorld := originalCallWorld childControls .fundamental (.ref (.left bridge.original)) childEnvironment
  have lower : WorldBelow strata.rules.length childWorld
      (originalCallWorld controls .fundamental caller baseline) := by
    apply Below.root
      (EquationStratifiedFuel.openingDecrease packet.owner.selected.ordinal_pos packet.owner.selected.ordinal_le
        controls.cutoffBound bounded controls.ordered.constantCount
        (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
        packet.owner.selected.origin.ordered.constantCount
        (richSchedule .fundamental
          (Closure.close ((EndpointState.ref (.left bridge.original)).dependencyOrigin
            packet.owner.selected.origin.ordered) []).cost))
    intro value member
    cases member
  have childPaid : Sponsored frontier [childWorld] := by
    intro value member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, paid⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present,
      EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans lower paid⟩
  have funded : CallBelow strata.rules.length (frontier ++ [childWorld])
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]) := by
    have step : CallBelow strata.rules.length [childWorld]
        [originalCallWorld controls .fundamental caller baseline] :=
      split_call (by intro value member; cases List.mem_singleton.mp member; exact lower)
    have appendLower : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ [childWorld])
          (sponsors ++ [originalCallWorld controls .fundamental caller baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  have frameData : WorldUnaryFrameData P childControls frontier childFrame childEnvironment := by
    refine ⟨?_, ?_, ?_, .nil childControls, ?_⟩
    · simpa only [childFrame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using packet.owner.selected.origin.sourceBelow
    · simpa only [childFrame, OriginalRichFrame.nil, RawOriginalRichFrame.AllSources, and_true] using source
    · intro query member
      simp only [childFrame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries,
        List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  have atomClosed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  let queryReady : ControlledStoredQuery childControls frontier (.observation query) := {
    annotation := queryAnnotation
    within := fun control _ => depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)
    sponsored := fun world member => sponsored world (worlds member) }
  obtain ⟨answer, ⟨ready⟩⟩ := (bank _ funded).equality bridge.original true
    (EndpointProvenance.ofLocation .here .nil) childControls childFrame childEnvironment childEnvironment
    frontier (Nat.le_refl _) (Covered.refl _) rfl childPaid frameData atomClosed formed .nil
    query (fun _ _ member => nomatch member) queryReady
  refine ⟨answer, ready, ?_⟩
  exact EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded ready.within

/-- Both endpoints of the equality remain literal original endpoints. The
canonical destination observation wraps the actual graded right query, and its
new opening site is funded directly below the current caller. -/
theorem LevelBridge.reindexFunctionWorld
    {packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)}
    (bridge : packet.LevelBridge nextLevels)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (annotation : WorldObsProvenance strata packet.query)
    (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (source : P packet.owner.selected.origin.source)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (destination : EndpointState sourceEnv U sourceContext (.const name nextLevels) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    ∃ result : RichGradedResult sourceEnv env U registry target destination locals σ available (Profile.fn key output),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  obtain ⟨answer, ready, bounded⟩ := bridge.executeWorld equal annotation formed caller controls baseline frontier
    callerPaid source sponsored bounded bank
  let nextPacket := bridge.packet equal answer.rightQuery.observation answer.rightQuery.resources
  let next : RichGradedResult sourceEnv env U registry target destination locals σ available (Profile.fn key output) := {
    rank := answer.rightQuery.rank, bound := answer.rightQuery.bound, raw := answer.rightQuery.raw
    footprint := [], observation := nextPacket.observation destination locals σ
    adapter := answer.rightQuery.adapter, resources := fun _ _ member => nomatch member
    live := answer.rightQuery.live }
  let nextAnnotation := nextPacket.observationProvenance destination locals σ ready.annotation
  refine ⟨next, ⟨⟨nextAnnotation, ?_, ?_⟩⟩⟩
  · intro control active
    simpa only [StoredOriginalQuery.headDepth, next, RichObs.stratifiedDepth, observation_headDepth,
      nextPacket, LevelBridge.packet, ofOrigin, LevelBridge.origin, stratifiedHeadPolicy,
      chargeDepth, EquationStratifiedFuel.headDepth,
      packet.owner.headOrdinal_eq] using bounded control active
  · intro world member
    change world ∈ nextPacket.originalSite.worlds ++ ready.annotation.worlds at member
    rcases List.mem_append.mp member with member | member
    · have lower := nextPacket.originalSite_below controls.cutoff controls.cutoffBound controls.fuel
        controls.ordered.constantCount
        (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
        baseline.worlds bounded world member
      obtain ⟨sponsor, present, paid⟩ := callerPaid _ (List.mem_singleton_self _)
      exact ⟨sponsor, present,
        EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
          EquationControlMeasure.less_trans lower paid⟩
    · exact ready.sponsored world member

/-- The executable caller supplies level equivalence, not a constructed
equality original or a completed function answer. -/
theorem reindexFunctionLevelsWorld
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (annotation : WorldObsProvenance strata packet.query)
    (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (source : P packet.owner.selected.origin.source)
    (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (destination : EndpointState sourceEnv U sourceContext (.const name nextLevels) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    ∃ result : RichGradedResult sourceEnv env U registry target destination locals σ available (Profile.fn key output),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  obtain ⟨bridge⟩ := packet.levelBridge equal
  exact bridge.reindexFunctionWorld equal annotation formed caller controls baseline frontier
    callerPaid source sponsored bounded bank destination locals σ available

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
