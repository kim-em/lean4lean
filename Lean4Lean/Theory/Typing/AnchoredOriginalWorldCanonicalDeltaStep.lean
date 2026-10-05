import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCanonicalDeltaComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank

/-! The shared canonical-delta computational clause invokes the actual world
bank twice on the SAME selected RHS, in its literal empty frame. The canonical
head computes both calls' control table and strict decrease. The caller's frame
and inherited frontier are unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}
  {profile : Profile n}

theorem bodyOpening
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (bound : WithinAbove controls.cutoff controls.fuel packet.stratifiedDepth) :
    WorldBelow strata.rules.length
      (originalCallWorld packet.bodyControls .fundamental packet.bodyNode .nil)
      (originalCallWorld controls .fundamental caller baseline) := by
  apply Below.root
    (openingDecrease packet.selected.ordinal_pos packet.selected.ordinal_le
      controls.cutoffBound bound _ _ _ _)
  intro child member
  cases member

/-- This is the actual canonical constructor branch, not an extra recursive
answer interface. `bodyAnnotation` and its sponsorship are the retained child
of the incoming query. The actual lower F answers supply all output channels. -/
theorem stepWorld
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (source : P packet.selected.origin.source)
    (bodyAnnotation : WorldObsProvenance strata packet.body)
    (bodyPaid : Sponsored frontier bodyAnnotation.worlds)
    (bound : WithinAbove controls.cutoff controls.fuel packet.stratifiedDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    ∃ result : RichComputationalValue sourceEnv env U registry target caller locals σ τ available profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation result.rightQuery.observation)) := by
  let childControls := packet.bodyControls
  let childFrame : OriginalRichFrame packet.selected.origin.source env U registry target .nil
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) := .nil
  let childEnvironment : WorldEnvironmentProvenance strata U
      (childFrame.dependencyEnvironment childControls.ordered) := .nil
  let childWorld := originalCallWorld childControls .fundamental packet.bodyNode childEnvironment
  have lower : WorldBelow strata.rules.length childWorld
      (originalCallWorld controls .fundamental caller baseline) := packet.bodyOpening caller controls baseline bound
  have childPaid : Sponsored frontier [childWorld] := by
    intro child member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, member, smaller⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, member,
      EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans lower smaller⟩
  have funded : CallBelow strata.rules.length (frontier ++ [childWorld])
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]) := by
    have step : CallBelow strata.rules.length [childWorld]
        [originalCallWorld controls .fundamental caller baseline] :=
      split_call (by intro child member; cases List.mem_singleton.mp member; exact lower)
    have appendLower : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ [childWorld])
          (sponsors ++ [originalCallWorld controls .fundamental caller baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  let calls := bank _ funded
  have frameData : WorldUnaryFrameData P childControls frontier childFrame childEnvironment := by
    refine ⟨?_, ?_, ?_, .nil childControls, ?_⟩
    · simpa only [childFrame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using packet.selected.origin.sourceBelow
    · simpa only [childFrame, OriginalRichFrame.nil,
        RawOriginalRichFrame.AllSources, and_true] using source
    · intro query member
      simp only [childFrame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries,
        List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  let queryReady : ControlledStoredQuery childControls frontier (.observation packet.body) := {
    annotation := bodyAnnotation
    within := fun _ _ => Nat.le_max_left _ _
    sponsored := bodyPaid }
  obtain ⟨answer, ⟨typeReady⟩, ⟨rightReady⟩⟩ := calls.computational packet.bodyNode
    packet.bodyProvenance childControls childFrame childEnvironment childEnvironment frontier
    (Nat.le_refl _) (Covered.refl _) rfl childPaid frameData closed formed .nil
    packet.body (fun _ _ member => nomatch member) queryReady
  obtain ⟨raw, ⟨rawReady⟩, _⟩ := calls.computational packet.bodyNode
    packet.bodyProvenance childControls childFrame childEnvironment childEnvironment frontier
    (Nat.le_refl _) (Covered.refl _) rfl childPaid frameData closed formed .nil
    answer.rightQuery.observation answer.rightQuery.resources rightReady
  let result := packet.assembleShared answer raw.toRichSupportedValue henv hscoped formed
    assignedWF seedAssigned caller locals σ τ available
  refine ⟨result, ⟨⟨?_, ?_, ?_⟩⟩, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · exact packet.returnProvenance answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ typeReady.annotation
  · exact packet.returnCertificate_within answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ bound typeReady.within
  · exact packet.returnProvenance_sponsored answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ typeReady.annotation childPaid typeReady.sponsored
  · exact packet.returnRawProvenance answer raw.toRichSupportedValue caller locals τ
      rightReady.annotation rawReady.annotation
  · exact packet.returnRawObservation_within answer raw.toRichSupportedValue caller locals τ
      bound rightReady.within rawReady.within
  · exact packet.returnRawProvenance_sponsored answer raw.toRichSupportedValue caller locals τ
      rightReady.annotation rawReady.annotation childPaid rightReady.sponsored rawReady.sponsored

end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
