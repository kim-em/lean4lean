import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSite

/-! A closed constant subterm is opened in its enclosing owner's selected
source. One actual lower F call supplies both returned queries. The caller's
primitive constant endpoint determines its assigned universe instance; no
comparison of the caller and canonical originals is required. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalConstSitePacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel} {profile : Profile n}

/-- The conditional induction clause is restricted to the stored actual
constant node, its empty frame, and its computed original cost. Both bounds
refer to the same returned computational value. -/
def ComputationalBelow
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (parent : EquationControlMeasure.Key strata.rules.length) : Prop :=
  ∀ fuel : Nat → Nat,
    WithinAbove (packet.owner.selected.ordinal - 1) fuel
      (fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control) →
    strata.SourceCutoff packet.owner.selected.origin.source (packet.owner.selected.ordinal - 1) →
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.owner.selected.ordinal - 1) fuel
        packet.owner.selected.origin.ordered.constantCount packet.siteSchedule) parent →
    ∃ answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
        (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile,
      WithinAbove (packet.owner.selected.ordinal - 1) fuel
        (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) ∧
      WithinAbove (packet.owner.selected.ordinal - 1) fuel
        (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control)

theorem openingDecrease
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants schedule : Nat) (bounded : WithinAbove cutoff fuel packet.chargeDepth) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.owner.selected.ordinal - 1)
        (fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control)
        packet.owner.selected.origin.ordered.constantCount packet.siteSchedule)
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule) :=
  EquationStratifiedFuel.openingDecrease packet.owner.selected.ordinal_pos
    packet.owner.selected.ordinal_le cutoffBound bounded constants schedule
    packet.owner.selected.origin.ordered.constantCount packet.siteSchedule

/-- Opening and returning use one lower call. The enclosing owner's mask is
restored on both actual returned packets, even when the displayed constant
is a different name from that owner. -/
theorem step
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.info.type.instL callerLevels))
    (locals : List Nat) (σ τ : Subst)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
        (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile,
      ∃ result : CanonicalConstSiteReturnResult packet caller locals σ τ answer,
        WithinAbove cutoff fuel result.rightQuery.packet.chargeDepth ∧
        WithinAbove cutoff fuel result.typeQuery.packet.chargeDepth := by
  let children := fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control
  obtain ⟨answer, queryBound, typeBound⟩ := lower children
    (fun _ _ => Nat.le_refl _) packet.owner.sourceCutoff
    (packet.openingDecrease cutoff cutoffBound fuel constants schedule bounded)
  refine ⟨answer, packet.assembleReturn henv callerWF equivalent caller locals σ τ answer, ?_, ?_⟩
  · change WithinAbove cutoff fuel (packet.returnRaw answer).chargeDepth
    rw [returnRaw_depth]
    exact EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded queryBound
  · change WithinAbove cutoff fuel (headDepth packet.owner.selected.ordinal
      (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control))
    exact EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded typeBound

/-- Invert either actual primitive constDF endpoint to obtain the caller's
assigned instance, then run the controlled step without an alignment premise. -/
theorem primitiveStep
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (locals : List Nat) (σ τ : Subst)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
        (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile,
      ∃ result : CanonicalConstSiteReturnResult packet (.ref reference) locals σ τ answer,
        WithinAbove cutoff fuel result.rightQuery.packet.chargeDepth ∧
        WithinAbove cutoff fuel result.typeQuery.packet.chargeDepth := by
  obtain ⟨callerLevels, callerWF, equivalent, assignedEq⟩ :=
    packet.primitiveAssigned below reference rfl primitive
  cases assignedEq
  exact packet.step henv callerWF equivalent (.ref reference)
    locals σ τ cutoff cutoffBound fuel constants schedule bounded lower

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
