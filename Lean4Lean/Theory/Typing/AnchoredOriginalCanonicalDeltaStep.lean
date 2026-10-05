import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth
import Lean4Lean.Theory.Typing.EquationStratifiedFuel
import Lean4Lean.Theory.Typing.EquationControls

/-! A fixed-original canonical delta step. Both recursive calls are made here:
first on the stored RHS query, then on that answer's actual graded raw query.
Their real empty-frame costs enter the alternating key. Only lawful controls
above the canonical source cutoff are preserved; higher-head masks restore the
caller's lower controls on the SAME returned value and type packets. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def CanonicalDeltaTypePacket.stratifiedDepth
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) : Nat → Nat :=
  headDepth (strata.select packet.registered.2).ordinal
    (fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control)

private theorem stratifiedObs_cast (same : before = after)
    (query : RichObs sourceEnv env U registry target node locals σ profile before)
    (rank : Name → Nat) (control : Nat) :
    (same ▸ query : RichObs sourceEnv env U registry target node locals σ profile after).stratifiedDepth rank control =
      query.stratifiedDepth rank control := by cases same; rfl

private theorem stratifiedCert_cast (same : before = after)
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile before)
    (rank : Name → Nat) (control : Nat) :
    (same ▸ query : RichCert sourceEnv env U registry target node locals σ relevant profile after).stratifiedDepth rank control =
      query.stratifiedDepth rank control := by cases same; rfl

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel} {profile : Profile n}

noncomputable def stratifiedChildren
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (control : Nat) : Nat :=
  max (packet.body.stratifiedDepth (strata.headOrdinal registry) control)
    (packet.certificate.stratifiedDepth (strata.headOrdinal registry) control)

noncomputable def stratifiedDepth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) : Nat → Nat :=
  headDepth packet.selected.ordinal packet.stratifiedChildren

theorem returnRaw_stratifiedDepth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (raw : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw) :
    (packet.returnRaw answer raw).stratifiedDepth =
      headDepth packet.selected.ordinal (fun control =>
        max (answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control)
          (raw.certificate.stratifiedDepth (strata.headOrdinal registry) control)) := by
  funext control
  simp only [stratifiedDepth, stratifiedChildren, returnRaw, selected,
    headDepth, stratifiedObs_cast, stratifiedCert_cast]

theorem returnType_stratifiedDepth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
    (locals : List Nat) (σ : Subst) :
    (packet.returnType answer assignedWF seedAssigned caller locals σ).packet.stratifiedDepth =
      headDepth packet.selected.ordinal (fun control =>
        answer.certificate.stratifiedDepth (strata.headOrdinal registry) control) := rfl

noncomputable def bodyNode
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :=
  EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF))

noncomputable def bodySchedule
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) : Nat :=
  richSchedule .fundamental
    (Closure.close (packet.bodyNode.dependencyOrigin packet.selected.origin.ordered) []).cost

/-- Exact fixed-original lower F clause. It returns SAME-witness bounds on
the chosen raw observer and assigned certificate, not two unrelated answers.
The source context, actual endpoint, empty frame and cost are fixed here. -/
def ComputationalBelow
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (parent : EquationControlMeasure.Key strata.rules.length) : Prop :=
  ∀ {grade : Nat} {requested : Profile grade} {footprint : Footprint}
    (query : RichObs packet.selected.origin.source env U registry target packet.bodyNode
      [] packet.bodyRealization requested footprint),
    footprint.Available (fun _ => []) →
    ∀ (fuel : Nat → Nat),
    WithinAbove (packet.selected.ordinal - 1) fuel
      (fun control => query.stratifiedDepth (strata.headOrdinal registry) control) →
    strata.SourceCutoff packet.selected.origin.source (packet.selected.ordinal - 1) →
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.selected.ordinal - 1) fuel
        packet.selected.origin.ordered.constantCount packet.bodySchedule) parent →
    ∃ answer : RichComputationalValue packet.selected.origin.source env U registry target packet.bodyNode
        [] packet.bodyRealization packet.bodyRealization (fun _ => []) requested,
      WithinAbove (packet.selected.ordinal - 1) fuel
        (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) ∧
      WithinAbove (packet.selected.ordinal - 1) fuel
        (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control)

/-- Two actual lower calls produce every delta output channel. No supplied
smaller-call inequality, raw support certificate or caller code-R is needed. -/
theorem step
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.stratifiedDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ answer : RichComputationalValue packet.selected.origin.source env U registry target packet.bodyNode
        [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile,
      ∃ _raw : RichComputationalValue packet.selected.origin.source env U registry target packet.bodyNode
          [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw,
        ∃ result : CanonicalDeltaReturnResult packet caller locals σ τ answer,
          WithinAbove cutoff fuel result.rightQuery.packet.stratifiedDepth ∧
          WithinAbove cutoff fuel result.typeQuery.packet.stratifiedDepth := by
  have decrease : EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.selected.ordinal - 1)
        packet.stratifiedChildren packet.selected.origin.ordered.constantCount packet.bodySchedule)
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule) :=
    openingDecrease packet.selected.ordinal_pos packet.selected.ordinal_le cutoffBound bounded
      constants schedule packet.selected.origin.ordered.constantCount packet.bodySchedule
  have sourceBound := packet.selected.sourceCutoff
  obtain ⟨answer, queryBound, typeBound⟩ := lower packet.body
    (fun _ _ member => nomatch member) packet.stratifiedChildren
    (fun _ _ => Nat.le_max_left _ _) sourceBound decrease
  obtain ⟨raw, _, rawTypeBound⟩ := lower answer.rightQuery.observation answer.rightQuery.resources
    packet.stratifiedChildren queryBound sourceBound decrease
  refine ⟨answer, raw, packet.assembleReturn henv hscoped formed assignedWF seedAssigned caller locals σ τ
    answer raw.toRichSupportedValue, ?_, ?_⟩
  · change WithinAbove cutoff fuel (packet.returnRaw answer raw.toRichSupportedValue).stratifiedDepth
    rw [returnRaw_stratifiedDepth]
    apply rebuild packet.selected.ordinal_pos bounded
    intro control active
    exact Nat.max_le.mpr ⟨queryBound control active, rawTypeBound control active⟩
  · change WithinAbove cutoff fuel
      (packet.returnType answer.toRichSupportedValue assignedWF seedAssigned caller.typeFormation.node locals σ).packet.stratifiedDepth
    rw [returnType_stratifiedDepth]
    exact rebuild packet.selected.ordinal_pos bounded typeBound

end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
