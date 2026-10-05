import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSharedReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyEndpoints

/-! Exact closed-site provenance for the constant carrier. Both original
sites have literal empty frames. The returned assigned certificate retains
precisely the selected child's certificate and annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalConstSitePacket

noncomputable def siteControls
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) :
    OriginalWorldControls strata packet.owner.selected.origin.source where
  ordered := packet.owner.selected.origin.ordered
  cutoff := packet.owner.selected.ordinal - 1
  cutoffBound := Nat.le_trans (Nat.sub_le _ _) packet.owner.selected.ordinal_le
  sourceCutoff := packet.owner.sourceCutoff
  fuel := fun control => packet.query.stratifiedDepth (strata.headOrdinal registry) control

noncomputable def originalSite
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) :
    WorldQuerySite (registry := registry) (target := target) strata
      (.ref packet.site) [] packet.realization :=
  .empty packet.siteControls (EndpointProvenance.ofLocation .here .nil) packet.realization

noncomputable def assignedSite
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) :
    WorldQuerySite (registry := registry) (target := target) strata
      (EndpointState.ref packet.site).typeFormation.node [] packet.realization :=
  .empty packet.siteControls (EndpointProvenance.ofLocation (.assignedFormation .here) .nil)
    packet.realization

/-- The exact empty-frame original site is strictly below the current call
by the canonical opening rule, independently of the caller's capture list. -/
theorem originalSite_below
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (captures : List (EquationWorldClosureOrder.Closure
      (EquationControlMeasure.Key strata.rules.length)))
    (bounded : WithinAbove cutoff fuel packet.chargeDepth) :
    ∀ world ∈ packet.originalSite.worlds,
      Below (@EquationControlMeasure.Less strata.rules.length) world
        (.node (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule) captures) := by
  intro world member
  change world ∈ [EquationWorldClosureOrder.Closure.node
    (EquationControlMeasure.key strata.rules.length packet.siteControls.cutoff packet.siteControls.fuel
      packet.siteControls.ordered.constantCount packet.siteSchedule) []] at member
  cases List.mem_singleton.mp member
  exact .root (packet.openingDecrease cutoff cutoffBound fuel constants schedule bounded)
    (by intro child member; cases member)

/-- The exact shared leaf retains the original closed child annotation.
Controls come from this packet's computed canonical opening. -/
noncomputable def observationProvenance
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (annotation : WorldObsProvenance strata packet.query) :
    WorldObsProvenance strata (packet.observation caller locals σ) :=
  .canonicalConst packet.origin packet.realization packet.query packet.resources annotation
    packet.siteControls (EndpointProvenance.ofLocation .here .nil)

@[simp] theorem observationProvenance_worlds
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (annotation : WorldObsProvenance strata packet.query) :
    (packet.observationProvenance caller locals σ annotation).worlds =
      packet.originalSite.worlds ++ annotation.worlds := rfl

section Return
variable
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (caller : EndpointState sourceEnv U source (packet.info.type.instL callerLevels) (.sort level))
    (locals : List Nat) (σ : Subst)

noncomputable def sharedAssignedCertificate :
    RichCert sourceEnv env U registry target caller locals σ true answer.support [] :=
  .recipe (.root source locals σ packet.owner (EndpointState.ref packet.site).typeFormation.node
    packet.typeClosed.instL
    (EqUpToLevels.instL_expr packet.info.type packet.assignedWF callerWF equivalent)
    packet.realization answer.certificate answer.resources)

noncomputable def sharedAssignedProvenance
    (annotation : WorldCertProvenance strata answer.certificate) :
    WorldCertProvenance strata
      (packet.sharedAssignedCertificate answer callerWF equivalent caller locals σ) :=
  .recipe (.root source locals σ packet.owner (EndpointState.ref packet.site).typeFormation.node
    packet.typeClosed.instL
    (EqUpToLevels.instL_expr packet.info.type packet.assignedWF callerWF equivalent)
    packet.realization answer.certificate answer.resources annotation
    packet.siteControls (EndpointProvenance.ofLocation (.assignedFormation .here) .nil))

theorem sharedAssignedProvenance_worlds
    (annotation : WorldCertProvenance strata answer.certificate) :
    (packet.sharedAssignedProvenance answer callerWF equivalent caller locals σ annotation).worlds =
      packet.assignedSite.worlds ++ annotation.worlds := rfl

theorem sharedAssigned_related
    (hWF : ∀ level ∈ callerLevels, level.WF U)
    (hEq : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (henv : env.Ordered) (τ : Subst) :
    TypeRelated env U registry target ((packet.info.type.instL callerLevels).subst σ)
      ((packet.info.type.instL callerLevels).subst τ) answer.support := by
  simpa only [packet.typeClosed.instL.subst_eq (σ := σ) .zero,
    packet.typeClosed.instL.subst_eq (σ := τ) .zero] using
    packet.returnType_related henv answer hWF hEq σ

theorem sharedAssigned_depth (policy : Name → Nat → Nat) :
    (packet.sharedAssignedCertificate answer callerWF equivalent caller locals σ).headDepth policy =
      policy packet.ownerName (answer.certificate.headDepth policy) := by
  simp only [sharedAssignedCertificate, RichCert.headDepth, RichCodeRecipe.headDepth]

end Return

theorem assignedSite_covered
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      packet.assignedSite.worlds packet.originalSite.worlds := by
  have cost := (EndpointState.ref packet.site).typeFormation_dependency_cost_le
    packet.siteControls.ordered []
  change Covered _
    [EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length packet.siteControls.cutoff packet.siteControls.fuel
        packet.siteControls.ordered.constantCount (richSchedule .fundamental
          (Closure.close ((EndpointState.ref packet.site).typeFormation.node.dependencyOrigin
            packet.siteControls.ordered) []).cost)) []]
    [EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length packet.siteControls.cutoff packet.siteControls.fuel
        packet.siteControls.ordered.constantCount (richSchedule .fundamental
          (Closure.close ((EndpointState.ref packet.site).dependencyOrigin
            packet.siteControls.ordered) []).cost)) []]
  intro child member
  cases List.mem_singleton.mp member
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases Nat.eq_or_lt_of_le cost with equal | smaller
  · left
    rw [equal]
  · right
    exact original_child (richSchedule_strict smaller .fundamental .fundamental) _ _ _ _ _

/-- The exact shared F answer, retaining the SAME lower computational answer
in both the assigned certificate and the right observation. -/
noncomputable def assembleShared
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (henv : env.Ordered)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.info.type.instL callerLevels))
    (locals : List Nat) (σ τ : Subst) (available : Valuation) :
    RichComputationalValue sourceEnv env U registry target caller locals σ τ available profile where
  support := answer.support
  footprint := []
  certificate := packet.sharedAssignedCertificate answer.toRichSupportedValue callerWF equivalent
    caller.typeFormation.node locals σ
  resources := fun _ _ member => nomatch member
  typed := answer.typed
  related := packet.returnRelated henv answer.toRichSupportedValue callerWF equivalent σ τ
  typeCode := packet.returnType_related henv answer.toRichSupportedValue callerWF equivalent σ
  rightQuery := {
    rank := answer.rightQuery.rank
    bound := answer.rightQuery.bound
    raw := answer.rightQuery.raw
    footprint := []
    observation := (packet.returnRaw answer).observation caller locals τ
    adapter := answer.rightQuery.adapter
    resources := fun _ _ member => nomatch member
    live := answer.rightQuery.live }

/-- Computed children rebuild the parent's exact masks and opening sites.
The premises are the actual smaller answer's two annotations, not a supplied
annotation or semantic answer for the returned caller query. -/
theorem assembleShared_controlled
    (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.owner.selected.origin.source env U registry target
      (.ref packet.site) [] packet.realization packet.realization (fun _ => []) profile)
    (henv : env.Ordered)
    (callerWF : ∀ level ∈ callerLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) packet.assignedLevels callerLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.info.type.instL callerLevels))
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (controls : OriginalWorldControls strata controlSource)
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (bounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth)
    (sitePaid : Sponsored frontier packet.originalSite.worlds)
    (typeReady : ControlledStoredQuery packet.siteControls frontier (.certificate answer.certificate))
    (queryReady : ControlledStoredQuery packet.siteControls frontier (.observation answer.rightQuery.observation)) :
    let result := packet.assembleShared answer henv callerWF equivalent caller locals σ τ available
    ∃ typeOutput : ControlledStoredQuery controls frontier (.certificate result.certificate),
      ∃ queryOutput : ControlledStoredQuery controls frontier (.observation result.rightQuery.observation),
        typeOutput.annotation.worlds = packet.assignedSite.worlds ++ typeReady.annotation.worlds ∧
        queryOutput.annotation.worlds = packet.originalSite.worlds ++ queryReady.annotation.worlds := by
  let codeAnnotation := packet.sharedAssignedProvenance answer.toRichSupportedValue callerWF equivalent
    caller.typeFormation.node locals σ typeReady.annotation
  let queryAnnotation : WorldObsProvenance strata ((packet.returnRaw answer).observation caller locals τ) :=
    .canonicalConst (packet.returnRaw answer).origin packet.realization answer.rightQuery.observation
      answer.rightQuery.resources queryReady.annotation packet.siteControls
      (EndpointProvenance.ofLocation .here .nil)
  have codeWorlds : codeAnnotation.worlds = packet.assignedSite.worlds ++ typeReady.annotation.worlds := rfl
  have queryWorlds : queryAnnotation.worlds = packet.originalSite.worlds ++ queryReady.annotation.worlds := rfl
  have typePaid : Sponsored frontier packet.assignedSite.worlds := by
    intro world member
    obtain ⟨original, present, equal | less⟩ := packet.assignedSite_covered world member
    · subst world
      exact sitePaid original present
    · obtain ⟨sponsor, present, lower⟩ := sitePaid original present
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans less lower⟩
  refine ⟨⟨codeAnnotation, ?_, ?_⟩, ⟨queryAnnotation, ?_, ?_⟩, ?_, ?_⟩
  · intro control active
    change (packet.sharedAssignedCertificate answer.toRichSupportedValue callerWF equivalent
      caller.typeFormation.node locals σ).stratifiedDepth (strata.headOrdinal registry) control ≤ _
    simp only [RichCert.stratifiedDepth, sharedAssigned_depth, stratifiedHeadPolicy]
    rw [packet.owner.headOrdinal_eq]
    exact EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded typeReady.within control active
  · change Sponsored frontier codeAnnotation.worlds
    rw [codeWorlds]
    exact typePaid.merge typeReady.sponsored
  · intro control active
    change ((packet.returnRaw answer).observation caller locals τ).stratifiedDepth
      (strata.headOrdinal registry) control ≤ _
    simp only [RichObs.stratifiedDepth, observation_headDepth, returnRaw, stratifiedHeadPolicy]
    rw [packet.owner.headOrdinal_eq]
    exact EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos bounded queryReady.within control active
  · change Sponsored frontier queryAnnotation.worlds
    rw [queryWorlds]
    exact sitePaid.merge queryReady.sponsored
  · exact codeWorlds
  · exact queryWorlds

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
