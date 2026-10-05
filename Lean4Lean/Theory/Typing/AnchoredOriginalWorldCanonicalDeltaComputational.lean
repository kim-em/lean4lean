import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCanonicalDeltaReturn

/-! The two actual canonical RHS answers assemble a computational answer in
the shared query grammar. The right observer keeps the original child controls,
even though its new body query and support certificate have different depths.
No output control table is inferred from those new depths. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
open private footprint_empty from Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaReturn
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private noncomputable def castObsAnnotation (same : before = after)
    {query : RichObs sourceEnv env U registry target node locals σ profile before}
    (annotation : WorldObsProvenance strata query) :
    WorldObsProvenance strata
      (same ▸ query : RichObs sourceEnv env U registry target node locals σ profile after) := by
  cases same
  exact annotation

private theorem castObsAnnotation_worlds (same : before = after)
    {query : RichObs sourceEnv env U registry target node locals σ profile before}
    (annotation : WorldObsProvenance strata query) :
    (castObsAnnotation same annotation).worlds = annotation.worlds := by cases same; rfl

private noncomputable def castCertAnnotation (same : before = after)
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile before}
    (annotation : WorldCertProvenance strata query) :
    WorldCertProvenance strata
      (same ▸ query : RichCert sourceEnv env U registry target node locals σ relevant profile after) := by
  cases same
  exact annotation

private theorem castCertAnnotation_worlds (same : before = after)
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile before}
    (annotation : WorldCertProvenance strata query) :
    (castCertAnnotation same annotation).worlds = annotation.worlds := by cases same; rfl

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}
  {profile : Profile n}
  (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
  (answer : RichComputationalValue packet.selected.origin.source env U registry target
    packet.bodyNode [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
  (raw : RichSupportedValue packet.selected.origin.source env U registry target
    packet.bodyNode [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw)

noncomputable def returnRawProvenance
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (τ : Subst)
    (queryAnnotation : WorldObsProvenance strata answer.rightQuery.observation)
    (codeAnnotation : WorldCertProvenance strata raw.certificate) :
    WorldObsProvenance strata ((packet.returnRaw answer raw).observation caller locals τ) :=
  .canonicalDelta packet.lookup packet.nameEq packet.registered packet.seedWF
    packet.seedLength packet.levelsWF packet.equivalent packet.bodyClosed packet.typeClosed
    (packet.returnRaw answer raw).certificate raw.typed
    (castCertAnnotation (footprint_empty raw.resources) codeAnnotation)
    (castObsAnnotation (footprint_empty answer.rightQuery.resources) queryAnnotation)
    packet.bodyControls packet.typeProvenance packet.bodyProvenance

theorem returnRawProvenance_worlds
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (τ : Subst)
    (queryAnnotation : WorldObsProvenance strata answer.rightQuery.observation)
    (codeAnnotation : WorldCertProvenance strata raw.certificate) :
    (packet.returnRawProvenance answer raw caller locals τ queryAnnotation codeAnnotation).worlds =
      packet.typeSite.worlds ++ packet.bodySite.worlds ++
        codeAnnotation.worlds ++ queryAnnotation.worlds := by
  change packet.typeSite.worlds ++ packet.bodySite.worlds ++
    (castCertAnnotation (footprint_empty raw.resources) codeAnnotation).worlds ++
    (castObsAnnotation (footprint_empty answer.rightQuery.resources) queryAnnotation).worlds = _
  rw [castCertAnnotation_worlds, castObsAnnotation_worlds]

/-- The actual same-frame F answer. Both empty-footprint returned queries
work with the caller's existing resource table; that table is unchanged. -/
noncomputable def assembleShared
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst) (available : Valuation) :
    RichComputationalValue sourceEnv env U registry target caller locals σ τ available profile where
  support := answer.support
  footprint := []
  certificate := packet.returnCertificate answer.toRichSupportedValue assignedWF seedAssigned
    caller.typeFormation.node locals σ
  resources := fun _ _ member => nomatch member
  typed := answer.typed
  typeCode := packet.returnCertificate_related answer.toRichSupportedValue assignedWF seedAssigned
    caller.typeFormation.node locals σ henv σ
  related := (packet.assembleReturn henv hscoped formed assignedWF seedAssigned caller locals σ τ answer raw).related
  rightQuery := {
    rank := answer.rightQuery.rank
    bound := answer.rightQuery.bound
    raw := answer.rightQuery.raw
    footprint := []
    observation := (packet.returnRaw answer raw).observation caller locals τ
    adapter := answer.rightQuery.adapter
    resources := fun _ _ member => nomatch member
    live := answer.rightQuery.live }

theorem returnRawProvenance_sponsored
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (τ : Subst)
    (queryAnnotation : WorldObsProvenance strata answer.rightQuery.observation)
    (codeAnnotation : WorldCertProvenance strata raw.certificate)
    (bodyPaid : Sponsored frontier packet.bodySite.worlds)
    (queryPaid : Sponsored frontier queryAnnotation.worlds)
    (codePaid : Sponsored frontier codeAnnotation.worlds) :
    Sponsored frontier
      (packet.returnRawProvenance answer raw caller locals τ queryAnnotation codeAnnotation).worlds := by
  rw [returnRawProvenance_worlds]
  have typePaid : Sponsored frontier packet.typeSite.worlds := by
    intro child member
    obtain ⟨body, belongs, equal | smaller⟩ := packet.typeSite_covered child member
    · subst child
      exact bodyPaid body belongs
    · obtain ⟨sponsor, present, lower⟩ := bodyPaid body belongs
      exact ⟨sponsor, present,
        EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
          EquationControlMeasure.less_trans smaller lower⟩
  exact ((typePaid.merge bodyPaid).merge codePaid).merge queryPaid

theorem returnRawObservation_within
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (τ : Subst)
    (bounded : WithinAbove cutoff fuel packet.stratifiedDepth)
    (queryBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control))
    (codeBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => raw.certificate.stratifiedDepth (strata.headOrdinal registry) control)) :
    WithinAbove cutoff fuel (fun control =>
      ((packet.returnRaw answer raw).observation caller locals τ).stratifiedDepth
        (strata.headOrdinal registry) control) := by
  rw [(packet.returnRaw answer raw).observation_stratifiedDepth,
    packet.returnRaw_stratifiedDepth answer raw]
  apply rebuild packet.selected.ordinal_pos bounded
  intro control active
  exact Nat.max_le.mpr ⟨queryBound control active, codeBound control active⟩

/-- Joint preservation for the actual computational result, retaining all
three annotations returned by the two concrete RHS calls. -/
theorem assembleShared_preserves
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (inputType : WorldCertProvenance strata packet.certificate)
    (inputBody : WorldObsProvenance strata packet.body)
    (inputPaid : Sponsored frontier
      (packet.observationProvenance caller locals σ inputType inputBody).worlds)
    (bounded : WithinAbove cutoff fuel packet.stratifiedDepth)
    (typeAnnotation : WorldCertProvenance strata answer.certificate)
    (queryAnnotation : WorldObsProvenance strata answer.rightQuery.observation)
    (codeAnnotation : WorldCertProvenance strata raw.certificate)
    (typePaid : Sponsored frontier typeAnnotation.worlds)
    (queryPaid : Sponsored frontier queryAnnotation.worlds)
    (codePaid : Sponsored frontier codeAnnotation.worlds)
    (typeBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control))
    (queryBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control))
    (codeBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => raw.certificate.stratifiedDepth (strata.headOrdinal registry) control)) :
    let result := packet.assembleShared answer raw henv hscoped formed assignedWF seedAssigned caller locals σ τ available
    ∃ outputType : WorldCertProvenance strata result.certificate,
      ∃ outputQuery : WorldObsProvenance strata result.rightQuery.observation,
        outputType.worlds = packet.typeSite.worlds ++ typeAnnotation.worlds ∧
        outputQuery.worlds = packet.typeSite.worlds ++ packet.bodySite.worlds ++
          codeAnnotation.worlds ++ queryAnnotation.worlds ∧
        Sponsored frontier outputType.worlds ∧ Sponsored frontier outputQuery.worlds ∧
        WithinAbove cutoff fuel (fun control => result.certificate.stratifiedDepth (strata.headOrdinal registry) control) ∧
        WithinAbove cutoff fuel (fun control => result.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) := by
  have bodyPaid := packet.observation_body_sponsored caller locals σ inputType inputBody inputPaid
  refine ⟨packet.returnProvenance answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ typeAnnotation,
    packet.returnRawProvenance answer raw caller locals τ queryAnnotation codeAnnotation,
    rfl, packet.returnRawProvenance_worlds answer raw caller locals τ queryAnnotation codeAnnotation,
    ?_, ?_, ?_, ?_⟩
  · exact packet.returnProvenance_sponsored answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ typeAnnotation bodyPaid typePaid
  · exact packet.returnRawProvenance_sponsored answer raw caller locals τ
      queryAnnotation codeAnnotation bodyPaid queryPaid codePaid
  · exact packet.returnCertificate_within answer.toRichSupportedValue assignedWF seedAssigned
      caller.typeFormation.node locals σ bounded typeBound
  · exact packet.returnRawObservation_within answer raw caller locals τ bounded queryBound codeBound

end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
