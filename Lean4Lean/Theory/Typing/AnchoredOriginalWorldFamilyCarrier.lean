import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstSharedReturn

/-! A finite source-indexed family carrier retains the actual canonical
constant packets around a selected header. Updated payloads are reconstructed
through those exact sites; no constant owner or origin equality is invented. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive WorldFamilyCarrier {strata : EquationStratification env}
    (header : IndependentFamilyHeader env U registry target name levels) :
    {sourceEnv : VEnv} → OriginalWorldControls strata sourceEnv →
      OriginalWorldControls strata header.origin.source → Type where
  | direct (controls : OriginalWorldControls strata header.registrationEnv) :
      WorldFamilyCarrier header controls (controls.atHeader header.origin)
  | canonical {controls : OriginalWorldControls strata sourceEnv}
      (packet : CanonicalConstSitePacket env U registry target strata name levels profile)
      (child : WorldFamilyCarrier header packet.siteControls headerControls)
      (charged : WithinAbove controls.cutoff controls.fuel packet.chargeDepth) :
      WorldFamilyCarrier header controls headerControls

noncomputable def WorldFamilyCarrier.openings
    {strata : EquationStratification env}
    {header : IndependentFamilyHeader env U registry target name levels}
    {controls : OriginalWorldControls strata sourceEnv}
    {headerControls : OriginalWorldControls strata header.origin.source}
    (carrier : WorldFamilyCarrier header controls headerControls) :
    List (World strata.rules.length) :=
  match carrier with
  | .direct _ => []
  | .canonical packet child _ => packet.originalSite.worlds ++ child.openings

noncomputable def WorldFamilyCarrier.maskDepth
    (carrier : WorldFamilyCarrier header controls headerControls)
    (policy : Name → Nat → Nat) (depth : Nat) : Nat :=
  match carrier with
  | .direct _ => depth
  | .canonical packet child _ => policy packet.ownerName (child.maskDepth policy depth)

section Rebuild
variable {strata : EquationStratification env}
  {header : IndependentFamilyHeader env U registry target name levels}
  {controls : OriginalWorldControls strata sourceEnv}
  {headerControls : OriginalWorldControls strata header.origin.source}
  {typeRealization planRealization : Subst} {demand support : Profile n}
  (certificate : RichCert header.origin.source env U registry target
    (.ref (header.origin.familyHeader header.seedWF).reference) [] typeRealization true support [])
  (typed : demand.HasType support)
  (plan : RichFamilyPlan env U registry target (header.origin.familyHeader header.seedWF).reference
    name header.seed header.signature .nil planRealization [] demand [])

noncomputable def WorldFamilyCarrier.rebuild
    (certificate : RichCert header.origin.source env U registry target
      (.ref (header.origin.familyHeader header.seedWF).reference) [] typeRealization true support [])
    (typed : demand.HasType support)
    (plan : RichFamilyPlan env U registry target (header.origin.familyHeader header.seedWF).reference
      name header.seed header.signature .nil planRealization [] demand [])
    {sourceEnv : VEnv} {controls : OriginalWorldControls strata sourceEnv}
    {headerControls : OriginalWorldControls strata header.origin.source}
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) :
    RichObs sourceEnv env U registry target caller locals σ demand [] :=
  match sourceEnv, controls, headerControls, carrier, caller with
  | _, _, _, .direct _, caller =>
    .family header.origin header.lookup header.notDefinition header.notNative header.notQuotient
      header.seedWF header.seedLength header.levelsWF header.equivalent header.signature header.typeClosed
      certificate typed plan
  | _, _, _, .canonical packet child _, caller =>
    .canonicalConst packet.origin packet.realization
      (child.rebuild certificate typed plan (.ref packet.site) [] packet.realization)
      (by intro _ _ member; cases member)

theorem WorldFamilyCarrier.rebuild_headDepth
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (policy : Name → Nat → Nat) :
    (carrier.rebuild certificate typed plan caller locals σ).headDepth policy =
      carrier.maskDepth policy (max (plan.headDepth policy) (certificate.headDepth policy)) := by
  induction carrier generalizing source assigned locals σ with
  | direct => rw [rebuild, RichObs.headDepth, maskDepth]
  | canonical packet child charged ih =>
    rw [rebuild, RichObs.headDepth, maskDepth]
    change policy packet.ownerName
      ((child.rebuild certificate typed plan (.ref packet.site) [] packet.realization).headDepth policy) = _
    rw [ih]

noncomputable def WorldFamilyCarrier.rebuildAnnotation
    (certificate : RichCert header.origin.source env U registry target
      (.ref (header.origin.familyHeader header.seedWF).reference) [] typeRealization true support [])
    (typed : demand.HasType support)
    (plan : RichFamilyPlan env U registry target (header.origin.familyHeader header.seedWF).reference
      name header.seed header.signature .nil planRealization [] demand [])
    {sourceEnv : VEnv} {controls : OriginalWorldControls strata sourceEnv}
    {headerControls : OriginalWorldControls strata header.origin.source}
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificateAnnotation : WorldCertProvenance strata certificate)
    (planAnnotation : WorldFamilyPlanProvenance strata plan) :
    WorldObsProvenance strata (carrier.rebuild certificate typed plan caller locals σ) :=
  match sourceEnv, controls, headerControls, carrier, caller with
  | _, _, _, .direct controls, caller =>
    .family header.origin header.lookup header.notDefinition header.notNative header.notQuotient
      header.seedWF header.seedLength header.levelsWF header.equivalent header.signature header.typeClosed
      certificate typed plan certificateAnnotation planAnnotation
      (.empty (controls.atHeader header.origin) (EndpointProvenance.ofLocation .here .nil) typeRealization)
  | _, _, _, .canonical packet child _, caller =>
    .canonicalConst packet.origin packet.realization
      (child.rebuild certificate typed plan (.ref packet.site) [] packet.realization)
      (by intro _ _ member; cases member)
      (child.rebuildAnnotation certificate typed plan (.ref packet.site) [] packet.realization
        certificateAnnotation planAnnotation)
      packet.siteControls (EndpointProvenance.ofLocation .here .nil)

theorem WorldFamilyCarrier.rebuildAnnotation_worlds
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificateAnnotation : WorldCertProvenance strata certificate)
    (planAnnotation : WorldFamilyPlanProvenance strata plan) :
    (carrier.rebuildAnnotation certificate typed plan caller locals σ certificateAnnotation planAnnotation).worlds =
      carrier.openings ++
      (WorldQuerySite.empty (registry := registry) (target := target) headerControls
        (EndpointProvenance.ofLocation (.here (root := (header.origin.familyHeader header.seedWF).reference)) .nil)
        typeRealization).worlds ++ certificateAnnotation.worlds ++ planAnnotation.worlds := by
  induction carrier generalizing source assigned locals σ with
  | direct => rfl
  | canonical packet child charged ih =>
    change packet.originalSite.worlds ++
      (child.rebuildAnnotation certificate typed plan (.ref packet.site) [] packet.realization
        certificateAnnotation planAnnotation).worlds = _
    rw [ih]
    simp only [openings, List.append_assoc]

theorem WorldFamilyCarrier.rebuild_within
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificateWithin : WithinAbove headerControls.cutoff headerControls.fuel
      (fun control => certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (planWithin : WithinAbove headerControls.cutoff headerControls.fuel
      (fun control => plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WithinAbove controls.cutoff controls.fuel
      (fun control => (carrier.rebuild certificate typed plan caller locals σ).headDepth
        (stratifiedHeadPolicy (strata.headOrdinal registry) control)) := by
  induction carrier generalizing source assigned locals σ with
  | direct controls =>
    intro control active
    change (WorldFamilyCarrier.rebuild certificate typed plan (.direct controls)
      caller locals σ).headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control
    rw [WorldFamilyCarrier.rebuild_headDepth certificate typed plan (.direct controls)
      caller locals σ (stratifiedHeadPolicy (strata.headOrdinal registry) control)]
    change max (plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
      (certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) ≤ _
    exact Nat.max_le.mpr ⟨planWithin control active, certificateWithin control active⟩
  | canonical packet child charged ih =>
    have childWithin := ih (.ref packet.site) [] packet.realization certificateWithin planWithin
    have bounded := EquationStratifiedFuel.rebuild packet.owner.selected.ordinal_pos charged childWithin
    intro control active
    simpa only [rebuild, RichObs.headDepth, CanonicalConstSitePacket.origin,
      stratifiedHeadPolicy, packet.owner.headOrdinal_eq, EquationStratifiedFuel.headDepth] using bounded control active

/-- Every output observer and its annotation are computed from the same
updated payload. Header fuel is used under its original canonical masks. -/
noncomputable def WorldFamilyCarrier.rebuildControlled
    (carrier : WorldFamilyCarrier header controls headerControls)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificateReady : ControlledStoredQuery headerControls frontier (.certificate certificate))
    (planAnnotation : WorldFamilyPlanProvenance strata plan)
    (planWithin : WithinAbove headerControls.cutoff headerControls.fuel
      (fun control => plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (planSponsored : Sponsored frontier planAnnotation.worlds)
    (openingsSponsored : Sponsored frontier carrier.openings)
    (headerSponsored : Sponsored frontier
      (WorldQuerySite.empty (registry := registry) (target := target) headerControls
        (EndpointProvenance.ofLocation (.here (root := (header.origin.familyHeader header.seedWF).reference)) .nil)
        typeRealization).worlds) :
    ControlledStoredQuery controls frontier
      (.observation (carrier.rebuild certificate typed plan caller locals σ)) where
  annotation := carrier.rebuildAnnotation certificate typed plan caller locals σ
    certificateReady.annotation planAnnotation
  within := carrier.rebuild_within certificate typed plan caller locals σ certificateReady.within planWithin
  sponsored := by
    change Sponsored frontier (carrier.rebuildAnnotation certificate typed plan caller locals σ
      certificateReady.annotation planAnnotation).worlds
    rw [carrier.rebuildAnnotation_worlds certificate typed plan caller locals σ
      certificateReady.annotation planAnnotation]
    exact ((openingsSponsored.merge headerSponsored).merge certificateReady.sponsored).merge planSponsored

end Rebuild
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
