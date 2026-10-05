import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCarrier
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyLegacyLeaf
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstSharedReturn

/-! Executable family headers use a genuine earlier declaration from the
actual constant original. Legacy payload annotations are copied jointly;
the new top opening is paid by the actual declaration-source decrease. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private constantSourceHeader from Lean4Lean.Theory.Typing.AnchoredOriginalLegacyFamilyConstantOrigin
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure WorldFundedFamilyHeader (strata : EquationStratification env)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel)
    (frontier : List (World strata.rules.length)) (parent : World strata.rules.length) where
  header : IndependentFamilyHeader env U registry target name levels
  controls : OriginalWorldControls strata header.origin.source
  certificate : ControlledStoredQuery controls frontier (.certificate header.typeCertificate)
  plan : WorldFamilyPlanProvenance strata header.plan
  planWithin : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
    (fun control => header.plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
  planSponsored : Sponsored frontier plan.worlds
  closedBelow : ∀ {expression assigned} (node : EndpointState header.origin.source U [] expression assigned)
    (phase : RichPhase), WorldBelow strata.rules.length
      (originalCallWorld controls phase node .nil) parent
  headerBelow : WorldBelow strata.rules.length
    (originalCallWorld controls .fundamental (.ref (header.origin.familyHeader header.seedWF).reference) .nil) parent

noncomputable def WorldFundedFamilyHeader.site
    (selected : WorldFundedFamilyHeader strata U registry target name levels frontier parent) :
    WorldQuerySite (registry := registry) (target := target) strata
      (.ref (selected.header.origin.familyHeader selected.header.seedWF).reference) [] selected.header.typeRealization :=
  .empty selected.controls (EndpointProvenance.ofLocation .here .nil) selected.header.typeRealization

/-- This is the new top site's genuine opening proof, not sponsorship
inferred from the old ambient legacy header annotation. -/
theorem WorldFundedFamilyHeader.siteBelow
    (selected : WorldFundedFamilyHeader strata U registry target name levels frontier parent) :
    ∀ world ∈ selected.site.worlds, WorldBelow strata.rules.length world parent := by
  intro world member
  change world ∈ [originalCallWorld selected.controls .fundamental
    (.ref (selected.header.origin.familyHeader selected.header.seedWF).reference) .nil] at member
  cases List.mem_singleton.mp member
  exact selected.headerBelow

noncomputable def WorldFundedFamilyHeader.retarget
    (selected : WorldFundedFamilyHeader strata U registry target name levels frontier first)
    (below : WorldBelow strata.rules.length first second) :
    WorldFundedFamilyHeader strata U registry target name levels frontier second := by
  refine { selected with closedBelow := ?_, headerBelow := ?_ }
  · intro expression assigned node phase
    exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans (selected.closedBelow node phase) below
  · exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans selected.headerBelow below

/-- The source-indexed carrier is retained by the same selection that
computed and funded the header. Its canonical openings are actual children
of the recorded parent call. -/
structure WorldFundedFamilyHeaderAt {strata : EquationStratification env}
    (callerControls : OriginalWorldControls strata sourceEnv)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel)
    (frontier : List (World strata.rules.length)) (parent : World strata.rules.length)
    extends WorldFundedFamilyHeader strata U registry target name levels frontier parent where
  carrier : WorldFamilyCarrier header callerControls controls
  openingsBelow : ∀ world ∈ carrier.openings, WorldBelow strata.rules.length world parent

/-- The exact old low children are attached at the header selected by the
actual constant proof. No semantic comparison or supplied header answer is
required, and the inherited foreign-query frontier is unchanged. -/
theorem WorldFamilyLegacyLeaf.attachFunded
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    (leaf : WorldFamilyLegacyLeaf strata U registry target name levels)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (original : EndpointState sourceEnv U constantSource (.const name levels) constantAssigned)
    (caller : EndpointState sourceEnv U source callerExpression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => leaf.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier leaf.worlds)
    (path : GeneralOutputPath env U registry target leaf.atom requested) :
    ∃ selected : WorldFundedFamilyHeaderAt controls U registry target name levels frontier
        (originalCallWorld controls phase caller captured),
      Nonempty (GeneralOutputPath env U registry target selected.header.atom requested) := by
  obtain ⟨origin⟩ := constantSourceHeader controls.ordered below original leaf.lookup
  obtain ⟨plan, planAnn, worlds, depth⟩ := leaf.planAnnotation.atOriginalHeader
    (header := (origin.familyHeader leaf.seedWF).reference)
  let header : IndependentFamilyHeader env U registry target name levels := {
    registrationEnv := sourceEnv, ordered := controls.ordered, below := below,
    info := leaf.info, origin := origin, lookup := leaf.lookup,
    notDefinition := leaf.notDefinition, notNative := leaf.notNative, notQuotient := leaf.notQuotient,
    seed := leaf.seed, seedWF := leaf.seedWF, seedLength := leaf.seedLength,
    levelsWF := leaf.levelsWF, equivalent := leaf.equivalent, signature := leaf.signature,
    typeClosed := leaf.typeClosed, rank := leaf.rank, atom := leaf.atom,
    typeRealization := leaf.realization, typeSupport := leaf.support,
    typeCertificate := .legacy leaf.certificate, typed := leaf.typed,
    planRealization := nativeCaptureSubst [], plan := plan }
  let certificate : ControlledStoredQuery (controls.atHeader origin) frontier (.certificate header.typeCertificate) := {
    annotation := .legacy leaf.certificate leaf.certificateAnnotation
    within := by
      intro control active
      have bounded := within control active
      change max _ (leaf.certificate.headDepth _) ≤ _ at bounded
      change (RichCert.legacy leaf.certificate).headDepth _ ≤ _
      rw [RichCert.headDepth]
      exact Nat.le_trans (Nat.le_max_right _ _) bounded
    sponsored := by
      intro world member
      exact sponsored world (List.mem_append_left _ member) }
  let result : WorldFundedFamilyHeaderAt controls U registry target name levels frontier
      (originalCallWorld controls phase caller captured) := {
    header := header, controls := controls.atHeader origin, certificate := certificate, plan := planAnn
    planWithin := by
      intro control active
      change plan.headDepth _ ≤ _
      rw [depth]
      exact Nat.le_trans (Nat.le_max_left _ _) (within control active)
    planSponsored := by
      intro world member
      rw [worlds] at member
      exact sponsored world (List.mem_append_right _ member)
    closedBelow := fun {_ _} node childPhase => originalClosedHeader_below controls origin node caller captured childPhase phase
    headerBelow := originalClosedHeader_below controls origin _ caller captured .fundamental phase
    carrier := WorldFamilyCarrier.direct (header := header) controls
    openingsBelow := by intro world member; exact nomatch member }
  exact ⟨result, ⟨path⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
