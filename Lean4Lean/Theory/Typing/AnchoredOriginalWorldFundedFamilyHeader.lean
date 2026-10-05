import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyProgramData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

/-! Exhaustive constant-family selection. A rigid finite program remains an
explicit alternative to the genuine telescope header; canonical wrappers are
retained at their actual source sites in either case. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private GeneralOutputPath.lowerRaised from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem raisedFamilyConditions {atom : Atom n} (bound : n ≤ N)
    (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    FamilyEndDemand (raiseAtom N bound atom) ∧
      (∀ flag, ¬ (Profile.singleton (raiseAtom N bound atom)).HasType (.sort flag)) := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact ⟨ends, nonsortable⟩
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n; simpa only [raiseAtom_self] using And.intro ends nonsortable
    · have previous : n ≤ N := by omega
      rw [raiseAtom_step previous]
      obtain ⟨ends, nonsortable⟩ := ih previous
      refine ⟨ends, ?_⟩
      intro flag sorted
      apply nonsortable flag
      have high : (Profile.singleton (raiseAtom N previous atom)).pad.HasType (.sort flag) := by
        simpa only [Profile.pad_singleton] using sorted
      simpa only [Profile.down_sort] using high.pad_inv

/-- Operational selection recomputes canonical child controls and the actual
source header. The inherited frontier pays only retained payload children;
every newly attached top header is proved strictly below the actual caller. -/
theorem WorldObsProvenance.fundedFamilyProgram
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (caller : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n} {atom : Atom n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.worlds) :
    ∃ selected : WorldFamilyProgramAt controls U registry target name levels frontier
        (originalCallWorld controls phase caller captured),
      Nonempty (GeneralOutputPath env U registry target selected.atom atom) := by
  match n, demand, footprint, assigned, node, query, annotation with
  | _, _, _, _, _, _, .family origin lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    let header : IndependentFamilyHeader env U registry target name levels := {
      registrationEnv := sourceEnv, ordered := controls.ordered, below := below,
      info := _, origin := origin, lookup := lookup,
      notDefinition := noDefinition, notNative := noNative, notQuotient := noQuotient,
      seed := _, seedWF := seedWF, seedLength := seedLength,
      levelsWF := levelsWF, equivalent := equivalent, signature := signature, typeClosed := typeClosed,
      rank := _, atom := atom, typeRealization := _, typeSupport := _,
      typeCertificate := certificate, typed := typed, planRealization := _, plan := tree }
    let result : WorldFundedFamilyHeaderAt controls U registry target name levels frontier
        (originalCallWorld controls phase caller captured) := {
      header := header, controls := controls.atHeader origin,
      certificate := {
        annotation := certificateAnn
        within := by
          intro control active
          have bounded := within control active
          simp only [RichObs.headDepth] at bounded
          exact Nat.le_trans (Nat.le_max_right _ _) bounded
        sponsored := fun world present =>
          sponsored world (List.mem_append_left _ (List.mem_append_right _ present)) }
      plan := treeAnn
      planWithin := by
        intro control active
        have bounded := within control active
        simp only [RichObs.headDepth] at bounded
        exact Nat.le_trans (Nat.le_max_left _ _) bounded
      planSponsored := fun world present => sponsored world (List.mem_append_right _ present)
      closedBelow := fun {_ _} node childPhase => originalClosedHeader_below controls origin node caller captured childPhase phase
      headerBelow := originalClosedHeader_below controls origin _ caller captured .fundamental phase
      carrier := WorldFamilyCarrier.direct (header := header) controls
      openingsBelow := by intro world member; exact nomatch member }
    exact ⟨.telescope result, ⟨.refl⟩⟩
  | _, _, _, _, currentNode, _, .rigidFamily (frozenLevels := frozenLevels)
      origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq
      typeClosed plan certificate ready typed child storedControls provenance =>
    cases List.mem_singleton.mp member
    let input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan _ := {
      info := _, origin := origin, lookup := lookup, inert := inert,
      seed := _, seedWF := seedWF, seedLength := seedLength,
      frozenWF := frozenWF, levelsWF := levelsWF, seedFrozen := seedFrozen,
      frozenLevelsEq := frozenLevelsEq, typeClosed := typeClosed,
      realization := _, certificate := certificate, ready := ready, typed := typed }
    let leaf : WorldRigidFamilyLeaf strata U registry target name levels frontier := {
      sourceEnv := sourceEnv, source := source, assigned := _, node := currentNode,
      locals := locals, substitution := σ, frozenLevels := frozenLevels,
      rank := _, plan := plan, support := _, input := input, controls := controls,
      controlled := {
        annotation := .rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF
          seedFrozen frozenLevelsEq typeClosed plan certificate ready typed child storedControls provenance
        within := within
        sponsored := sponsored } }
    exact ⟨.rigid (.literal leaf), ⟨.refl⟩⟩
  | _, _, _, _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ _ tree .. =>
    exact (RichConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, _, _, _, .canonicalDelta lookup .. => rw [notDefinition] at lookup; contradiction
  | _, _, _, _, _, _, .canonicalConst origin realization child resources childAnn storedControls provenance =>
    let packet := CanonicalConstSitePacket.ofOrigin (target := target) origin realization child resources
    have childWithin : EquationStratifiedFuel.WithinAbove packet.siteControls.cutoff packet.siteControls.fuel
        (fun control => child.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) :=
      fun _ _ => Nat.le_refl _
    obtain ⟨selected, path⟩ := childAnn.fundedFamilyProgram henv hscoped formed packet.siteControls
      origin.owner.selected.origin.sourceBelow (.ref origin.site) .nil .fundamental
      notDefinition notNative member ends nonsortable childWithin
      (fun world present => sponsored world (List.mem_append_right _ present))
    have charged : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel packet.chargeDepth := by
      intro control active
      have bounded := within control active
      simpa only [RichObs.headDepth, packet, CanonicalConstSitePacket.ofOrigin,
        CanonicalConstSitePacket.chargeDepth, RichObs.stratifiedDepth, stratifiedHeadPolicy,
        origin.owner.headOrdinal_eq, EquationStratifiedFuel.headDepth] using bounded
    have opening : WorldBelow strata.rules.length
        (originalCallWorld packet.siteControls .fundamental (.ref origin.site) .nil)
        (originalCallWorld controls phase caller captured) := by
      exact packet.originalSite_below controls.cutoff controls.cutoffBound controls.fuel
        controls.ordered.constantCount
        (richSchedule phase (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
        captured.worlds charged _ (List.mem_singleton_self _)
    cases selected with
    | telescope selected =>
      let result : WorldFundedFamilyHeaderAt controls U registry target name levels frontier
          (originalCallWorld controls phase caller captured) := {
        toWorldFundedFamilyHeader := selected.toWorldFundedFamilyHeader.retarget opening
        carrier := .canonical packet selected.carrier charged
        openingsBelow := by
          intro world member
          rcases List.mem_append.mp member with here | inherited
          · change world ∈ [originalCallWorld packet.siteControls .fundamental (.ref origin.site) .nil] at here
            cases List.mem_singleton.mp here
            exact opening
          · exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
              EquationControlMeasure.less_trans (selected.openingsBelow world inherited) opening }
      exact ⟨.telescope result, path⟩
    | rigid selected =>
      exact ⟨.rigid (.canonical packet childAnn storedControls provenance selected), path⟩
  | _, _, _, _, currentNode, _, .legacy source child =>
    obtain ⟨leaf, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative member ends nonsortable
    obtain ⟨selected, ⟨start⟩⟩ := leaf.attachFunded controls below currentNode caller captured phase
      (fun control active => by
        have bounded := within control active
        simp only [RichObs.headDepth] at bounded
        exact Nat.le_trans (depth _) bounded)
      (fun world present => sponsored world (worlds present)) path
    exact ⟨.telescope selected, ⟨start⟩⟩
  | _, _, _, _, _, _, .code (certificate := certificate) child =>
    exact (nonsortable _ (certificate.formed.singleton_of_mem member)).elim
  | _, _, _, _, _, _, .empty => cases member
  | _, _, _, _, _, _, .route routePath child =>
    exact child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative member ends nonsortable
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
  | _, _, _, _, _, _, .union left right =>
    rcases List.mem_append.mp member with selected | selected
    · exact left.fundedFamilyProgram henv hscoped formed controls below caller captured phase
        notDefinition notNative selected ends nonsortable
        (fun control active => by
          have bounded := within control active
          simp only [RichObs.headDepth] at bounded
          exact Nat.le_trans (Nat.le_max_left _ _) bounded)
        (fun world present => sponsored world (List.mem_append_left _ present))
    · exact right.fundedFamilyProgram henv hscoped formed controls below caller captured phase
        notDefinition notNative selected ends nonsortable
        (fun control active => by
          have bounded := within control active
          simp only [RichObs.headDepth] at bounded
          exact Nat.le_trans (Nat.le_max_right _ _) bounded)
        (fun world present => sponsored world (List.mem_append_right _ present))
  | _, _, _, _, _, _, .view child change =>
    cases List.mem_singleton.mp member
    obtain ⟨selected, ⟨path⟩⟩ := child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
      (fun flag sorted => nonsortable flag ((AtomAction.view change).sortable sorted))
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
    exact ⟨selected, ⟨.action path (.view change)⟩⟩
  | _, _, _, _, _, _, .action child change =>
    cases List.mem_singleton.mp member
    obtain ⟨selected, ⟨path⟩⟩ := child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
      (fun flag sorted => nonsortable flag (change.sortable sorted))
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
    exact ⟨selected, ⟨.action path change⟩⟩
  | _, _, _, _, _, _, .select child selected =>
    cases List.mem_singleton.mp member
    exact child.fundedFamilyProgram henv hscoped formed controls below caller captured phase notDefinition notNative selected ends nonsortable
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
  | _, _, _, _, _, _, .pad child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected, ⟨path⟩⟩ := child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative selected ends (fun flag sorted => nonsortable flag sorted.pad_sort)
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
    exact ⟨selected, ⟨.pad path⟩⟩
  | _, _, _, _, _, _, .unpad child =>
    obtain ⟨selected, ⟨path⟩⟩ := child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative (List.mem_map_of_mem member) ends
      (fun flag sorted => nonsortable flag (by
        have high : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using sorted
        simpa only [Profile.down_sort] using high.pad_inv))
      (fun control active => by simpa only [RichObs.headDepth] using within control active) sponsored
    exact ⟨selected, ⟨.unpad path⟩⟩
  | _, _, _, _, _, _, .castProfile equal child =>
    have selected := member
    rw [← equal] at selected
    exact child.fundedFamilyProgram henv hscoped formed controls below caller captured phase notDefinition notNative selected ends nonsortable
      (by cases equal; exact within) sponsored
  | _, _, _, _, _, _, .lowerRaised (profile := profile) (N := N) (bound := bound) child =>
    have high : raiseAtom N bound atom ∈ (raiseProfile N bound profile).atoms := by
      have selected : List.Subset (Profile.singleton atom).atoms profile.atoms := by
        intro a present; cases List.mem_singleton.mp present; exact member
      apply raiseProfile_subset bound selected
      simp only [raiseProfile_singleton]
      exact List.mem_singleton_self _
    obtain ⟨highEnds, highNonsortable⟩ := raisedFamilyConditions bound ends nonsortable
    obtain ⟨selected, ⟨path⟩⟩ := child.fundedFamilyProgram henv hscoped formed controls below caller captured phase
      notDefinition notNative high highEnds highNonsortable
      (fun control active => by simpa only [RichObs.headDepth_lowerRaised] using within control active)
      sponsored
    exact ⟨selected, ⟨GeneralOutputPath.lowerRaised bound path⟩⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
