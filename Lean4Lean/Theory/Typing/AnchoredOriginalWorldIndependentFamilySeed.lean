import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyConstant
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyPlanLegacy
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

/-! The retained family header is independent of a nominal constant root.
Its actual header site, child annotations, and nested canonical owners are
selected together from the incoming annotated observation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- A canonical wrapper is retained with its exact positive child and empty
original site. Its name alone would lose the actual opening obligation. -/
structure WorldFamilyCanonicalOwner (strata : EquationStratification env)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) where
  origin : CanonicalConstOrigin env U registry strata name levels
  realization : Subst
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  query : RichObs origin.owner.selected.origin.source env U registry target
    (.ref origin.site) [] realization profile footprint
  resources : footprint.Available (fun _ => [])
  child : WorldObsProvenance strata query
  controls : OriginalWorldControls strata origin.owner.selected.origin.source
  provenance : EndpointProvenance .nil (.ref origin.site)

noncomputable def WorldFamilyCanonicalOwner.site
    (owner : WorldFamilyCanonicalOwner strata U registry target name levels) :
    WorldQuerySite (registry := registry) (target := target) strata
      (.ref owner.origin.site) [] owner.realization :=
  .empty owner.controls owner.provenance owner.realization

structure WorldIndependentFamilySeed (strata : EquationStratification env)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) where
  header : IndependentFamilyHeader env U registry target name levels
  certificate : WorldCertProvenance strata header.typeCertificate
  plan : WorldFamilyPlanProvenance strata header.plan
  site : WorldQuerySite (registry := registry) (target := target) strata
    (.ref (header.origin.familyHeader header.seedWF).reference) [] header.typeRealization
  owners : List (WorldFamilyCanonicalOwner strata U registry target name levels)

noncomputable def WorldIndependentFamilySeed.worlds
    (seed : WorldIndependentFamilySeed strata U registry target name levels) :
    List (World strata.rules.length) :=
  seed.owners.flatMap (fun owner => owner.site.worlds) ++
    (seed.site.worlds ++ seed.certificate.worlds ++ seed.plan.worlds)

noncomputable def WorldIndependentFamilySeed.headDepth
    (seed : WorldIndependentFamilySeed strata U registry target name levels)
    (policy : Name → Nat → Nat) : Nat :=
  seed.owners.foldr (fun owner depth => policy owner.origin.ownerName depth)
    (max (seed.header.plan.headDepth policy) (seed.header.typeCertificate.headDepth policy))

noncomputable def WorldIndependentFamilySeed.under
    (seed : WorldIndependentFamilySeed strata U registry target name levels)
    (owner : WorldFamilyCanonicalOwner strata U registry target name levels) :
    WorldIndependentFamilySeed strata U registry target name levels :=
  { seed with owners := owner :: seed.owners }

theorem WorldIndependentFamilySeed.under_worlds
    (seed : WorldIndependentFamilySeed strata U registry target name levels)
    (owner : WorldFamilyCanonicalOwner strata U registry target name levels) :
    (seed.under owner).worlds = owner.site.worlds ++ seed.worlds := by
  simp only [worlds, under, List.flatMap_cons, List.append_assoc]

theorem WorldIndependentFamilySeed.under_headDepth
    (seed : WorldIndependentFamilySeed strata U registry target name levels)
    (owner : WorldFamilyCanonicalOwner strata U registry target name levels)
    (policy : Name → Nat → Nat) :
    (seed.under owner).headDepth policy = policy owner.origin.ownerName (seed.headDepth policy) := rfl

private theorem sortableFamilySeed
    (henv : env.Ordered)
    (origin : ConstantHeaderOrigin env name info)
    (lookup : env.constants name = some info)
    (noDefinition : registry.definitions name = none) (noNative : registry.natives name = none)
    (noQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels)) (typeClosed : info.type.Closed)
    {support : Profile n} {atom : Atom n}
    (certificate : SortableCert env U registry target [] typeRealization
      (info.type.instL seedLevels) true support [])
    (typed : (Profile.singleton atom).HasType support)
    (tree : SortableFamilyPlan env U registry target name seedLevels signature [] (.singleton atom) [])
    (certificateAnn : WorldSortableCertProvenance strata certificate)
    (treeAnn : WorldSortableFamilyPlanProvenance strata tree)
    (site : WorldQuerySite (registry := registry) (target := target) strata
      (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
    ∃ result : WorldIndependentFamilySeed strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target result.header.atom atom) ∧
      result.worlds = site.worlds ++ certificateAnn.worlds ++ treeAnn.worlds ∧
      ∀ policy, result.headDepth policy = max (tree.headDepth policy) (certificate.headDepth policy) := by
  obtain ⟨plan, planAnn, worlds, depth⟩ := treeAnn.atOriginalHeader
    (header := (origin.familyHeader seedWF).reference)
  let header : IndependentFamilyHeader env U registry target name levels := {
    registrationEnv := env, ordered := henv, below := VEnv.LE.rfl,
    info := info, origin := origin, lookup := lookup,
    notDefinition := noDefinition, notNative := noNative, notQuotient := noQuotient,
    seed := seedLevels, seedWF := seedWF, seedLength := seedLength,
    levelsWF := levelsWF, equivalent := equivalent, signature := signature, typeClosed := typeClosed,
    rank := n, atom := atom, typeRealization := typeRealization, typeSupport := support,
    typeCertificate := .legacy certificate, typed := typed,
    planRealization := nativeCaptureSubst [], plan := plan }
  let result : WorldIndependentFamilySeed strata U registry target name levels :=
    ⟨header, .legacy certificate certificateAnn, planAnn, site, []⟩
  refine ⟨result, ⟨.refl⟩, ?_, ?_⟩
  · change site.worlds ++ certificateAnn.worlds ++ planAnn.worlds = _
    rw [worlds]
  · intro policy
    change max (plan.headDepth policy) ((RichCert.legacy certificate).headDepth policy) = _
    rw [depth, RichCert.headDepth]

theorem WorldLegacyObsProvenance.independentFamilyValue
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {demand : Profile n} {atom : Atom n}
    {query : Obs env U registry target locals σ (.const name levels) demand footprint}
    (annotation : WorldLegacyObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : WorldIndependentFamilySeed strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.header.atom atom) ∧
      List.Subset seed.worlds annotation.worlds ∧
      ∀ policy, (∀ name a b, a ≤ b → policy name a ≤ policy name b) → seed.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      certificate typed tree certificateAnn treeAnn origin site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    obtain ⟨convertedAnn, worlds, depth⟩ := treeAnn.toSortable
    obtain ⟨seed, path, seedWorlds, seedDepth⟩ := sortableFamilySeed henv origin lookup
      noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      (.ofCode certificate certificate.formed) typed tree.toSortable
      (.ofCode certificate certificate.formed certificateAnn) convertedAnn site
    refine ⟨seed, path, ?_, ?_⟩
    · intro w present
      rw [seedWorlds] at present
      change w ∈ site.worlds ++ certificateAnn.worlds ++ treeAnn.worlds
      change w ∈ site.worlds ++ certificateAnn.worlds ++ convertedAnn.worlds at present
      rw [worlds] at present
      exact present
    · intro policy _
      rw [seedDepth, depth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.le_refl _
  | _, _, _, _, .delta lookup .. => rw [notDefinition] at lookup; contradiction
  | _, _, _, _, .native lookup .. => rw [notNative] at lookup; contradiction
  | _, _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ tree .. =>
    exact (ConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, _, .empty => cases member
  | _, _, _, _, .union left right leftAnn rightAnn =>
    rcases List.mem_append.mp member with selected | selected
    · obtain ⟨seed, path, worlds, depth⟩ := leftAnn.independentFamilyValue
        henv hscoped formed notDefinition notNative selected ends
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_left _ (worlds present)
      · intro policy mono
        rw [Obs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_left _ _)
    · obtain ⟨seed, path, worlds, depth⟩ := rightAnn.independentFamilyValue
        henv hscoped formed notDefinition notNative selected ends
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_right _ (worlds present)
      · intro policy mono
        rw [Obs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_right _ _)
  | _, _, _, _, .pad source child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative selected ends
    refine ⟨seed, ⟨.pad path⟩, worlds, ?_⟩
    intro policy mono; rw [Obs.headDepth]; exact depth policy mono
  | _, _, _, _, .unpad source child =>
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_map_of_mem member) ends
    refine ⟨seed, ⟨.unpad path⟩, worlds, ?_⟩
    intro policy mono; rw [Obs.headDepth]; exact depth policy mono
  | _, _, _, _, .view source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
    refine ⟨seed, ⟨.action path (.view change)⟩, worlds, ?_⟩
    intro policy mono; rw [Obs.headDepth]; exact depth policy mono
  | _, _, _, _, .rowShift source child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _) ends
    refine ⟨seed, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, worlds, ?_⟩
    intro policy mono; rw [Obs.headDepth]; exact depth policy mono
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega


theorem WorldSortableObsProvenance.independentFamilyValue
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {demand : Profile n} {atom : Atom n}
    {query : SortableObs env U registry target locals σ (.const name levels) demand footprint}
    (annotation : WorldSortableObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ seed : WorldIndependentFamilySeed strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.header.atom atom) ∧
      List.Subset seed.worlds annotation.worlds ∧
      ∀ policy, (∀ name a b, a ≤ b → policy name a ≤ policy name b) →
        seed.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      certificate typed tree certificateAnn treeAnn origin site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    obtain ⟨seed, path, worlds, depth⟩ := sortableFamilySeed henv origin lookup
      noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      certificate typed tree certificateAnn treeAnn site
    refine ⟨seed, path, ?_, ?_⟩
    · intro w present; rw [worlds] at present; exact present
    · intro policy _; rw [depth, SortableObs.headDepth]; exact Nat.le_refl _
  | _, _, _, _, .legacy source child =>
    obtain ⟨seed, path, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative member ends
    refine ⟨seed, path, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
  | _, _, _, _, .code flag certificate child => exact (nonsortable _ (certificate.formed.singleton_of_mem member)).elim
  | _, _, _, _, .union left right leftAnn rightAnn =>
    rcases List.mem_append.mp member with selected | selected
    · obtain ⟨seed, path, worlds, depth⟩ := leftAnn.independentFamilyValue
        henv hscoped formed notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_left _ (worlds present)
      · intro policy mono
        rw [SortableObs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_left _ _)
    · obtain ⟨seed, path, worlds, depth⟩ := rightAnn.independentFamilyValue
        henv hscoped formed notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_right _ (worlds present)
      · intro policy mono
        rw [SortableObs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_right _ _)
  | _, _, _, _, .pad source child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative selected ends
      (fun flag sorted => nonsortable flag sorted.pad_sort)
    refine ⟨seed, ⟨.pad path⟩, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
  | _, _, _, _, .unpad source child =>
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_map_of_mem member) ends
      (fun flag sorted => nonsortable flag (by
        have high : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using sorted
        simpa only [Profile.down_sort] using high.pad_inv))
    refine ⟨seed, ⟨.unpad path⟩, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
  | _, _, _, _, .view source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
      (fun flag sorted => nonsortable flag ((AtomAction.view change).sortable sorted))
    refine ⟨seed, ⟨.action path (.view change)⟩, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
  | _, _, _, _, .action source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
      (fun flag sorted => nonsortable flag (change.sortable sorted))
    refine ⟨seed, ⟨.action path change⟩, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
  | _, _, _, _, .rowShift source child =>
    cases List.mem_singleton.mp member
    have impossible : ∀ {m : Nat} (k : Key m) (a : Atom m) flag,
        ¬ (Profile.fn k a).HasType (.sort flag) := by
      intro m k a flag typed
      obtain ⟨cover, present, bad⟩ := typed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp present
      contradiction
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _) ends
      (impossible _ _)
    refine ⟨seed, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, worlds, ?_⟩
    intro policy mono; rw [SortableObs.headDepth]; exact depth policy mono
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

open private GeneralOutputPath.lowerRaised from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins

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

/-- Joint selection from the actual annotation. The owner masks are retained;
this theorem does not assert that an arbitrary stored header site funds a new
opening of its selected plan. -/
theorem WorldObsProvenance.independentFamilyValue
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n} {atom : Atom n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ seed : WorldIndependentFamilySeed strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.header.atom atom) ∧
      List.Subset seed.worlds annotation.worlds ∧
      ∀ policy, (∀ name a b, a ≤ b → policy name a ≤ policy name b) →
        seed.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, assigned, node, query, annotation with
  | _, _, _, _, _, _, .family origin lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    let header : IndependentFamilyHeader env U registry target name levels := {
      registrationEnv := sourceEnv, ordered := ordered, below := below,
      info := _, origin := origin, lookup := lookup,
      notDefinition := noDefinition, notNative := noNative, notQuotient := noQuotient,
      seed := _, seedWF := seedWF, seedLength := seedLength,
      levelsWF := levelsWF, equivalent := equivalent, signature := signature, typeClosed := typeClosed,
      rank := _, atom := atom, typeRealization := _, typeSupport := _,
      typeCertificate := certificate, typed := typed, planRealization := _, plan := tree }
    let seed : WorldIndependentFamilySeed strata U registry target name levels :=
      ⟨header, certificateAnn, treeAnn, site, []⟩
    refine ⟨seed, ⟨.refl⟩, fun _ present => present, ?_⟩
    intro policy _
    change max (tree.headDepth policy) (certificate.headDepth policy) ≤ _
    rw [RichObs.headDepth]
    exact Nat.le_refl _
  | _, _, _, _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ _ tree .. =>
    exact (RichConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, _, _, _, .canonicalDelta lookup .. => rw [notDefinition] at lookup; contradiction
  | _, _, _, _, _, _, .canonicalConst origin realization child resources childAnn controls provenance =>
    obtain ⟨seed, path, worlds, depth⟩ := childAnn.independentFamilyValue henv hscoped formed
      origin.owner.selected.origin.ordered origin.owner.selected.origin.sourceBelow
      notDefinition notNative member ends nonsortable
    let owner : WorldFamilyCanonicalOwner strata U registry target name levels :=
      ⟨origin, realization, _, _, _, child, resources, childAnn, controls, provenance⟩
    refine ⟨seed.under owner, path, ?_, ?_⟩
    · intro w present
      rw [WorldIndependentFamilySeed.under_worlds] at present
      rcases List.mem_append.mp present with present | present
      · exact List.mem_append_left _ present
      · exact List.mem_append_right _ (worlds present)
    · intro policy mono
      rw [WorldIndependentFamilySeed.under_headDepth, RichObs.headDepth]
      exact mono _ _ _ (depth policy mono)
  | _, _, _, _, _, _, .legacy source child =>
    obtain ⟨seed, path, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed notDefinition notNative member ends nonsortable
    refine ⟨seed, path, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .code (certificate := certificate) child => exact (nonsortable _ (certificate.formed.singleton_of_mem member)).elim
  | _, _, _, _, _, _, .empty => cases member
  | _, _, _, _, _, _, .route routePath child =>
    obtain ⟨seed, path, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative member ends nonsortable
    refine ⟨seed, path, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .union left right =>
    rcases List.mem_append.mp member with selected | selected
    · obtain ⟨seed, path, worlds, depth⟩ := left.independentFamilyValue
        henv hscoped formed ordered below notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_left _ (worlds present)
      · intro policy mono; rw [RichObs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_left _ _)
    · obtain ⟨seed, path, worlds, depth⟩ := right.independentFamilyValue
        henv hscoped formed ordered below notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_right _ (worlds present)
      · intro policy mono; rw [RichObs.headDepth]
        exact Nat.le_trans (depth policy mono) (Nat.le_max_right _ _)
  | _, _, _, _, _, _, .view child change =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
      (fun flag sorted => nonsortable flag ((AtomAction.view change).sortable sorted))
    refine ⟨seed, ⟨.action path (.view change)⟩, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .action child change =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
      (fun flag sorted => nonsortable flag (change.sortable sorted))
    refine ⟨seed, ⟨.action path change⟩, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .select child selected =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, path, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative selected ends nonsortable
    refine ⟨seed, path, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .pad child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative selected ends
      (fun flag sorted => nonsortable flag sorted.pad_sort)
    refine ⟨seed, ⟨.pad path⟩, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .unpad child =>
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative (List.mem_map_of_mem member) ends
      (fun flag sorted => nonsortable flag (by
        have high : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using sorted
        simpa only [Profile.down_sort] using high.pad_inv))
    refine ⟨seed, ⟨.unpad path⟩, worlds, ?_⟩
    intro policy mono; rw [RichObs.headDepth]; exact depth policy mono
  | _, _, _, _, _, _, .castProfile equal child =>
    have selected := member
    rw [← equal] at selected
    obtain ⟨seed, path, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative selected ends nonsortable
    refine ⟨seed, path, worlds, ?_⟩
    cases equal
    exact depth
  | _, _, _, _, _, _, .lowerRaised (profile := profile) (N := N) (bound := bound) child =>
    have high : raiseAtom N bound atom ∈ (raiseProfile N bound profile).atoms := by
      have selected : List.Subset (Profile.singleton atom).atoms profile.atoms := by
        intro a present; cases List.mem_singleton.mp present; exact member
      apply raiseProfile_subset bound selected
      simp only [raiseProfile_singleton]
      exact List.mem_singleton_self _
    obtain ⟨highEnds, highNonsortable⟩ := raisedFamilyConditions bound ends nonsortable
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.independentFamilyValue
      henv hscoped formed ordered below notDefinition notNative high highEnds highNonsortable
    refine ⟨seed, ⟨GeneralOutputPath.lowerRaised bound path⟩, worlds, ?_⟩
    intro policy mono
    simpa only [RichObs.headDepth_lowerRaised] using depth policy mono
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
