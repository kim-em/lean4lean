import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyPlanLegacy
import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyFamilyConstantOrigin

/-! The exact low family payload is selected jointly with its annotations.
It can then be attached to the genuine earlier header of an actual constant
original, without borrowing the legacy annotation's ambient header source. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure WorldFamilyLegacyLeaf (strata : EquationStratification env)
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) where
  info : VConstant
  lookup : env.constants name = some info
  notDefinition : registry.definitions name = none
  notNative : registry.natives name = none
  notQuotient : name ≠ ``Quot.lift
  seed : List VLevel
  seedWF : ∀ level ∈ seed, level.WF U
  seedLength : seed.length = info.uvars
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seed levels
  signature : ConstantTelescope (info.type.instL seed)
  typeClosed : info.type.Closed
  rank : Nat
  atom : Atom rank
  realization : Subst
  support : Profile rank
  certificate : SortableCert env U registry target [] realization
    (info.type.instL seed) true support []
  typed : (Profile.singleton atom).HasType support
  plan : SortableFamilyPlan env U registry target name seed signature [] (.singleton atom) []
  certificateAnnotation : WorldSortableCertProvenance strata certificate
  planAnnotation : WorldSortableFamilyPlanProvenance strata plan
  origin : ConstantHeaderOrigin env name info
  oldSite : WorldQuerySite (registry := registry) (target := target) strata
    (.ref (origin.familyHeader seedWF).reference) [] realization

noncomputable def WorldFamilyLegacyLeaf.worlds
    (leaf : WorldFamilyLegacyLeaf strata U registry target name levels) :
    List (World strata.rules.length) := leaf.certificateAnnotation.worlds ++ leaf.planAnnotation.worlds
noncomputable def WorldFamilyLegacyLeaf.headDepth
    (leaf : WorldFamilyLegacyLeaf strata U registry target name levels)
    (policy : Name → Nat → Nat) : Nat :=
  max (leaf.plan.headDepth policy) (leaf.certificate.headDepth policy)

theorem WorldLegacyObsProvenance.familyLeaf
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {demand : Profile n} {atom : Atom n}
    {query : Obs env U registry target locals σ (.const name levels) demand footprint}
    (annotation : WorldLegacyObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : WorldFamilyLegacyLeaf strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) ∧
      List.Subset seed.worlds annotation.worlds ∧
      ∀ policy, seed.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      certificate typed tree certificateAnn treeAnn origin site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    obtain ⟨convertedAnn, worlds, depth⟩ := treeAnn.toSortable
    let seed : WorldFamilyLegacyLeaf strata U registry target name levels := {
      info := _, lookup := lookup, notDefinition := noDefinition, notNative := noNative,
      notQuotient := noQuotient, seed := _, seedWF := seedWF, seedLength := seedLength,
      levelsWF := levelsWF, equivalent := equivalent, signature := signature, typeClosed := typeClosed,
      rank := _, atom := atom, realization := _, support := _,
      certificate := .ofCode certificate certificate.formed, typed := typed, plan := tree.toSortable,
      certificateAnnotation := .ofCode certificate certificate.formed certificateAnn,
      planAnnotation := convertedAnn, origin := origin, oldSite := site }
    refine ⟨seed, ⟨.refl⟩, ?_, ?_⟩
    · intro w present
      change w ∈ certificateAnn.worlds ++ convertedAnn.worlds at present
      rw [worlds] at present
      exact List.mem_append_right site.worlds present
    · intro policy
      change max (tree.toSortable.headDepth policy) ((SortableCert.ofCode certificate certificate.formed).headDepth policy) ≤ _
      rw [depth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.le_refl _
  | _, _, _, _, .delta lookup .. => rw [notDefinition] at lookup; contradiction
  | _, _, _, _, .native lookup .. => rw [notNative] at lookup; contradiction
  | _, _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ tree .. =>
    exact (ConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, _, .empty => cases member
  | _, _, _, _, .union left right leftAnn rightAnn =>
    rcases List.mem_append.mp member with selected | selected
    · obtain ⟨seed, path, worlds, depth⟩ := leftAnn.familyLeaf
        henv hscoped formed notDefinition notNative selected ends
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_left _ (worlds present)
      · intro policy
        rw [Obs.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_left _ _)
    · obtain ⟨seed, path, worlds, depth⟩ := rightAnn.familyLeaf
        henv hscoped formed notDefinition notNative selected ends
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_right _ (worlds present)
      · intro policy
        rw [Obs.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
  | _, _, _, _, .pad source child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative selected ends
    refine ⟨seed, ⟨.pad path⟩, worlds, ?_⟩
    intro policy; rw [Obs.headDepth]; exact depth policy
  | _, _, _, _, .unpad source child =>
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_map_of_mem member) ends
    refine ⟨seed, ⟨.unpad path⟩, worlds, ?_⟩
    intro policy; rw [Obs.headDepth]; exact depth policy
  | _, _, _, _, .view source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
    refine ⟨seed, ⟨.action path (.view change)⟩, worlds, ?_⟩
    intro policy; rw [Obs.headDepth]; exact depth policy
  | _, _, _, _, .rowShift source child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _) ends
    refine ⟨seed, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, worlds, ?_⟩
    intro policy; rw [Obs.headDepth]; exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega


theorem WorldSortableObsProvenance.familyLeaf
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {demand : Profile n} {atom : Atom n}
    {query : SortableObs env U registry target locals σ (.const name levels) demand footprint}
    (annotation : WorldSortableObsProvenance strata query)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ seed : WorldFamilyLegacyLeaf strata U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) ∧
      List.Subset seed.worlds annotation.worlds ∧
      ∀ policy, seed.headDepth policy ≤ query.headDepth policy := by
  match n, demand, footprint, query, annotation with
  | _, _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed
      certificate typed tree certificateAnn treeAnn origin site =>
    have singleton := tree.singleton_of_mem member
    cases singleton
    let seed : WorldFamilyLegacyLeaf strata U registry target name levels := {
      info := _, lookup := lookup, notDefinition := noDefinition, notNative := noNative,
      notQuotient := noQuotient, seed := _, seedWF := seedWF, seedLength := seedLength,
      levelsWF := levelsWF, equivalent := equivalent, signature := signature, typeClosed := typeClosed,
      rank := _, atom := atom, realization := _, support := _,
      certificate := certificate, typed := typed, plan := tree,
      certificateAnnotation := certificateAnn, planAnnotation := treeAnn, origin := origin, oldSite := site }
    refine ⟨seed, ⟨.refl⟩, ?_, ?_⟩
    · intro w present
      exact List.mem_append_right site.worlds present
    · intro policy
      change max (tree.headDepth policy) (certificate.headDepth policy) ≤ _
      rw [SortableObs.headDepth]
      exact Nat.le_refl _
  | _, _, _, _, .legacy source child =>
    obtain ⟨seed, path, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative member ends
    refine ⟨seed, path, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
  | _, _, _, _, .code flag certificate child => exact (nonsortable _ (certificate.formed.singleton_of_mem member)).elim
  | _, _, _, _, .union left right leftAnn rightAnn =>
    rcases List.mem_append.mp member with selected | selected
    · obtain ⟨seed, path, worlds, depth⟩ := leftAnn.familyLeaf
        henv hscoped formed notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_left _ (worlds present)
      · intro policy
        rw [SortableObs.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_left _ _)
    · obtain ⟨seed, path, worlds, depth⟩ := rightAnn.familyLeaf
        henv hscoped formed notDefinition notNative selected ends nonsortable
      refine ⟨seed, path, ?_, ?_⟩
      · intro w present; exact List.mem_append_right _ (worlds present)
      · intro policy
        rw [SortableObs.headDepth]
        exact Nat.le_trans (depth policy) (Nat.le_max_right _ _)
  | _, _, _, _, .pad source child =>
    obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative selected ends
      (fun flag sorted => nonsortable flag sorted.pad_sort)
    refine ⟨seed, ⟨.pad path⟩, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
  | _, _, _, _, .unpad source child =>
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_map_of_mem member) ends
      (fun flag sorted => nonsortable flag (by
        have high : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using sorted
        simpa only [Profile.down_sort] using high.pad_inv))
    refine ⟨seed, ⟨.unpad path⟩, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
  | _, _, _, _, .view source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
      (fun flag sorted => nonsortable flag ((AtomAction.view change).sortable sorted))
    refine ⟨seed, ⟨.action path (.view change)⟩, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
  | _, _, _, _, .action source change child =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
      (fun flag sorted => nonsortable flag (change.sortable sorted))
    refine ⟨seed, ⟨.action path change⟩, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
  | _, _, _, _, .rowShift source child =>
    cases List.mem_singleton.mp member
    have impossible : ∀ {m : Nat} (k : Key m) (a : Atom m) flag,
        ¬ (Profile.fn k a).HasType (.sort flag) := by
      intro m k a flag typed
      obtain ⟨cover, present, bad⟩ := typed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp present
      contradiction
    obtain ⟨seed, ⟨path⟩, worlds, depth⟩ := child.familyLeaf
      henv hscoped formed notDefinition notNative (List.mem_singleton_self _) ends
      (impossible _ _)
    refine ⟨seed, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩, worlds, ?_⟩
    intro policy; rw [SortableObs.headDepth]; exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
