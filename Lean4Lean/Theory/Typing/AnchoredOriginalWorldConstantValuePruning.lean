import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantRelocation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation
import Lean4Lean.Theory.Typing.AnchoredAtomActionCode
import Lean4Lean.Theory.Typing.AnchoredSortableScope

/-! Select a nonsortable value from a constant query together with its actual
annotation. Only retained children contribute worlds; discarded code recipes
do not acquire an invented closed annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem lowerSort {n N : Nat} (bound : n ≤ N) (flag : Bool) :
    lowerProfile n bound (Profile.sort flag) = Profile.sort flag := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; exact lowerProfile_self _
    · have previous : n ≤ N := by omega
      rw [lowerProfile_step previous, Profile.down_sort]
      exact ih previous

theorem WorldObsProvenance.pruneConstantValueAux
    {n : Nat} {profile : Profile n} {atom : Atom n}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata query)
    (fuel : Nat) (bounded : sizeOf annotation < fuel)
    (selected : atom ∈ profile.atoms)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ
      (.singleton atom) [],
    ∃ next : WorldObsProvenance strata result,
      next.worlds ⊆ annotation.worlds ∧
      ∀ policy, result.headDepth policy ≤ query.headDepth policy := by
  cases annotation with
  | empty => cases selected
  | rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed childAnn controls site =>
    refine ⟨.select (.rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed) selected,
      .select (.rigidFamily origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed childAnn controls site) selected, ?_, ?_⟩
    · intro world member; exact member
    · intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn headerSite =>
    refine ⟨.select (.family origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree) selected,
      .select (.family origin lookup notDefinition notNative notQuotient seedWF seedLength
        levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn headerSite)
        selected, (fun _ member => member), ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | constructor origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn headerSite =>
    refine ⟨.select (.constructor origin lookup notDefinition notNative notQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed certificate typed tree) selected,
      .select (.constructor origin lookup notDefinition notNative notQuotient seedWF seedLength
        levelsWF equivalent signature typeClosed certificate typed tree certificateAnn treeAnn headerSite)
        selected, (fun _ member => member), ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | canonicalDelta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed certificateAnn bodyAnn controls typeSite bodySite =>
    refine ⟨.select (.canonicalDelta (name := name) (levels := levels)
      lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
      certificate typed _) selected,
      .select (.canonicalDelta lookup nameEq registered seedWF seedLength levelsWF equivalent
        bodyClosed typeClosed certificate typed certificateAnn bodyAnn controls typeSite bodySite)
        selected, (fun _ member => member), ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | canonicalConst origin realization child resources childAnn controls site =>
    refine ⟨.select (.canonicalConst (name := name) (levels := levels)
      origin realization child resources) selected,
      .select (.canonicalConst origin realization child resources childAnn controls site) selected,
      (fun _ member => member), ?_⟩
    intro policy; simp only [RichObs.headDepth]; exact Nat.le_refl _
  | legacy child childAnn =>
    have empty : footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry member
      obtain ⟨index, need⟩ := entry
      have impossible := child.scoped (show (VExpr.const name levels).Closed from trivial) index need member
      omega
    cases empty
    obtain ⟨moved, movedAnn, worlds, depth⟩ := childAnn.relocateConstant newLocals τ
    refine ⟨.select (.legacy moved) selected, .select (.legacy moved movedAnn) selected, ?_, ?_⟩
    · intro world member
      change world ∈ movedAnn.worlds at member
      change world ∈ childAnn.worlds
      rwa [worlds] at member
    · intro policy
      simp only [RichObs.headDepth, depth]; exact Nat.le_refl _
  | code child =>
    rename_i relevant certificate
    exact (nonsortable relevant (certificate.formed.singleton_of_mem selected)).elim
  | route path child =>
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) selected nonsortable destination newLocals τ
    exact ⟨result, next, worlds, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | union left right =>
    rcases List.mem_append.mp selected with member | member
    · obtain ⟨result, next, worlds, depth⟩ := left.pruneConstantValueAux (fuel - 1)
        (by simp at bounded; omega) member nonsortable destination newLocals τ
      refine ⟨result, next, ?_, fun policy => by
        simpa only [RichObs.headDepth] using Nat.le_trans (depth policy) (Nat.le_max_left _ _)⟩
      intro world member
      exact List.mem_append_left _ (worlds member)
    · obtain ⟨result, next, worlds, depth⟩ := right.pruneConstantValueAux (fuel - 1)
        (by simp at bounded; omega) member nonsortable destination newLocals τ
      refine ⟨result, next, ?_, fun policy => by
        simpa only [RichObs.headDepth] using Nat.le_trans (depth policy) (Nat.le_max_right _ _)⟩
      intro world member
      exact List.mem_append_right _ (worlds member)
  | view child change =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) List.mem_cons_self
      (fun flag formed => nonsortable flag ((AtomAction.view change).sortable formed)) destination newLocals τ
    exact ⟨.view result change, .view next change, worlds,
      fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | action child change =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) List.mem_cons_self
      (fun flag formed => nonsortable flag (change.sortable formed)) destination newLocals τ
    exact ⟨.action result change, .action next change, worlds,
      fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | select child member =>
    cases List.mem_singleton.mp selected
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) member nonsortable destination newLocals τ
    exact ⟨result, next, worlds, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | pad child =>
    obtain ⟨old, member, equal⟩ := List.mem_map.mp selected
    cases equal
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) member
      (fun flag formed => nonsortable flag formed.pad_sort) destination newLocals τ
    exact ⟨.pad result, .pad next, worlds, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | unpad child =>
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) (List.mem_map_of_mem selected)
      (fun flag formed => nonsortable flag (by
        have hp : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using formed
        simpa only [Profile.down_sort] using hp.pad_inv)) destination newLocals τ
    exact ⟨.unpad result, .unpad next, worlds, fun policy => by simpa only [RichObs.headDepth] using depth policy⟩
  | castProfile equal child =>
    have smaller : sizeOf child < fuel - 1 := by
      simp only [WorldObsProvenance.castProfile.sizeOf_spec] at bounded
      omega
    cases equal
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      smaller selected nonsortable destination newLocals τ
    exact ⟨result, next, worlds, depth⟩
  | @lowerRaised low high _ _ _ _ _ _ _ _ _ _ original _ bound observation child =>
    have member : raiseAtom high bound atom ∈ (raiseProfile high bound profile).atoms := by
      have included : (Profile.singleton atom).atoms ⊆ profile.atoms := by
        intro a member
        cases List.mem_singleton.mp member
        exact selected
      have lifted := raiseProfile_subset bound included
      rw [raiseProfile_singleton] at lifted
      exact lifted _ List.mem_cons_self
    obtain ⟨result, next, worlds, depth⟩ := child.pruneConstantValueAux (fuel - 1)
      (by simp at bounded; omega) member
      (fun flag formed => nonsortable flag (by
        have hp : (raiseProfile high bound (.singleton atom)).HasType (.sort flag) := by
          simpa only [raiseProfile_singleton] using formed
        have lowered := Profile.HasType.lower bound hp
        rw [lowerSort] at lowered
        exact lowered)) destination newLocals τ
    have lifted : ∃ result : RichObs sourceEnv env U registry target destination newLocals τ
        (raiseProfile high bound (.singleton atom)) [],
      ∃ next : WorldObsProvenance strata result,
        next.worlds ⊆ child.worlds ∧
        ∀ policy, result.headDepth policy ≤ observation.headDepth policy := by
      rw [raiseProfile_singleton]
      exact ⟨result, next, worlds, depth⟩
    obtain ⟨result, next, worlds, depth⟩ := lifted
    exact ⟨result.lowerRaised, .lowerRaised next, worlds, fun policy => by
      simpa only [RichObs.headDepth_lowerRaised] using depth policy⟩
termination_by fuel
decreasing_by all_goals omega

theorem WorldObsProvenance.pruneConstantValue
    {n : Nat} {profile : Profile n} {atom : Atom n}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata query)
    (selected : atom ∈ profile.atoms)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ (.singleton atom) [],
    ∃ next : WorldObsProvenance strata result,
      next.worlds ⊆ annotation.worlds ∧
      ∀ policy, result.headDepth policy ≤ query.headDepth policy :=
  annotation.pruneConstantValueAux (sizeOf annotation + 1) (Nat.lt_succ_self _)
    selected nonsortable destination newLocals τ

theorem WorldObsProvenance.pruneConstantFunction
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint}
    (annotation : WorldObsProvenance strata query)
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ (Profile.fn key output) [],
    ∃ next : WorldObsProvenance strata result,
      next.worlds ⊆ annotation.worlds ∧
      ∀ policy, result.headDepth policy ≤ query.headDepth policy := by
  apply annotation.pruneConstantValue List.mem_cons_self
  intro flag sorted
  obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ List.mem_cons_self
  cases List.mem_singleton.mp member
  contradiction

/-- The selected query and its control evidence are constructed together. -/
theorem ControlledStoredQuery.pruneConstantFunction
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (destination : EndpointState sourceEnv U nextSource (.const name levels) nextAssigned)
    (newLocals : List Nat) (τ : Subst) :
    ∃ result : RichObs sourceEnv env U registry target destination newLocals τ (Profile.fn key output) [],
    ∃ next : ControlledStoredQuery controls frontier (.observation result),
      next.annotation.worlds ⊆ ready.annotation.worlds ∧
      ∀ policy, result.headDepth policy ≤ query.headDepth policy := by
  obtain ⟨result, next, worlds, depth⟩ := ready.annotation.pruneConstantFunction destination newLocals τ
  refine ⟨result, ⟨next, ?_, ?_⟩, worlds, depth⟩
  · intro control active
    exact Nat.le_trans (depth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (worlds member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
