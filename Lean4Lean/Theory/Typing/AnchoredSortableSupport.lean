import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredSourcePruning

/-! Recover an actual universe-code cover from a retained assigned-type
certificate. The source expression is never identified with a literal sort. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCert.sortCover
    {atom : Atom n} {support : Profile n}
    (certificate : SortableCert env U registry Γ locals σ assigned true support footprint)
    (sortable : (Profile.singleton atom).HasType (.sort relevant))
    (typed : (Profile.singleton atom).HasType support)
    (code : TypeRelated env U registry Γ left right support) (henv : env.Ordered) :
    ∃ flag, Nonempty (SortableCert env U registry Γ locals σ assigned true
      (Profile.sort (n := n) flag) footprint) ∧
      (Profile.singleton atom).HasType (.sort flag) ∧
      TypeRelated env U registry Γ left right (Profile.sort (n := n) flag) := by
  induction n with
  | zero =>
    obtain ⟨cover, member, equal⟩ := typed atom (List.mem_singleton_self _)
    change cover = true at equal
    subst cover
    exact ⟨true, ⟨.select certificate member⟩, Profile.HasType.sort atom,
      code.singleton member⟩
  | succ n ih =>
    cases atom with
    | pad lower =>
      change (Profile.singleton lower).pad.HasType _ at sortable typed
      have smallSortable : (Profile.singleton lower).HasType (.sort relevant) := by
        simpa only [Profile.down_sort] using sortable.pad_inv
      obtain ⟨flag, ⟨selected⟩, lowerTyped, lowerCode⟩ :=
        ih certificate.down smallSortable typed.pad_inv (code.down henv)
      exact ⟨flag, ⟨selected.sortPad⟩, lowerTyped.pad_sort, lowerCode.sortPad⟩
    | fn | ctor | record =>
      obtain ⟨cover, member, impossible⟩ := sortable.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    | sort | pi | family =>
      obtain ⟨cover, member, covered⟩ := typed.2.2 _ (List.mem_singleton_self _)
      cases cover with
      | sort flag =>
        exact ⟨flag, ⟨.select certificate member⟩,
          ⟨typed.wf_value, Profile.WF.sort (n := n + 1) flag, fun actual h => by
            cases List.mem_singleton.mp h
            exact ⟨.sort flag, List.mem_singleton_self _, covered⟩⟩,
          code.singleton member⟩
      | fn | pi | pad | family | ctor | record => contradiction

/-- A support map acts separately on each actual outer atom. Each output
is typed using that atom's retained universe cover, with all resources kept. -/
theorem SortableCert.mapSupport
    {value support : Profile n} {a b : Atom n}
    (certificate : SortableCert env U registry Γ locals σ assigned true support footprint)
    (view : AtomView env U registry Γ a b)
    (sortable : value.HasType (.sort relevant)) (typed : value.HasType support)
    (code : TypeRelated env U registry Γ left right support) (henv : env.Ordered)
    (resources : footprint.Available available) :
    ∃ nextSupport nextFootprint,
      Nonempty (SortableCert env U registry Γ locals σ assigned true nextSupport nextFootprint) ∧
      nextFootprint.Available available ∧ (view.mapType value).HasType nextSupport ∧
      TypeRelated env U registry Γ left right nextSupport := by
  induction value with
  | nil =>
    refine ⟨.empty, [], ⟨.seed .empty (Profile.HasType.empty (Profile.WF.sort true))⟩,
      (fun _ _ h => nomatch h), ?_, ?_⟩
    · rw [view.mapType_lists.1]
      exact Profile.HasType.empty Profile.WF.empty
    · cases n <;> exact fun _ _ _ _ h => nomatch h
  | cons atom rest ih =>
    obtain ⟨flag, ⟨selected⟩, atomTyped, atomCode⟩ := certificate.sortCover
      (sortable.singleton_of_mem List.mem_cons_self)
      (typed.singleton_of_mem List.mem_cons_self) code henv
    obtain ⟨otherSupport, otherFootprint, ⟨other⟩, otherResources, otherTyped, otherCode⟩ :=
      ih (ProfileView.typed_tail sortable) (ProfileView.typed_tail typed)
    refine ⟨(Profile.sort flag).union otherSupport, footprint ++ otherFootprint,
      ⟨.union selected other⟩, ?_, ?_, ?_⟩
    · intro i need member
      exact (List.mem_append.mp member).elim (resources i need) (otherResources i need)
    · change (view.mapType ((Profile.singleton atom).union rest)).HasType _
      rw [view.mapType_lists.2]
      exact (view.mapType_sort atomTyped).union_types otherTyped
    · apply TypeRelated.of_singletons
      intro actual member
      exact (List.mem_append.mp member).elim
        (fun h => atomCode.singleton h) (fun h => otherCode.singleton h)

end Lean4Lean.AnchoredSource.Adapted
