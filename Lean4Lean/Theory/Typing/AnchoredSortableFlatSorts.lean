import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredFlatSortsGrades

/-! Reconstruct flattened universe covers from finite source certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Select an existing sort cover and remove only its explicit padding. -/
noncomputable def SortableCert.sortFlag {profile : Profile n}
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint)
    (member : flag ∈ profile.sortFlags) :
    SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := n) flag) footprint := by
  induction n with
  | zero => exact .select certificate member
  | succ n ih => exact (ih certificate.down member).sortPad

noncomputable def SortableCert.sortAt {n m : Nat}
    (certificate : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := n) flag) footprint) :
    SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := m) flag) footprint := by
  have base : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := 0) flag) footprint := by
    induction n with
    | zero => exact certificate
    | succ n ih => exact ih (by simpa only [Profile.down_sort] using certificate.down)
  induction m with
  | zero => exact base
  | succ m ih => exact ih.sortPad

/-- Every retained cover is selected from the actual source certificate.
Duplicating its finite footprint is harmless and made explicit in the result. -/
theorem SortableCert.flatSorts {profile : Profile n}
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint)
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      Nonempty (SortableCert env U registry Γ locals σ expression relevant
        profile.flatSorts nextFootprint) ∧ nextFootprint.Available available := by
  have build (flags : List Bool) (included : List.Subset flags profile.sortFlags) :
      ∃ nextFootprint,
        Nonempty (SortableCert env U registry Γ locals σ expression relevant
          (flags.flatMap fun flag => Profile.sort (n := n) flag) nextFootprint) ∧
        nextFootprint.Available available := by
    induction flags with
    | nil =>
      exact ⟨[], ⟨.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant))⟩,
        fun _ _ h => nomatch h⟩
    | cons flag rest ih =>
      obtain ⟨tailFootprint, ⟨tail⟩, tailResources⟩ :=
        ih (fun _ h => included (List.mem_cons_of_mem _ h))
      refine ⟨footprint ++ tailFootprint,
        ⟨.union (certificate.sortFlag (included List.mem_cons_self)) tail⟩, ?_⟩
      intro i need member
      exact (List.mem_append.mp member).elim (resources i need) (tailResources i need)
  exact build profile.sortFlags (fun _ h => h)

theorem SortableCert.flatSortsAt {profile : Profile n}
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint)
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      Nonempty (SortableCert env U registry Γ locals σ expression relevant
        (profile.flatSortsAt m) nextFootprint) ∧ nextFootprint.Available available := by
  have build (flags : List Bool) (included : List.Subset flags profile.sortFlags) :
      ∃ nextFootprint,
        Nonempty (SortableCert env U registry Γ locals σ expression relevant
          (Profile.sortsAt m flags) nextFootprint) ∧
        nextFootprint.Available available := by
    induction flags with
    | nil =>
      exact ⟨[], ⟨.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant))⟩,
        fun _ _ h => nomatch h⟩
    | cons flag rest ih =>
      obtain ⟨tailFootprint, ⟨tail⟩, tailResources⟩ :=
        ih (fun _ h => included (List.mem_cons_of_mem _ h))
      refine ⟨footprint ++ tailFootprint,
        ⟨.union (certificate.sortFlag (included List.mem_cons_self)).sortAt tail⟩, ?_⟩
      intro i need member
      exact (List.mem_append.mp member).elim (resources i need) (tailResources i need)
  exact build profile.sortFlags (fun _ h => h)

end Lean4Lean.AnchoredSource.Adapted
