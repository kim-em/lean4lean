import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
import Lean4Lean.Theory.Typing.AnchoredSortableFlatSorts

/-! Computed universe support preserves every declaration budget on one
finite source certificate, even when the output query changes grade. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCert.sortFlag_allDepth {profile : Profile n}
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint)
    (member : flag ∈ profile.sortFlags) :
    ∃ output : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := n) flag) footprint,
      ∀ current, output.nativeDepth current = certificate.nativeDepth current := by
  induction n with
  | zero => exact ⟨.select certificate member, fun _ => by simp only [SortableCert.nativeDepth]⟩
  | succ n ih =>
    obtain ⟨output, bound⟩ := ih certificate.down member
    exact ⟨output.sortPad, fun current => by
      simpa only [SortableCert.nativeDepth] using bound current⟩

theorem SortableCert.sortAt_allDepth {n m : Nat}
    (certificate : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := n) flag) footprint) :
    ∃ output : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := m) flag) footprint,
      ∀ current, output.nativeDepth current = certificate.nativeDepth current := by
  have base : ∃ output : SortableCert env U registry Γ locals σ expression relevant
      (Profile.sort (n := 0) flag) footprint,
      ∀ current, output.nativeDepth current = certificate.nativeDepth current := by
    induction n with
    | zero => exact ⟨certificate, fun _ => rfl⟩
    | succ n ih =>
      let lowered : SortableCert env U registry Γ locals σ expression relevant
          (Profile.sort (n := n) flag) footprint :=
        cast (congrArg (fun p : Profile n => SortableCert env U registry Γ locals σ expression relevant p footprint)
          (Profile.down_sort flag)) certificate.down
      obtain ⟨output, bound⟩ := ih lowered
      refine ⟨output, fun current => (bound current).trans ?_⟩
      have step : lowered.nativeDepth current = certificate.down.nativeDepth current :=
        SortableCert.nativeDepth_cast current (Profile.down_sort flag) _ certificate.down
      simpa only [SortableCert.nativeDepth] using step
  obtain ⟨output, bound⟩ := base
  induction m with
  | zero => exact ⟨output, bound⟩
  | succ m ih =>
    obtain ⟨next, bound⟩ := ih
    exact ⟨next.sortPad, fun current => by simpa only [SortableCert.nativeDepth] using bound current⟩

theorem SortableCert.flatSortsAt_allDepth {profile : Profile n}
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint)
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      ∃ output : SortableCert env U registry Γ locals σ expression relevant
        (profile.flatSortsAt m) nextFootprint,
      nextFootprint.Available available ∧
      ∀ current, output.nativeDepth current ≤ certificate.nativeDepth current := by
  have build (flags : List Bool) (included : List.Subset flags profile.sortFlags) :
      ∃ nextFootprint,
        ∃ output : SortableCert env U registry Γ locals σ expression relevant
          (Profile.sortsAt m flags) nextFootprint,
        nextFootprint.Available available ∧
        ∀ current, output.nativeDepth current ≤ certificate.nativeDepth current := by
    induction flags with
    | nil =>
      exact ⟨[], .seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)),
        (fun _ _ h => nomatch h), by
          intro current; simp only [SortableCert.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _⟩
    | cons flag rest ih =>
      obtain ⟨tailFootprint, tail, tailResources, tailBound⟩ :=
        ih (fun _ h => included (List.mem_cons_of_mem _ h))
      obtain ⟨selected, selectedDepth⟩ := certificate.sortFlag_allDepth (included List.mem_cons_self)
      obtain ⟨changed, changedDepth⟩ := selected.sortAt_allDepth (m := m)
      refine ⟨footprint ++ tailFootprint, .union changed tail, ?_, ?_⟩
      · intro i need member
        exact (List.mem_append.mp member).elim (resources i need) (tailResources i need)
      · intro current
        simp only [SortableCert.nativeDepth, changedDepth current, selectedDepth current]
        exact Nat.max_le.mpr ⟨Nat.le_refl _, tailBound current⟩
  exact build profile.sortFlags (fun _ h => h)

end Lean4Lean.AnchoredSource.Adapted
