import Lean4Lean.Theory.Typing.AnchoredSortableDepthPruning
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionDepth
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthGrades
import Lean4Lean.Theory.Typing.AnchoredSortableGradedResult

/-! Exact code extraction from a generalized adapted result keeps every
declaration budget. The same reconstructed certificate serves all controls;
source atom selection, normalization, and finite code actions are explicit. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem SortableObs.codeFromGeneral_allDepth
    {raw requested : Profile n}
    (observation : SortableObs env U registry Γ locals σ expression raw footprint)
    (adapter : GeneralProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ nextFootprint,
      ∃ certificate : SortableCert env U registry Γ locals σ expression relevant requested nextFootprint,
      nextFootprint.Atomizes footprint ∧
      ∀ current, certificate.nativeDepth current ≤ observation.nativeDepth current := by
  induction requested with
  | nil =>
    exact ⟨[], .seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)),
      (fun _ _ h => nomatch h), by
        intro current
        simp only [SortableCert.nativeDepth, Obs.nativeDepth]
        exact Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨original, originalMember, ⟨entry⟩⟩ := adapter.origin List.mem_cons_self
    obtain ⟨flag, sourceFormed, ⟨program⟩⟩ :=
      entry.toCodeAtOutput (formed.singleton_of_mem List.mem_cons_self)
    obtain ⟨selected, selectedBound⟩ := observation.atom_allDepth originalMember
    let selectedCode := program.applyCertificate (SortableCert.observe selected.observation sourceFormed)
    have selectedLeaves := (program.atomizes selected.footprint).trans selected.atomizes
    have tailAdapter : GeneralProfileAdapter env U registry Γ raw tail := by
      cases adapter with
      | cons _ _ rest => exact rest
    obtain ⟨tailFootprint, tailCode, tailLeaves, tailBound⟩ :=
      ih tailAdapter (ProfileView.typed_tail formed)
    refine ⟨_, .union selectedCode tailCode, selectedLeaves.append tailLeaves, ?_⟩
    intro current
    simp only [SortableCert.nativeDepth, selectedCode,
      SortableCodeAction.nativeDepth_applyCertificate]
    exact Nat.max_le.mpr ⟨selectedBound current, tailBound current⟩

theorem SortableObs.sortableCert_of_generalAdapter_allDepth
    {raw requested : Profile n}
    (henv : env.Ordered)
    (observation : SortableObs env U registry Γ locals σ expression raw footprint)
    (adapter : GeneralNormalProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ nextFootprint,
      ∃ certificate : SortableCert env U registry Γ locals σ expression relevant requested nextFootprint,
      nextFootprint.Atomizes footprint ∧ nextFootprint.Available available ∧
      ∀ current, certificate.nativeDepth current ≤ observation.nativeDepth current := by
  obtain ⟨normalFootprint, normal, normalization, normalBound⟩ := observation.normalize_allDepth henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  obtain ⟨nextFootprint, certificate, leaves, certificateBound⟩ :=
    normal.codeFromGeneral_allDepth (canonical ▸ adapter) formed
  have retained := leaves.trans normalization
  exact ⟨nextFootprint, certificate, retained,
    retained.available_closed resources closed,
    fun current => Nat.le_trans (certificateBound current) (normalBound current)⟩

theorem SortableGradedResult.code_allDepth
    (henv : env.Ordered) (closed : available.AtomClosed)
    (result : SortableGradedResult env U registry Γ locals σ available expression requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint,
      ∃ certificate : SortableCert env U registry Γ locals σ expression relevant requested footprint,
      footprint.Available available ∧
      ∀ current, certificate.nativeDepth current ≤ result.observation.nativeDepth current := by
  obtain ⟨footprint, certificate, _, resources, bounded⟩ :=
    result.observation.sortableCert_of_generalAdapter_allDepth henv result.adapter
      (Profile.HasType.raise_sort result.bound formed) result.resources closed
  exact ⟨footprint, certificate.lowerRaised result.bound, resources, by
    intro current
    simpa only [SortableCert.nativeDepth_lowerRaised] using bounded current⟩

end Lean4Lean.AnchoredSource.Adapted
