import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionCertificate
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterComposition
import Lean4Lean.Theory.Typing.AnchoredSortablePruning

/-! A generalized directional adapter reconstructs genuine source code.
The original source atom's relevance is retained through its finite code
program; it need not equal the final requested relevance. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCodeAction.atomizes
    (action : SortableCodeAction env U registry Γ relevant profile next nextProfile)
    (footprint : Footprint) : (action.footprint footprint).Atomizes footprint := by
  induction action generalizing footprint with
  | comp first second firstIH secondIH => exact (secondIH _).trans (firstIH _)
  | union first second firstIH secondIH => exact (firstIH _).append (secondIH _)
  | _ => exact .refl _

private theorem SortableObs.codeFromGeneral
    {raw requested : Profile n}
    (observation : SortableObs env U registry Γ locals σ expression raw footprint)
    (adapter : GeneralProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ nextFootprint,
      Nonempty (SortableCert env U registry Γ locals σ expression relevant requested nextFootprint) ∧
      nextFootprint.Atomizes footprint := by
  induction requested with
  | nil =>
    exact ⟨[], ⟨.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant))⟩,
      fun _ _ h => nomatch h⟩
  | cons head tail ih =>
    obtain ⟨original, originalMember, ⟨entry⟩⟩ := adapter.origin List.mem_cons_self
    obtain ⟨flag, sourceFormed, ⟨program⟩⟩ :=
      entry.toCodeAtOutput (formed.singleton_of_mem List.mem_cons_self)
    obtain ⟨selected⟩ := observation.atom originalMember
    have selectedCode := program.applyCertificate (SortableCert.observe selected.observation sourceFormed)
    have selectedLeaves := (program.atomizes selected.footprint).trans selected.atomizes
    have tailAdapter : GeneralProfileAdapter env U registry Γ raw tail := by
      cases adapter with
      | cons _ _ rest => exact rest
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailLeaves⟩ :=
      ih tailAdapter (ProfileView.typed_tail formed)
    exact ⟨_, ⟨.union selectedCode tailCode⟩, selectedLeaves.append tailLeaves⟩

theorem SortableObs.sortableCert_of_generalAdapter
    {raw requested : Profile n}
    (henv : env.Ordered)
    (observation : SortableObs env U registry Γ locals σ expression raw footprint)
    (adapter : GeneralProfileAdapter env U registry Γ
      (AdapterNormal.profile raw) (AdapterNormal.profile requested))
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ nextFootprint,
      Nonempty (SortableCert env U registry Γ locals σ expression relevant requested nextFootprint) ∧
      nextFootprint.Atomizes footprint ∧ nextFootprint.Available available := by
  obtain ⟨normalFootprint, ⟨normal⟩, normalization⟩ := observation.normalize henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  obtain ⟨nextFootprint, ⟨certificate⟩, leaves⟩ :=
    normal.codeFromGeneral (canonical ▸ adapter) formed
  have retained := leaves.trans normalization
  exact ⟨nextFootprint, ⟨certificate⟩, retained,
    retained.available_closed resources closed⟩

end Lean4Lean.AnchoredSource.Adapted
