import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableRetraction

/-! Exact grade restoration for formation certificates preserves both sort
flags and every frozen family request. Native Pi certificates stay in the
new grammar; only ordinary observation seeds use the legacy F bridge. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableCert.raise {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (certificate : SortableCert env U registry Γ locals σ expression relevant demand footprint) :
    SortableCert env U registry Γ locals σ expression relevant (raiseProfile N bound demand) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact certificate
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using certificate
    · have small : n ≤ N := by omega
      simpa only [raiseProfile_step small] using SortableCert.pad (ih small)

noncomputable def SortableCert.lowerRaised {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (certificate : SortableCert env U registry Γ locals σ expression relevant
      (raiseProfile N bound demand) footprint) :
    SortableCert env U registry Γ locals σ expression relevant demand footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact certificate
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using certificate
    · have small : n ≤ N := by omega
      rw [raiseProfile_step small] at certificate
      exact ih small (.unpad certificate)

theorem Obs.sortableCert_of_adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {raw requested : Profile n} {footprint : Footprint} {available : Valuation}
    (henv : env.Ordered)
    (observation : Obs env U registry target locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry target raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ selectedFootprint,
      Nonempty (SortableCert env U registry target locals σ expression relevant requested selectedFootprint) ∧
      selectedFootprint.Atomizes footprint ∧ selectedFootprint.Available available := by
  obtain ⟨footprint, ⟨selected⟩, atomizes, resources⟩ :=
    observation.sortable_of_adapter henv adapter formed resources closed
  exact ⟨footprint, ⟨.seed selected formed⟩, atomizes, resources⟩

theorem GradedResult.sortableCode
    (henv : env.Ordered) (closed : available.AtomClosed)
    (result : GradedResult env U registry Γ locals σ available expression requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, Nonempty (SortableCert env U registry Γ locals σ expression relevant requested footprint) ∧
      footprint.Available available := by
  obtain ⟨footprint, ⟨certificate⟩, _, resources⟩ := result.observation.sortableCert_of_adapter
    henv result.adapter (Profile.HasType.raise_sort result.bound formed) result.resources closed
  exact ⟨footprint, ⟨certificate.lowerRaised result.bound⟩, resources⟩

end Lean4Lean.AnchoredSource.Adapted
