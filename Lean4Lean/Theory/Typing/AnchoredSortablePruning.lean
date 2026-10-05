import Lean4Lean.Theory.Typing.AnchoredSortableGrades
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePruning
import Lean4Lean.Theory.Typing.AnchoredSortableFamilyPlan

/-! Literal selection and normalization retain native Boolean Pi queries
inside computational observations and preserve available source resources. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortableObs.AtomSelection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {sourceFootprint : Footprint}
    (_source : SortableObs env U registry Γ locals σ expression profile sourceFootprint)
    (atom : Atom n) where
  footprint : Footprint
  observation : SortableObs env U registry Γ locals σ expression (.singleton atom) footprint
  atomizes : footprint.Atomizes sourceFootprint

theorem SortableObs.AtomSelection.refines
    {sourceFootprint : Footprint}
    {source : SortableObs env U registry Γ locals σ expression profile sourceFootprint}
    (selected : source.AtomSelection atom) :
    selected.footprint.Refines sourceFootprint := selected.atomizes.refines

/-- Select one value atom. In the application case the entire original
function and argument observations are retained. -/
theorem SortableObs.atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : SortableObs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) : Nonempty (source.AtomSelection atom) := by
  match n, atom, profile, source with
  | _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    exact ⟨⟨[], singleton ▸ SortableObs.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩⟩
  | _, _, _, .legacy observation =>
    obtain ⟨selected⟩ := observation.atom member
    exact ⟨⟨selected.footprint, .legacy selected.observation, selected.atomizes⟩⟩
  | _, _, _, .code relevant certificate =>
    exact ⟨⟨_, .code relevant (.select certificate member), .refl _⟩⟩
  | _, _, _, .app fn arg arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg arguments admitted, .refl _⟩⟩
  | _, _, _, .lam domain guard body normal covered =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal covered, .refl _⟩⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected⟩ := left.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩⟩
    · obtain ⟨selected⟩ := right.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩⟩
  | _, _, _, .action body act =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .action body act, .refl _⟩⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected⟩ := body.atom hl
    exact ⟨⟨selected.footprint, .pad selected.observation, selected.atomizes⟩⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected⟩ := body.atom (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.observation, selected.atomizes⟩⟩
  | _, _, _, .rowShift body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .rowShift body, .refl _⟩⟩
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

theorem SortableObs.subprofile
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {expression : VExpr}
    {input selected : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry target locals realization expression input footprint)
    (included : ∀ atom ∈ selected.atoms, atom ∈ input.atoms) :
    ∃ required, Nonempty (SortableObs env U registry target locals realization expression selected required) ∧
      Footprint.Atomizes required footprint := by
  induction selected with
  | nil => exact ⟨[], ⟨.legacy .empty⟩, fun _ _ h => nomatch h⟩
  | cons head tail ih =>
    obtain ⟨headSelection⟩ := observation.atom (included head List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailSortableObs⟩, tailSelection⟩ :=
      ih (fun atom h => included atom (List.mem_cons_of_mem _ h))
    exact ⟨headSelection.footprint ++ tailFootprint,
      ⟨.union headSelection.observation tailSortableObs⟩, headSelection.atomizes.append tailSelection⟩

private theorem SortableObs.profileView_selected
    (observation : SortableObs env U registry Γ locals σ expression (whole : Profile n) footprint)
    (view : ProfileView env U registry Γ (source : Profile n) target)
    (included : List.Subset source whole) :
    ∃ selected, Nonempty (SortableObs env U registry Γ locals σ expression target selected) ∧
      selected.Atomizes footprint := by
  match view with
  | .nil => exact ⟨[], ⟨.legacy .empty⟩, fun _ _ h => nomatch h⟩
  | .cons head tail =>
    obtain ⟨first⟩ := observation.atom (included List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailSortableObservation⟩, selected⟩ :=
      observation.profileView_selected tail (fun _ hm => included (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ tailFootprint,
      ⟨.union (.view first.observation head) tailSortableObservation⟩, first.atomizes.append selected⟩
termination_by sizeOf view
decreasing_by simp_wf; omega

theorem SortableObs.normalize
    (henv : env.Ordered)
    (observation : SortableObs env U registry Γ locals σ expression (demand : Profile n) footprint) :
    ∃ selected, Nonempty (SortableObs env U registry Γ locals σ expression
      (AdapterNormal.profile demand) selected) ∧ selected.Atomizes footprint :=
  observation.profileView_selected (AdapterNormal.profileView henv demand) (fun _ h => h)

theorem SortableObs.sortableCert_of_adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {raw requested : Profile n} {footprint : Footprint} {available : Valuation}
    (henv : env.Ordered)
    (observation : SortableObs env U registry Γ locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available)
    (closed : available.AtomClosed) :
    ∃ selectedFootprint,
      Nonempty (SortableCert env U registry Γ locals σ expression relevant requested selectedFootprint) ∧
      selectedFootprint.Atomizes footprint ∧ selectedFootprint.Available available := by
  obtain ⟨normalizedFootprint, ⟨normalized⟩, normalization⟩ := observation.normalize henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  have adapter' : ProfileAdapter env U registry Γ (AdapterNormal.profile raw) requested := canonical ▸ adapter
  obtain ⟨selectedFootprint, ⟨selected⟩, selection⟩ :=
    normalized.subprofile (adapter'.sortable_subset formed)
  have selection := selection.trans normalization
  exact ⟨selectedFootprint, ⟨.observe selected formed⟩, selection,
    selection.available_closed resources closed⟩

end Lean4Lean.AnchoredSource.Adapted
