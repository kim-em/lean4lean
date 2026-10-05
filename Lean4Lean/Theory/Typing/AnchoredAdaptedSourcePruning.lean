import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceCodeCert
import Lean4Lean.Theory.Typing.AnchoredSourceAdapterCode

/-! Literal atom selection and exact code recovery for the replacement core. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure Obs.AtomSelection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {sourceFootprint : Footprint}
    (_source : Obs env U registry Γ locals σ expression profile sourceFootprint)
    (atom : Atom n) where
  footprint : Footprint
  observation : Obs env U registry Γ locals σ expression (.singleton atom) footprint
  atomizes : footprint.Atomizes sourceFootprint

theorem Obs.AtomSelection.refines
    {sourceFootprint : Footprint}
    {source : Obs env U registry Γ locals σ expression profile sourceFootprint}
    (selected : source.AtomSelection atom) :
    selected.footprint.Refines sourceFootprint := selected.atomizes.refines

/-- Select one value atom. In the application case the entire original
function and argument observations are retained. -/
theorem Obs.atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : Obs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) : Nonempty (source.AtomSelection atom) := by
  match n, atom, profile, source with
  | _, _, _, .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨[], .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, .refl _⟩⟩
  | _, _, _, .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    exact ⟨⟨[], singleton ▸ Obs.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩⟩
  | _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    exact ⟨⟨[], singleton ▸ Obs.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩⟩
  | _, _, _, .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    exact ⟨⟨[], singleton ▸ Obs.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩⟩
  | _, a, _, .var locals σ index demand =>
    refine ⟨⟨[(index, ⟨_, .singleton a⟩)], .var locals σ index _, ?_⟩⟩
    intro other need hm
    cases List.mem_singleton.mp hm
    exact ⟨⟨_, demand⟩, List.mem_singleton_self _, .inr
      (List.mem_map.mpr ⟨a, member, rfl⟩)⟩
  | _, _, _, .empty => cases member
  | 0, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩⟩
  | _ + 1, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩⟩
  | _, _, _, .app fn arg arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg arguments admitted, .refl _⟩⟩
  | _, _, _, .lam domain guard body normal covered =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal covered, .refl _⟩⟩
  | _, _, _, .pi domain guard bodies =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .pi domain guard bodies, .refl _⟩⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected⟩ := left.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩⟩
    · obtain ⟨selected⟩ := right.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩⟩
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

theorem Obs.subprofile
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {realization : Subst} {expression : VExpr}
    {input selected : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals realization expression input footprint)
    (included : ∀ atom ∈ selected.atoms, atom ∈ input.atoms) :
    ∃ required, Nonempty (Obs env U registry target locals realization expression selected required) ∧
      Footprint.Atomizes required footprint := by
  induction selected with
  | nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | cons head tail ih =>
    obtain ⟨headSelection⟩ := observation.atom (included head List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailObs⟩, tailSelection⟩ :=
      ih (fun atom h => included atom (List.mem_cons_of_mem _ h))
    exact ⟨headSelection.footprint ++ tailFootprint,
      ⟨.union headSelection.observation tailObs⟩, headSelection.atomizes.append tailSelection⟩

private theorem Obs.profileView_selected
    (observation : Obs env U registry Γ locals σ expression (whole : Profile n) footprint)
    (view : ProfileView env U registry Γ (source : Profile n) target)
    (included : List.Subset source whole) :
    ∃ selected, Nonempty (Obs env U registry Γ locals σ expression target selected) ∧
      selected.Atomizes footprint := by
  match view with
  | .nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | .cons head tail =>
    obtain ⟨first⟩ := observation.atom (included List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailObservation⟩, selected⟩ :=
      observation.profileView_selected tail (fun _ hm => included (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ tailFootprint,
      ⟨.union (.view first.observation head) tailObservation⟩, first.atomizes.append selected⟩
termination_by sizeOf view
decreasing_by simp_wf; omega

theorem Obs.normalize
    (henv : env.Ordered)
    (observation : Obs env U registry Γ locals σ expression (demand : Profile n) footprint) :
    ∃ selected, Nonempty (Obs env U registry Γ locals σ expression
      (AdapterNormal.profile demand) selected) ∧ selected.Atomizes footprint :=
  observation.profileView_selected (AdapterNormal.profileView henv demand) (fun _ h => h)

theorem Obs.codeCert_of_adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {raw requested : Profile n} {footprint : Footprint} {available : Valuation}
    (henv : env.Ordered)
    (observation : Obs env U registry Γ locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort true))
    (resources : footprint.Available available)
    (closed : available.AtomClosed) :
    ∃ selectedFootprint,
      Nonempty (CodeCert env U registry Γ locals σ expression requested selectedFootprint) ∧
      selectedFootprint.Atomizes footprint ∧ selectedFootprint.Available available := by
  obtain ⟨normalizedFootprint, ⟨normalized⟩, normalization⟩ := observation.normalize henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  have adapter' : ProfileAdapter env U registry Γ (AdapterNormal.profile raw) requested := canonical ▸ adapter
  obtain ⟨selectedFootprint, ⟨selected⟩, selection⟩ :=
    normalized.subprofile (adapter'.sortable_subset formed)
  have selection := selection.trans normalization
  exact ⟨selectedFootprint, ⟨.seed selected formed⟩, selection,
    selection.available_closed resources closed⟩

end Lean4Lean.AnchoredSource.Adapted
