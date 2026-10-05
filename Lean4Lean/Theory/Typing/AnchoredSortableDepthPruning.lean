import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
import Lean4Lean.Theory.Typing.AnchoredSortablePruning

/-! The same selected source query preserves every declaration control at
once. The existential observer is outside the universal control binder,
which is necessary for retaining several caller budgets simultaneously. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}

theorem Obs.atom_allDepth {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : Obs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) :
    ∃ selected : source.AtomSelection atom,
      ∀ current, selected.observation.nativeDepth current ≤ source.nativeDepth current := by
  match n, atom, profile, source with
  | _, _, _, .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨[], .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    intro current; exact Nat.le_refl _
  | _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.family lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    intro current; exact Nat.le_refl _
  | _, _, _, .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.constructor lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    intro current; exact Nat.le_refl _
  | _, a, _, .var locals σ index demand =>
    refine ⟨⟨[(index, ⟨_, .singleton a⟩)], .var locals σ index _, ?_⟩, ?_⟩
    · intro other need hm
      cases List.mem_singleton.mp hm
      exact ⟨⟨_, demand⟩, List.mem_singleton_self _, .inr
        (List.mem_map.mpr ⟨a, member, rfl⟩)⟩
    · intro current; simp only [Obs.nativeDepth]; exact Nat.le_refl _
  | _, _, _, .empty => cases member
  | 0, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _ + 1, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .app fn arg arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg arguments admitted, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .lam domain guard body normal covered =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal covered, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .pi domain guard bodies =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .pi domain guard bodies, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected, bound⟩ := left.atom_allDepth member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩,
        fun current => Nat.le_trans (bound current) (by simp only [Obs.nativeDepth]; exact Nat.le_max_left _ _)⟩
    · obtain ⟨selected, bound⟩ := right.atom_allDepth member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩,
        fun current => Nat.le_trans (bound current) (by simp only [Obs.nativeDepth]; exact Nat.le_max_right _ _)⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩, (fun _ => Nat.le_refl _)⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected, bound⟩ := body.atom_allDepth hl
    exact ⟨⟨selected.footprint, .pad selected.observation, selected.atomizes⟩,
      by intro current; simpa only [Obs.nativeDepth] using bound current⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected, bound⟩ := body.atom_allDepth
      (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.observation, selected.atomizes⟩,
      by intro current; simpa only [Obs.nativeDepth] using bound current⟩
  | _, _, _, .rowShift body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .rowShift body, .refl _⟩, (fun _ => Nat.le_refl _)⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)


theorem SortableObs.atom_allDepth
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : SortableObs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) :
    ∃ selected : source.AtomSelection atom,
      ∀ current, selected.observation.nativeDepth current ≤ source.nativeDepth current := by
  match n, atom, profile, source with
  | _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ SortableObs.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    exact fun _ => Nat.le_refl _
  | _, _, _, .legacy observation =>
    obtain ⟨selected, bound⟩ := observation.atom_allDepth member
    exact ⟨⟨selected.footprint, .legacy selected.observation, selected.atomizes⟩, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .code relevant certificate =>
    exact ⟨⟨_, .code relevant (.select certificate member), .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .app fn arg arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg arguments admitted, .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .lam domain guard body normal covered =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal covered, .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected, bound⟩ := left.atom_allDepth member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩,
        fun current => Nat.le_trans (bound current) (by simp only [SortableObs.nativeDepth]; exact Nat.le_max_left _ _)⟩
    · obtain ⟨selected, bound⟩ := right.atom_allDepth member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩,
        fun current => Nat.le_trans (bound current) (by simp only [SortableObs.nativeDepth]; exact Nat.le_max_right _ _)⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .action body act =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .action body act, .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected, bound⟩ := body.atom_allDepth hl
    exact ⟨⟨selected.footprint, .pad selected.observation, selected.atomizes⟩, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected, bound⟩ := body.atom_allDepth (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.observation, selected.atomizes⟩, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .rowShift body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .rowShift body, .refl _⟩, by intro current; simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]; exact Nat.le_refl _⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

private theorem SortableObs.profileView_allDepth
    (observation : SortableObs env U registry Γ locals σ expression (whole : Profile n) footprint)
    (view : ProfileView env U registry Γ (source : Profile n) target)
    (included : List.Subset source whole) :
    ∃ selected, ∃ output : SortableObs env U registry Γ locals σ expression target selected,
      selected.Atomizes footprint ∧
      ∀ current, output.nativeDepth current ≤ observation.nativeDepth current := by
  match view with
  | .nil => exact ⟨[], .legacy .empty, (fun _ _ h => nomatch h), by intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _⟩
  | .cons head tail =>
    obtain ⟨first, firstBound⟩ := observation.atom_allDepth (included List.mem_cons_self)
    obtain ⟨rest, tailObs, selection, tailBound⟩ :=
      observation.profileView_allDepth tail (fun _ hm => included (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ rest, .union (.view first.observation head) tailObs,
      first.atomizes.append selection, by intro current; simpa only [SortableObs.nativeDepth] using Nat.max_le.mpr ⟨firstBound current, tailBound current⟩⟩
termination_by sizeOf view
decreasing_by simp_wf; omega

theorem SortableObs.normalize_allDepth (henv : env.Ordered)
    (observation : SortableObs env U registry Γ locals σ expression (demand : Profile n) footprint) :
    ∃ selected, ∃ output : SortableObs env U registry Γ locals σ expression (AdapterNormal.profile demand) selected,
      selected.Atomizes footprint ∧
      ∀ current, output.nativeDepth current ≤ observation.nativeDepth current :=
  observation.profileView_allDepth (AdapterNormal.profileView henv demand) (fun _ h => h)

end Lean4Lean.AnchoredSource.Adapted
