import Lean4Lean.Theory.Typing.AnchoredNativeDepth
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePruning

/-! Literal source selection never increases current-block native depth.
The proof selects actual constructor subtrees, including the unchanged native plan. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
  {locals : List Nat} {σ : Subst} {expression : VExpr} {current : Name → Bool}

theorem Obs.atom_bounded {locals : List Nat} {σ : Subst} {expression : VExpr}
    {current : Name → Bool} {profile : Profile n} {footprint : Footprint}
    (source : Obs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) :
    ∃ selected : source.AtomSelection atom,
      selected.observation.nativeDepth current ≤ source.nativeDepth current := by
  match n, atom, profile, source with
  | _, _, _, .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨[], .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    exact Nat.le_refl _
  | _, _, _, .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.family lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    exact Nat.le_refl _
  | _, _, _, .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    have singleton := tree.singleton_of_mem member
    refine ⟨⟨[], singleton ▸ Obs.constructor lookup noDefinition noNative noQuotient seedWF seedLength
      levelsWF equivalent signature typeClosed typeCertificate typed tree, .refl _⟩, ?_⟩
    cases singleton
    exact Nat.le_refl _
  | _, a, _, .var locals σ index demand =>
    refine ⟨⟨[(index, ⟨_, .singleton a⟩)], .var locals σ index _, ?_⟩, ?_⟩
    · intro other need hm
      cases List.mem_singleton.mp hm
      exact ⟨⟨_, demand⟩, List.mem_singleton_self _, .inr
        (List.mem_map.mpr ⟨a, member, rfl⟩)⟩
    · simp only [Obs.nativeDepth]; exact Nat.le_refl _
  | _, _, _, .empty => cases member
  | 0, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩, Nat.le_refl _⟩
  | _ + 1, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .app fn arg arguments admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg arguments admitted, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .lam domain guard body normal covered =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal covered, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .pi domain guard bodies =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .pi domain guard bodies, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected, bound⟩ := left.atom_bounded (current := current) member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩,
        Nat.le_trans bound (by simp only [Obs.nativeDepth]; exact Nat.le_max_left _ _)⟩
    · obtain ⟨selected, bound⟩ := right.atom_bounded (current := current) member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩,
        Nat.le_trans bound (by simp only [Obs.nativeDepth]; exact Nat.le_max_right _ _)⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩, Nat.le_refl _⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected, bound⟩ := body.atom_bounded (current := current) hl
    exact ⟨⟨selected.footprint, .pad selected.observation, selected.atomizes⟩,
      by simpa only [Obs.nativeDepth] using bound⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected, bound⟩ := body.atom_bounded (current := current)
      (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.observation, selected.atomizes⟩,
      by simpa only [Obs.nativeDepth] using bound⟩
  | _, _, _, .rowShift body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .rowShift body, .refl _⟩, Nat.le_refl _⟩
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

theorem Obs.subprofile_bounded {input selected : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression input footprint)
    (included : ∀ atom ∈ selected.atoms, atom ∈ input.atoms) :
    ∃ required, ∃ output : Obs env U registry Γ locals σ expression selected required,
      required.Atomizes footprint ∧ output.nativeDepth current ≤ observation.nativeDepth current := by
  induction selected with
  | nil => exact ⟨[], .empty, (fun _ _ h => nomatch h), by simp only [Obs.nativeDepth]; exact Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨first, firstBound⟩ := observation.atom_bounded (current := current) (included head List.mem_cons_self)
    obtain ⟨rest, tailObs, selection, tailBound⟩ :=
      ih (fun atom h => included atom (List.mem_cons_of_mem _ h))
    exact ⟨first.footprint ++ rest, .union first.observation tailObs,
      first.atomizes.append selection, by simp only [Obs.nativeDepth]; exact Nat.max_le.mpr ⟨firstBound, tailBound⟩⟩

private theorem Obs.profileView_bounded {locals : List Nat} {σ : Subst} {expression : VExpr}
    {current : Name → Bool}
    (observation : Obs env U registry Γ locals σ expression (whole : Profile n) footprint)
    (view : ProfileView env U registry Γ (source : Profile n) target)
    (included : List.Subset source whole) :
    ∃ selected, ∃ output : Obs env U registry Γ locals σ expression target selected,
      selected.Atomizes footprint ∧ output.nativeDepth current ≤ observation.nativeDepth current := by
  match view with
  | .nil => exact ⟨[], .empty, (fun _ _ h => nomatch h), by simp only [Obs.nativeDepth]; exact Nat.zero_le _⟩
  | .cons head tail =>
    obtain ⟨first, firstBound⟩ := observation.atom_bounded (current := current) (included List.mem_cons_self)
    obtain ⟨rest, tailObs, selection, tailBound⟩ :=
      observation.profileView_bounded (current := current) tail (fun _ hm => included (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ rest, .union (.view first.observation head) tailObs,
      first.atomizes.append selection, by simp only [Obs.nativeDepth]; exact Nat.max_le.mpr ⟨firstBound, tailBound⟩⟩
termination_by sizeOf view
decreasing_by simp_wf; omega

theorem Obs.normalize_bounded (henv : env.Ordered)
    (observation : Obs env U registry Γ locals σ expression (demand : Profile n) footprint) :
    ∃ selected, ∃ output : Obs env U registry Γ locals σ expression (AdapterNormal.profile demand) selected,
      selected.Atomizes footprint ∧ output.nativeDepth current ≤ observation.nativeDepth current :=
  observation.profileView_bounded (AdapterNormal.profileView henv demand) (fun _ h => h)

theorem Obs.codeCert_of_adapter_bounded
    {raw requested : Profile n} {footprint : Footprint} {available : Valuation}
    (henv : env.Ordered)
    (observation : Obs env U registry Γ locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry Γ raw requested)
    (formed : requested.HasType (.sort true))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ selected, ∃ certificate : CodeCert env U registry Γ locals σ expression requested selected,
      selected.Atomizes footprint ∧ selected.Available available ∧
      certificate.nativeDepth current ≤ observation.nativeDepth current := by
  obtain ⟨normalizedFootprint, normalized, normalization, normalBound⟩ := observation.normalize_bounded (current := current) henv
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  have adapter' : ProfileAdapter env U registry Γ (AdapterNormal.profile raw) requested := canonical ▸ adapter
  obtain ⟨selectedFootprint, selected, selection, selectionBound⟩ :=
    normalized.subprofile_bounded (current := current) (adapter'.sortable_subset formed)
  have selection := selection.trans normalization
  exact ⟨selectedFootprint, .seed selected formed, selection,
    selection.available_closed resources closed, by
      simp only [CodeCert.nativeDepth]; exact Nat.le_trans selectionBound normalBound⟩

@[simp] theorem CodeCert.nativeDepth_lowerRaised (current : Name → Bool)
    {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (certificate : CodeCert env U registry Γ locals σ expression (raiseProfile N bound demand) footprint) :
    (certificate.lowerRaised bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [CodeCert.lowerRaised, Nat.recAux, dite_true]
      exact CodeCert.nativeDepth_cast current (raiseProfile_self ..) _ certificate
    · simp only [CodeCert.lowerRaised, Nat.recAux, dif_neg hn]
      change (CodeCert.lowerRaised (show n ≤ N by omega) (.unpad (cast _ certificate))).nativeDepth current = _
      rw [ih]
      simp only [CodeCert.nativeDepth]
      exact CodeCert.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand) _ certificate

end Lean4Lean.AnchoredSource.Adapted
