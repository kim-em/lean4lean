import Lean4Lean.Theory.Typing.AnchoredSourceNormalization

/-! Recover an exact source code certificate from a changed computational
profile. Hereditary adapters cannot change sortable atoms; finite origin
selection therefore suffices, without a new code-adapter source constructor.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Directional function adaptation never changes a universe/code demand.
Padding follows the strict lower-rank adapter. -/
theorem AtomAdapter.sortable_rigid
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (adapter : AtomAdapter env U registry Γ a b)
    (formed : (Profile.singleton b).HasType (.sort relevant)) : a = b := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => rfl
  | _ + 1, _, _, .fn keys result =>
    obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
    have hcover : cover = .sort relevant := List.mem_singleton.mp member
    subst cover
    contradiction
  | _ + 1, _, _, @AtomAdapter.pad _ _ _ _ _ first second child =>
    have padded : (Profile.singleton second).pad.HasType (.sort relevant) := formed
    have lower : (Profile.singleton second).HasType (.sort relevant) := by
      simpa only [Profile.down_sort] using padded.pad_inv
    have eq := child.sortable_rigid lower
    cases eq
    rfl
termination_by n

/-- Every requested code atom is literally present in the raw returned
profile. Unused raw atoms may remain and requested occurrences may repeat. -/
theorem ProfileAdapter.sortable_subset
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {source target : Profile n}
    (adapter : ProfileAdapter env U registry Γ source target)
    (formed : target.HasType (.sort relevant)) : List.Subset target source := by
  intro atom member
  obtain ⟨original, originalMember, ⟨entry⟩⟩ := adapter.origin member
  have equal := entry.sortable_rigid (formed.singleton_of_mem member)
  exact equal ▸ originalMember

theorem AdapterNormal.shiftAtom_sortable {a : Atom n}
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    AdapterNormal.shiftAtom a = AtomData.pad a := by
  cases n with
  | zero => rfl
  | succ n =>
    cases a with
    | sort | pi | pad | family | ctor | record => rfl
    | fn key output =>
      obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      have hcover : cover = .sort relevant := List.mem_singleton.mp member
      subst cover
      contradiction

theorem AdapterNormal.atom_sortable {a : Atom n}
    (formed : (Profile.singleton a).HasType (.sort relevant)) :
    AdapterNormal.atom a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases a with
    | sort | pi | family | ctor | record => rfl
    | fn key output =>
      obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      have hcover : cover = .sort relevant := List.mem_singleton.mp member
      subst cover
      contradiction
    | pad a =>
      have padded : (Profile.singleton a).pad.HasType (.sort relevant) := formed
      have lower : (Profile.singleton a).HasType (.sort relevant) := by
        simpa only [Profile.down_sort] using padded.pad_inv
      change AdapterNormal.shiftAtom (AdapterNormal.atom a) = .pad a
      rw [ih lower]
      exact AdapterNormal.shiftAtom_sortable lower

theorem AdapterNormal.profile_sortable {p : Profile n}
    (formed : p.HasType (.sort relevant)) : AdapterNormal.profile p = p := by
  change p.map AdapterNormal.atom = p
  calc
    p.map AdapterNormal.atom = p.map id := List.map_congr_left
      (fun a hm => AdapterNormal.atom_sortable (formed.singleton_of_mem hm))
    _ = p := List.map_id p

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- This is the seed operation needed by original type-child transfer after
its computational result changes demand. It selects actual observation
atoms; active application arguments remain whole under `Obs.subprofile`. -/
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

end Lean4Lean.AnchoredSource
