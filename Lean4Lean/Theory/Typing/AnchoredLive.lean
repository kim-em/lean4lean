import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

/-! Finite liveness of observed value atoms. A function demand retains its
concrete anchor admission and liveness of its output; no universal source
producer or assigned-type callback is part of the evidence. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def Atom.Live (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => True
  | _ + 1, .sort _ => True
  | _ + 1, .pi _ _ _ _ => True
  -- Data descriptors are frozen: the available views never eliminate their keys.
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => True
  | _ + 1, .fn key output =>
      Admitted env U registry Γ key key.anchor key.anchor ∧ Atom.Live env U registry Γ output
  | _ + 1, .pad atom => Atom.Live env U registry Γ atom

def Profile.Live (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, Atom.Live env U registry Γ atom

theorem Profile.Live.singleton_iff :
    Profile.Live env U registry Γ (.singleton atom) ↔ Atom.Live env U registry Γ atom :=
  ⟨fun h => h _ (List.mem_singleton_self _), fun h _ hm => (List.mem_singleton.mp hm) ▸ h⟩

theorem Profile.Live.empty : Profile.Live env U registry Γ (Profile.empty : Profile n) :=
  fun _ h => nomatch h

theorem Profile.Live.subset (h : Profile.Live env U registry Γ p)
    (included : List.Subset q p) : Profile.Live env U registry Γ q :=
  fun atom member => h atom (included member)

theorem Profile.Live.union_iff :
    Profile.Live env U registry Γ (p.union q) ↔
      Profile.Live env U registry Γ p ∧ Profile.Live env U registry Γ q := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append_left _ ha),
      fun a ha => h a (List.mem_append_right _ ha)⟩
  · rintro ⟨hp, hq⟩ a ha
    exact (List.mem_append.mp ha).elim (hp a) (hq a)

theorem Profile.Live.pad_iff {p : Profile n} :
    Profile.Live env U registry Γ p.pad ↔ Profile.Live env U registry Γ p := by
  constructor
  · intro h a ha
    exact h (.pad a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h a ha
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha
    exact h old ho

theorem Atom.Live.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {atom : Atom n} (h : Atom.Live env U registry Γ atom) :
    Atom.Live env U registry Δ (atom.rename ρ) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | record => trivial
    | pad atom => exact ih h
    | fn key output => exact ⟨Admitted.future henv W h.1, ih h.2⟩

theorem Profile.Live.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {profile : Profile n} (h : Profile.Live env U registry Γ profile) :
    Profile.Live env U registry Δ (profile.rename ρ) := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact (h old ho).future henv W

theorem AtomView.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  match n, a, b, view with
  | _, _, _, .refl _ => exact live
  | _ + 1, _, _, .reanchor admitted => exact ⟨admitted.reset_anchor, live.2⟩
  | _ + 1, _, _, .domainRekey path typed formed bridge =>
    exact ⟨live.1.rekey henv path typed formed bridge, live.2⟩
  | _ + 1, _, _, .input forward backward =>
    exact ⟨(AdapterSeed.view .same backward).admission henv hscoped hΓ live.1, live.2⟩
  | _ + 2, _, _, .commutePadFn _ _ => exact ⟨Admitted.pad henv live.1, live.2⟩
  | _ + 2, _, _, .uncommutePadFn _ _ => exact ⟨Admitted.unpad henv hΓ live.1, live.2⟩
  | _ + 1, _, _, .fn _ child => exact ⟨live.1, child.live henv hscoped hΓ live.2⟩
  | _ + 1, _, _, .pad child => exact child.live henv hscoped hΓ live
  | _, _, _, .trans first second =>
    exact second.live henv hscoped hΓ (first.live henv hscoped hΓ live)
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

theorem ProfileView.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {source target : Profile n} (view : ProfileView env U registry Γ source target)
    (live : Profile.Live env U registry Γ source) : Profile.Live env U registry Γ target := by
  match view with
  | .nil => exact .empty
  | .cons head tail =>
    intro atom member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.live henv hscoped hΓ (live _ List.mem_cons_self)
    · exact tail.live henv hscoped hΓ
        (fun a ha => live a (List.mem_cons_of_mem _ ha)) atom member
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

theorem AtomAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : AtomAdapter env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact live
  | _ + 1, _, _, .fn keys result =>
    exact ⟨keys.forward henv hscoped hΓ live.1, result.live henv hscoped hΓ live.2⟩
  | _ + 1, _, _, .pad child => exact child.live henv hscoped hΓ live
termination_by sizeOf adapter
decreasing_by all_goals simp_wf; omega

theorem ProfileAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {source target : Profile n} (adapter : ProfileAdapter env U registry Γ source target)
    (live : Profile.Live env U registry Γ source) : Profile.Live env U registry Γ target := by
  intro atom member
  obtain ⟨old, ho, ⟨entry⟩⟩ := adapter.origin member
  exact entry.live henv hscoped hΓ (live old ho)

theorem NormalAtomAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : NormalAtomAdapter env U registry Γ a b)
    (live : Atom.Live env U registry Γ a) : Atom.Live env U registry Γ b := by
  have normalized := (AdapterNormal.view henv a).live henv hscoped hΓ live
  have changed := AtomAdapter.live henv hscoped hΓ adapter normalized
  exact ((AdapterNormal.view henv b).inverse henv).live henv hscoped hΓ changed

theorem NormalProfileAdapter.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {source target : Profile n} (adapter : NormalProfileAdapter env U registry Γ source target)
    (live : Profile.Live env U registry Γ source) : Profile.Live env U registry Γ target := by
  have normalized := (AdapterNormal.profileView henv source).live henv hscoped hΓ live
  have changed := ProfileAdapter.live henv hscoped hΓ adapter normalized
  exact ((AdapterNormal.profileView henv target).inverse henv).live henv hscoped hΓ changed

end Lean4Lean.AnchoredSemantics
