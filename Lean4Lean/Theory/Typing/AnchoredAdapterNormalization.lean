import Lean4Lean.Theory.Typing.AnchoredAdapterInterpretation
import Lean4Lean.Theory.Typing.AnchoredViewInterpretation

/-! Canonical endpoints for finite adapters. Padding is distributed through
function atoms; the concrete reversible views justify both endpoint changes.
No intermediate type capability is part of the normalized adapter interface. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

namespace AdapterNormal

def shiftAtom : {n : Nat} → Atom n → Atom (n + 1)
  | 0, atom => .pad atom
  | _ + 1, .sort flag => .pad (.sort flag)
  | _ + 1, .pi A B domain rows => .pad (.pi A B domain rows)
  | _ + 1, .family data => .pad (.family data)
  | _ + 1, .ctor data => .pad (.ctor data)
  | _ + 1, .record data => .pad (.record data)
  | _ + 1, .pad atom => .pad (.pad atom)
  | _ + 1, .fn key output =>
      .fn ⟨key.domain, key.anchor, key.input.map shiftAtom⟩ (shiftAtom output)

def shiftProfile (profile : Profile n) : Profile (n + 1) := profile.map shiftAtom

def shiftKey (key : Key n) : Key (n + 1) :=
  ⟨key.domain, key.anchor, shiftProfile key.input⟩

def atom : {n : Nat} → Atom n → Atom n
  | 0, value => value
  | _ + 1, .sort flag => .sort flag
  | _ + 1, .pi A B domain rows => .pi A B domain rows
  | _ + 1, .family data => .family data
  | _ + 1, .ctor data => .ctor data
  | _ + 1, .record data => .record data
  | _ + 1, .pad value => shiftAtom (atom value)
  | _ + 1, .fn key output =>
      .fn ⟨key.domain, key.anchor, key.input.map atom⟩ (atom output)

def profile (value : Profile n) : Profile n := value.map atom

def key (value : Key n) : Key n := ⟨value.domain, value.anchor, profile value.input⟩

theorem atom_fn (k : Key n) (output : Atom n) :
    atom (n := n + 1) (.fn k output) = .fn (key k) (atom output) := rfl

theorem atom_pad (value : Atom n) :
    atom (n := n + 1) (.pad value) = shiftAtom (atom value) := rfl

theorem profile_pad (value : Profile n) : profile value.pad = shiftProfile (profile value) := by
  simp only [profile, Profile.pad, shiftProfile, List.map_map]
  rfl

theorem atom_commutePadFn (k : Key n) (output : Atom n) :
    atom (n := n + 2) (.pad (.fn k output)) = atom (n := n + 2) (.fn k.pad (.pad output)) := by
  simp only [atom, shiftAtom, Key.pad, Profile.pad, List.map_map]
  rfl

theorem atom_shiftAtom (value : Atom n) : atom (shiftAtom value) = shiftAtom (atom value) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases value with
    | sort | pi | pad | family | ctor | record => rfl
    | fn k output =>
      simp only [shiftAtom, atom, List.map_map]
      congr 2
      · apply List.map_congr_left
        intro a _
        exact ih a
      · exact ih output

theorem atom_idem (value : Atom n) : atom (atom value) = atom value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases value with
    | sort | pi | family | ctor | record => rfl
    | pad value => exact (atom_shiftAtom (atom value)).trans (congrArg shiftAtom (ih value))
    | fn k output =>
      simp only [atom, List.map_map]
      rw [ih output]
      congr 2
      apply List.map_congr_left
      intro a _
      exact ih a

theorem profile_idem (value : Profile n) : profile (profile value) = profile value := by
  simp only [profile, List.map_map]
  exact List.map_congr_left (fun a _ => atom_idem a)

theorem shiftAtom_rename (value : Atom n) (ρ : Lift) :
    shiftAtom (value.rename ρ) = (shiftAtom value).rename ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases value with
    | sort | pi | pad | family | ctor | record => rfl
    | fn k output =>
      simp only [Atom.rename, shiftAtom, List.map_map]
      rw [ih output]
      congr 2
      apply List.map_congr_left
      intro a _
      exact ih a

theorem atom_rename (value : Atom n) (ρ : Lift) :
    atom (value.rename ρ) = (atom value).rename ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases value with
    | sort | pi | family | ctor | record => rfl
    | pad value =>
      change shiftAtom (atom (value.rename ρ)) = (shiftAtom (atom value)).rename ρ
      rw [ih value, shiftAtom_rename]
    | fn k output =>
      simp only [Atom.rename, atom, List.map_map]
      rw [ih output]
      congr 2
      apply List.map_congr_left
      intro a _
      exact ih a

theorem profile_rename (value : Profile n) (ρ : Lift) :
    profile (value.rename ρ) = (profile value).rename ρ := by
  simp only [profile, Profile.rename, List.map_map]
  exact List.map_congr_left (fun a _ => atom_rename a ρ)

mutual
noncomputable def shiftView (henv : env.Ordered) (value : Atom n) :
    AtomView env U registry Γ (n := n + 1) (.pad value) (shiftAtom value) := by
  match n, value with
  | 0, value => exact .refl _
  | _ + 1, .sort _ => exact .refl _
  | _ + 1, .pi _ _ _ _ => exact .refl _
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => exact .refl _
  | _ + 1, .pad _ => exact .refl _
  | _ + 1, .fn k output =>
    have inputs := shiftProfileView (U := U) (registry := registry) (Γ := Γ) henv k.input
    exact .trans (.commutePadFn k output)
      (.trans (.fn (Key.pad k) (shiftView henv output))
        (.input (inputs.inverse henv) inputs))
termination_by (2 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def shiftProfileView (henv : env.Ordered) (value : Profile n) :
    ProfileView env U registry Γ value.pad (shiftProfile value) := by
  match value with
  | [] => exact .nil
  | head :: tail => exact .cons (shiftView henv head) (shiftProfileView henv tail)
termination_by (2 * n + 1, value.length)
decreasing_by all_goals simp_wf; omega
end

mutual
noncomputable def view (henv : env.Ordered) (value : Atom n) :
    AtomView env U registry Γ value (atom value) := by
  match n, value with
  | 0, value => exact .refl _
  | _ + 1, .sort _ => exact .refl _
  | _ + 1, .pi _ _ _ _ => exact .refl _
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => exact .refl _
  | _ + 1, .pad value => exact .trans (.pad (view henv value)) (shiftView henv (atom value))
  | _ + 1, .fn k output =>
    have inputs := profileView (U := U) (registry := registry) (Γ := Γ) henv k.input
    exact .trans (.fn k (view henv output)) (.input (inputs.inverse henv) inputs)
termination_by (2 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def profileView (henv : env.Ordered) (value : Profile n) :
    ProfileView env U registry Γ value (profile value) := by
  match value with
  | [] => exact .nil
  | head :: tail => exact .cons (view henv head) (profileView henv tail)
termination_by (2 * n + 1, value.length)
decreasing_by all_goals simp_wf; omega
end

end AdapterNormal

/-- The intermediate endpoints are fixed syntax, so cutting two adapters
does not create a new demand for an intermediate type capability. -/
abbrev NormalAtomAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (a b : Atom n) :=
  AtomAdapter env U registry Γ (AdapterNormal.atom a) (AdapterNormal.atom b)

abbrev NormalProfileAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (p q : Profile n) :=
  ProfileAdapter env U registry Γ (AdapterNormal.profile p) (AdapterNormal.profile q)

noncomputable def NormalAtomAdapter.comp
    (first : NormalAtomAdapter env U registry Γ a b)
    (second : NormalAtomAdapter env U registry Γ b c) :
    NormalAtomAdapter env U registry Γ a c := AtomAdapter.comp first second

noncomputable def NormalProfileAdapter.comp
    (first : NormalProfileAdapter env U registry Γ p q)
    (second : NormalProfileAdapter env U registry Γ q r) :
    NormalProfileAdapter env U registry Γ p r := ProfileAdapter.comp first second

noncomputable def NormalAtomAdapter.future
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (adapter : NormalAtomAdapter env U registry Γ a b) :
    NormalAtomAdapter env U registry Δ (a.rename ρ) (b.rename ρ) := by
  simpa only [NormalAtomAdapter, AdapterNormal.atom_rename] using AtomAdapter.future henv W adapter

noncomputable def NormalProfileAdapter.future
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (adapter : NormalProfileAdapter env U registry Γ p q) :
    NormalProfileAdapter env U registry Δ (p.rename ρ) (q.rename ρ) := by
  simpa only [NormalProfileAdapter, AdapterNormal.profile_rename] using ProfileAdapter.future henv W adapter

theorem NormalAtomAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {a b : Atom n}
    (adapter : NormalAtomAdapter env U registry Γ a b)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : (Profile.singleton b).HasType new)
    (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A (.singleton a) old) :
    Related env U registry Γ l r A (.singleton b) new := by
  let leftView := AdapterNormal.view (U := U) (registry := registry) (Γ := Γ) henv a
  let rightView := AdapterNormal.view (U := U) (registry := registry) (Γ := Γ) henv b
  have normalized := AtomAdapter.termMap adapter henv hscoped (rightView.mapType_typed typed)
    (rightView.codeMap henv hscoped code) (leftView.termMap henv hscoped hΓ related)
  exact Related.retag henv typed code
    ((rightView.inverse henv).termMap henv hscoped hΓ normalized)

theorem NormalProfileAdapter.termMap
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {p q : Profile n}
    (adapter : NormalProfileAdapter env U registry Γ p q)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {l r A : VExpr} {old new : Profile n}
    (typed : q.HasType new) (code : TypeRelated env U registry Γ A A new)
    (related : Related env U registry Γ l r A p old) :
    Related env U registry Γ l r A q new := by
  apply Related.of_singletons
  intro atom member
  obtain ⟨origin, originMember, ⟨entry⟩⟩ := adapter.origin (List.mem_map.mpr ⟨atom, member, rfl⟩)
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp originMember
  exact NormalAtomAdapter.termMap entry henv hscoped hΓ (typed.singleton_of_mem member) code
    (related.singleton_of_mem originalMember)

end Lean4Lean.AnchoredSemantics
