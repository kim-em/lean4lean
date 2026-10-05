import Lean4Lean.Theory.Typing.AnchoredDataAdmissibility

/-! An isolated coupled target-policy prototype. The lower relations are
constructed by the same rank recursion as the real semantics; eligibility
is checked at every actual value atom. No source or semantic callback is
assumed. This file does not change the production relation or source grammar. -/
namespace Lean4Lean.AnchoredProfiles
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

theorem DataTagEligible.rename_iff
    {env : VEnv} {registry : CanonicalHead.Registry} {atom : Atom (n + 1)} {ρ : Lift} :
    DataTagEligible env registry (atom.rename ρ) ↔ DataTagEligible env registry atom := by
  cases atom with
  | sort | fn | pi | pad | family => exact Iff.rfl
  | ctor data => exact Iff.rfl
  | record data =>
    change (∃ info, registry.projections data.family.name = some info ∧
      ∃ entry ∈ data.fields.map (fun entry => (entry.1, entry.2.rename ρ)),
        entry.1 < info.numFields ∧ Profile.Nonempty entry.2.input) ↔ _
    constructor
    · rintro ⟨info, lookup, entry, member, bound, nonempty⟩
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      refine ⟨info, lookup, original, present, bound, ?_⟩
      intro empty
      change original.2.input = [] at empty
      apply nonempty
      change Profile.rename ρ original.2.input = []
      rw [empty]
      rfl
    · rintro ⟨info, lookup, entry, member, bound, nonempty⟩
      refine ⟨info, lookup, (entry.1, entry.2.rename ρ),
        List.mem_map.mpr ⟨entry, member, rfl⟩, bound, ?_⟩
      intro empty
      apply nonempty
      exact List.map_eq_nil_iff.mp empty

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics.ExtensionalPrototype
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def relations (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) :
    (n : Nat) → Relations n
  | 0 => AnchoredSemantics.relations env U registry 0
  | n + 1 =>
    let lower := relations env U registry n
    let code := FutureCode env U fun Γ left right (profile : Profile (n + 1)) =>
      ∀ atom ∈ profile.atoms, CodeAtom env U registry lower Γ left right atom
    { code := code
      term := EachAtom <| FutureTerm env U <| SaturatedTerm env U fun Γ left right type value typeProfile =>
        value.HasType typeProfile ∧ code Γ type type typeProfile ∧
          ∀ atom ∈ value.atoms, DataTagEligible env registry atom ∧
            TermAtom env U registry lower Γ left right type typeProfile atom }

def Related (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (value support : Profile n) : Prop :=
  (relations env U registry n).term Γ left right type value support

def Admitted (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (key : Key n) (left right : VExpr) : Prop :=
  Admission env U (relations env U registry n) Γ key left right

/-- The saturated proof world cannot hide a forbidden data tag. Frozen
names, field positions and nonempty field inputs survive the literal lift. -/
theorem Related.eligible
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {value support : Profile (n + 1)}
    (related : Related env U registry Γ left right type value support) :
    ∀ atom ∈ value.atoms, DataTagEligible env registry atom := by
  intro atom member
  have actual := related atom member Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at actual
  rcases actual with empty | ⟨Δ, ρ, insertion, typed, code, terms⟩
  · cases empty
  · have found := (terms (atom.rename ρ) (List.mem_singleton_self _)).1
    exact DataTagEligible.rename_iff.mp found

/-- Existing admission guards now make eta-family constructor inputs
impossible. In particular the old input-strengthening counterexample cannot
be instantiated with these coupled lower relations. -/
theorem Admitted.noEtaConstructor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {key : Key (n + 1)} {left right : VExpr}
    (admitted : Admitted env U registry Γ key left right)
    {demand : ConstructorData (Profile n)}
    (member : (.ctor demand : Atom (n + 1)) ∈ key.input.atoms)
    {info : VProjectionInfo}
    (registered : env.projections demand.family.name info)
    (unindexed : info.nindices = 0) : False := by
  obtain ⟨_, _, support, _, _, _, anchor, _⟩ := admitted
  exact Related.eligible formed anchor _ member info registered unindexed

/-- A field-free record tag is equally unavailable through an admission.
Keeping a syntactically nonempty list of empty projection requests cannot
evade the guard: an actual in-range field is required. -/
theorem Admitted.noFieldFreeRecord
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {key : Key (n + 1)} {left right : VExpr}
    (admitted : Admitted env U registry Γ key left right)
    {demand : RecordData (Profile n)}
    (member : (.record demand : Atom (n + 1)) ∈ key.input.atoms)
    {info : VProjectionInfo}
    (registered : registry.projections demand.family.name = some info)
    (noFields : info.numFields = 0) : False := by
  obtain ⟨_, _, support, _, _, _, anchor, _⟩ := admitted
  obtain ⟨other, lookup, entry, present, bound, _⟩ := Related.eligible formed anchor _ member
  rw [registered] at lookup
  cases Option.some.inj lookup
  omega

/-- A forbidden major query cannot be hidden inside a live function
observer either: its existing anchor admission uses the guarded lower rank.
Only actual finite anchor evidence is inspected in the proof world. -/
theorem Related.fn_noEtaConstructor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {key : Key (n + 1)} {output : Atom (n + 1)}
    {support : Profile (n + 2)}
    (related : Related env U registry Γ left right type (Profile.fn key output) support)
    {demand : ConstructorData (Profile n)}
    (member : (.ctor demand : Atom (n + 1)) ∈ key.input.atoms)
    {info : VProjectionInfo}
    (registered : env.projections demand.family.name info)
    (unindexed : info.nindices = 0) : False := by
  have actual := related (.fn key output) (List.mem_singleton_self _) Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at actual
  rcases actual with empty | ⟨Δ, ρ, insertion, typed, code, terms⟩
  · cases empty
  · have behavior := (terms (Atom.rename (n := n + 2) ρ (.fn key output))
      (List.mem_singleton_self _)).2
    have seed : Admitted env U registry Δ (key.rename ρ)
        (key.anchor.lift' ρ) (key.anchor.lift' ρ) := behavior.1
    apply seed.noEtaConstructor (insertion.targetWF henv)
      (demand := demand.rename ρ) (info := info)
    · exact List.mem_map.mpr ⟨.ctor demand, member, rfl⟩
    · exact registered
    · exact unindexed

end Lean4Lean.AnchoredSemantics.ExtensionalPrototype
