import Lean4Lean.Theory.Typing.AnchoredDataLaws
import Lean4Lean.Theory.Typing.AnchoredSupportLaws
import Lean4Lean.Theory.Typing.AnchoredSortable

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.subprofile {value bound : Profile n}
    (hsub : ∀ atom ∈ value.atoms, atom ∈ bound.atoms)
    (h : TypeRelated env U registry Γ left right bound) :
    TypeRelated env U registry Γ left right value := by
  apply TypeRelated.of_singletons
  intro atom ha
  exact h.singleton (hsub atom ha)

private theorem compose_atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (lower : SupportLaws env U registry n)
    (dataLaws : RankedData.LowerEquality env U registry (relations env U registry n))
    {Γ : List VExpr} {left middle right : VExpr}
    {atom : Atom (n + 1)} {support other : Profile (n + 1)}
    (minimal : AtomMinimal atom support)
    (typed : (Profile.singleton atom).HasType other)
    (first : TypeRelated env U registry Γ left middle support)
    (second : TypeRelated env U registry Γ middle right other) :
    TypeRelated env U registry Γ left right support := by
  cases minimal with
  | @sort _ atom relevant sortable =>
    obtain ⟨s, hs⟩ := TypeRelated.sort_of_sortable henv sortable typed second
    intro Δ ρ future a ha
    have he : a = AtomData.sort relevant := List.mem_singleton.mp ha
    subst a
    exact (first Δ ρ future _ (List.mem_singleton_self _)).compose henv
      (hs Δ ρ future _ (List.mem_singleton_self _))
  | family originalTyped =>
    have member := originalTyped.family_cover_mem typed
    intro Δ ρ future a ha
    cases List.mem_singleton.mp ha
    obtain ⟨before⟩ := first Δ ρ future _ (List.mem_singleton_self _)
    obtain ⟨after⟩ := second Δ ρ future _ (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact before.trans henv dataLaws after
  | @fn _ domain result A B key output hi ho hd =>
    obtain ⟨A₂, B₂, domain₂, rows₂, result₂, hm₂, _, _, input₂, row₂, output₂⟩ :=
      typed.fn_inv (List.mem_singleton_self _)
    change Profile n at domain₂ result₂
    intro Δ ρ future atom ha
    have he : atom = (AtomData.pi (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) [(key.rename ρ, result.rename ρ)] : Atom (n + 1)) :=
      List.mem_singleton.mp ha
    subst atom
    obtain ⟨display₁⟩ := first Δ ρ future _ (List.mem_singleton_self _)
    have hm : Atom.rename (n := n + 1) ρ (.pi A₂ B₂ domain₂ rows₂) ∈ (other.rename ρ).atoms :=
      List.mem_map_of_mem hm₂
    obtain ⟨display₂⟩ := second Δ ρ future _ hm
    have hr : (key.rename ρ, result₂.rename ρ) ∈ Rows.rename ρ rows₂ :=
      List.mem_map_of_mem row₂
    exact PiWitness.minimalCompose henv lower.compose lower.transport
      (hi.rename ρ) (ho.rename ρ)
      (Profile.rename_hasType_iff.mpr input₂)
      (Profile.rename_hasType_iff.mpr output₂) hr display₁ display₂
  | @pad _ atom support minimal =>
    change (Profile.singleton atom).pad.HasType other at typed
    have ht : (Profile.singleton atom).HasType other.down := typed.pad_inv
    have hfirst : TypeRelated env U registry Γ left middle support :=
      (TypeRelated.pad_iff henv).mp first
    exact TypeRelated.pad henv
      (lower.compose _ _ _ _ _ _ _ minimal ht hfirst (second.down henv))

/-- The successor composition law discharges each Pi constructor using only
the already constructed lower rank. A selected part is extracted by literal
membership, never by assuming semantic restriction along intrinsic `≤`. -/
theorem SupportLaws.succ_compose
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (lower : SupportLaws env U registry n)
    (dataLaws : RankedData.LowerEquality env U registry (relations env U registry n))
    (Γ : List VExpr) (left middle right : VExpr)
    (value support other : Profile (n + 1))
    (minimal : Minimal value support) (typed : value.HasType other)
    (first : TypeRelated env U registry Γ left middle support)
    (second : TypeRelated env U registry Γ middle right other) :
    TypeRelated env U registry Γ left right support := by
  apply TypeRelated.of_singletons
  intro typeAtom htype
  obtain ⟨atom, ha, part, hpart, hm, hsub⟩ := minimal.support_origin_subset htype
  exact (compose_atom henv lower dataLaws hpart (typed.singleton_of_mem ha)
    (first.subprofile hsub) second).singleton hm

end Lean4Lean.AnchoredSemantics
