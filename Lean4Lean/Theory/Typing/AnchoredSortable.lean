import Lean4Lean.Theory.Typing.AnchoredPadding

/-! A sortable nonempty value demand forces an actual universe observation
of any semantic type support that types it. Explicit padding is reflected
before applying the smaller-rank argument; no head inversion is assumed.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem sort_succ
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right : VExpr} {n : Nat} {relevant : Bool}
    (H : TypeRelated env U registry Γ left right (Profile.sort (n := n) relevant)) :
    TypeRelated env U registry Γ left right (Profile.sort (n := n + 1) relevant) := by
  intro Δ ρ future atom hmem
  have heq : atom = .sort relevant := List.mem_singleton.mp hmem
  subst atom
  cases n <;> exact H Δ ρ future _ (List.mem_singleton_self _)

/-- A single demand typed both at a universe profile and at `bound` forces
`bound`'s actual related type codes to expose related universes. The resulting
relevance can depend on the cover; it need not equal the input sort flag. -/
theorem TypeRelated.sort_of_sortable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right : VExpr} {n : Nat} {atom : Atom n}
    {bound : Profile n} {relevant : Bool} (henv : env.Ordered)
    (hsort : (Profile.singleton atom).HasType (.sort relevant))
    (hbound : (Profile.singleton atom).HasType bound)
    (H : TypeRelated env U registry Γ left right bound) :
    ∃ s : Bool, TypeRelated env U registry Γ left right (Profile.sort (n := n) s) := by
  induction n with
  | zero =>
    obtain ⟨cover, hmem, htrue⟩ := hbound atom (List.mem_singleton_self _)
    change cover = true at htrue
    subst cover
    exact ⟨true, H.singleton hmem⟩
  | succ n ih =>
    cases atom with
    | pad lower =>
      have hs : (Profile.singleton lower).HasType (Profile.sort relevant) := by
        have hp : (Profile.singleton lower).pad.HasType (.sort relevant) := hsort
        simpa only [Profile.down_sort] using hp.pad_inv
      have hb : (Profile.singleton lower).HasType bound.down := by
        have hp : (Profile.singleton lower).pad.HasType bound := hbound
        exact hp.pad_inv
      obtain ⟨s, h⟩ := ih hs hb (TypeRelated.down henv H)
      exact ⟨s, sort_succ h⟩
    | fn | ctor | record =>
      obtain ⟨cover, hmem, htyped⟩ := hsort.2.2 _ (List.mem_singleton_self _)
      have heq : cover = .sort relevant := List.mem_singleton.mp hmem
      subst cover
      contradiction
    | sort | pi | family =>
      obtain ⟨cover, hmem, htyped⟩ := hbound.2.2 _ (List.mem_singleton_self _)
      cases cover with
      | sort s => exact ⟨s, H.singleton hmem⟩
      | fn | pi | pad | family | ctor | record => contradiction

end Lean4Lean.AnchoredSemantics
