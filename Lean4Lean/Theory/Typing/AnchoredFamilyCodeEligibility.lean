import Lean4Lean.Theory.Typing.AnchoredFamilyCodeShape
import Lean4Lean.Theory.Typing.AnchoredValueDataEligibility
import Batteries.Tactic.OpenPrivate

/-! Original family certificates plus actual data eligibility force every
value demand on a field-free unindexed family to be empty, at every rank.
This uses the exact certificate support rather than erasing result-type needs. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private AtomTyped checks from Lean4Lean.Theory.Typing.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- The support can be a union of family atoms at different padding depths.
No literal singleton or chosen rank is assumed. -/
theorem FamilyCodeProfile.unitLike_empty
    {env : VEnv} {name : Name} {info : VProjectionInfo}
    (henv : env.Ordered) (registered : env.projections name info)
    (unindexed : info.nindices = 0) (noFields : info.numFields = 0)
    {value support : Profile n}
    (shape : FamilyCodeProfile name support)
    (typed : value.HasType support)
    (eligible : ∀ atom ∈ value.atoms, ValueDataEligible env atom) : value = .empty := by
  induction n with
  | zero =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    obtain ⟨type, present, _⟩ := typed atom member
    exact shape type present
  | succ n ih =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    obtain ⟨type, present, compatible⟩ := typed.2.2 atom member
    have original := shape type present
    have allowed := eligible atom member
    cases type with
    | sort | fn | pi | ctor | record => exact original
    | family family =>
      change family.name = name at original
      cases atom with
      | ctor data =>
        change data.family = family at compatible
        change ∀ other, env.projections data.family.name other → other.nindices ≠ 0 at allowed
        rw [compatible, original] at allowed
        exact allowed info registered unindexed
      | record data =>
        change data.family = family at compatible
        obtain ⟨other, declaration, entry, _, bound, _⟩ := allowed
        rw [compatible, original] at declaration
        cases henv.projections_unique registered declaration
        omega
      | sort | fn | pi | pad | family => cases compatible
    | pad type =>
      cases atom with
      | pad atom =>
        have empty := ih
          (show FamilyCodeProfile name (.singleton type) from fun _ hm =>
            (List.mem_singleton.mp hm) ▸ original)
          compatible
          (show ∀ a ∈ (Profile.singleton atom).atoms, ValueDataEligible env a from
            fun _ hm => (List.mem_singleton.mp hm) ▸ allowed)
        cases empty
      | sort | fn | pi | family | ctor | record => cases compatible

end Lean4Lean.AnchoredSource.Adapted
