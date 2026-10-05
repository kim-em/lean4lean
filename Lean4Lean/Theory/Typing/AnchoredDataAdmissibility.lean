import Lean4Lean.Theory.Typing.AnchoredAdapters
import Batteries.Tactic.OpenPrivate

/-! Local consequences and limits of an extensional data-demand policy.
This file does not change the source grammar or claim admissibility for its
existing unrestricted observers. In particular, function adapters can add
arbitrary admitted input demands, so forward closure needs an extra guard. -/
namespace Lean4Lean.AnchoredProfiles
open VExpr VEnv
open private AtomTyped checks from Lean4Lean.Theory.Typing.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- A necessary local condition for extensional value demands. Constructor
tags belong only to families without the structure eta rule. A record demand
observes an actual field with a nonempty input. Family type codes remain
available; hereditary conditions on their requests are a separate obligation. -/
def DataTagEligible (env : VEnv) (registry : CanonicalHead.Registry) : Atom (n + 1) → Prop
  | .ctor data => ∀ info, env.projections data.family.name info → info.nindices ≠ 0
  | .record data => ∃ info, registry.projections data.family.name = some info ∧
      ∃ entry ∈ data.fields, entry.1 < info.numFields ∧ Profile.Nonempty entry.2.input
  | _ => True

/-- At an exact field-free family support, the proposed local data policy
really does force the value demand to be empty. No type-code demand is erased
to establish this fact. -/
theorem Profile.HasType.unitLikeEligible_empty
    {env : VEnv} {registry : CanonicalHead.Registry} {family : FamilyData (Profile n)}
    {info : VProjectionInfo}
    (registered : env.projections family.name info)
    (selected : registry.projections family.name = some info)
    (unindexed : info.nindices = 0) (noFields : info.numFields = 0)
    {value : Profile (n + 1)}
    (typed : value.HasType (.singleton (.family family)))
    (eligible : ∀ atom ∈ value.atoms, DataTagEligible env registry atom) :
    value = .empty := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro atom member
  obtain ⟨type, present, same⟩ := typed.2.2 atom member
  cases List.mem_singleton.mp present
  cases atom with
  | ctor data =>
    change data.family = family at same
    have allowed := eligible _ member
    change ∀ other, env.projections data.family.name other → other.nindices ≠ 0 at allowed
    rw [same] at allowed
    exact allowed info registered unindexed
  | record data =>
    change data.family = family at same
    obtain ⟨other, lookup, entry, present, bound, _⟩ := eligible _ member
    rw [same, selected] at lookup
    cases Option.some.inj lookup
    omega
  | sort | fn | pi | pad | family => cases same

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Existing adapters can strengthen an empty function input to any
admitted input. Hence an admissibility policy on nested input demands cannot
be preserved forwards by all current adapters without an additional premise. -/
theorem AtomAdapter.emptyInput_strengthen
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {domain anchor : VExpr} {input : Profile n} {output : Atom n}
    (admitted : Admitted env U registry Γ (⟨domain, anchor, input⟩ : Key n) anchor anchor) :
    Nonempty (AtomAdapter env U registry Γ (n := n + 1)
      (.fn (⟨domain, anchor, .empty⟩ : Key n) output)
      (.fn (⟨domain, anchor, input⟩ : Key n) output)) := by
  exact ⟨.fn (.input (.supplied admitted) (.nil input)) (.refl output)⟩

/-- A genuine constructor admission for a unit-like family is already a
counterexample to unrestricted forward preservation of eligible inputs.
This obstruction occurs inside function domains, even when the common
output is the permitted sort observation. -/
theorem DataTagEligible.not_adapter_closed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {demand : ConstructorData (Profile n)} {info : VProjectionInfo}
    (registered : env.projections demand.family.name info)
    (unindexed : info.nindices = 0)
    {domain anchor : VExpr}
    (admitted : Admitted env U registry Γ
      (⟨domain, anchor, .singleton (.ctor demand)⟩ : Key (n + 1)) anchor anchor) :
    ¬ (∀ (old new : Key (n + 1)),
      Nonempty (AtomAdapter env U registry Γ (n := n + 2)
        (.fn old (.sort true)) (.fn new (.sort true))) →
      (∀ atom ∈ old.input.atoms, DataTagEligible env registry atom) →
      (∀ atom ∈ new.input.atoms, DataTagEligible env registry atom)) := by
  intro preserves
  have contradiction := preserves ⟨domain, anchor, .empty⟩
    ⟨domain, anchor, .singleton (.ctor demand)⟩
    (AtomAdapter.emptyInput_strengthen admitted)
    (fun _ member => nomatch member) (.ctor demand) (List.mem_singleton_self _)
  exact contradiction info registered unindexed

end Lean4Lean.AnchoredSemantics
