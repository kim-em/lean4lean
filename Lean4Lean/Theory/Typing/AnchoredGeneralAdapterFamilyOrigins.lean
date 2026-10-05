import Lean4Lean.Theory.Typing.AnchoredCodeActionFamilyOrigins
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterFunction

/-! Generalized adapters retain finite family origins through normalized
endpoints. Descriptor equality is replaced by explicit family-code paths. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyAtomProperty.shift_iff
    {property : {n : Nat} → FamilyData (Profile n) → Prop} (atom : Atom n) :
    FamilyAtomProperty property (AdapterNormal.shiftAtom atom) ↔ FamilyAtomProperty property atom := by
  cases n with
  | zero => rfl
  | succ n => cases atom <;> rfl

theorem FamilyAtomProperty.normal_iff
    {property : {n : Nat} → FamilyData (Profile n) → Prop} (atom : Atom n) :
    FamilyAtomProperty property (AdapterNormal.atom atom) ↔ FamilyAtomProperty property atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | pad atom =>
      change FamilyAtomProperty property (AdapterNormal.shiftAtom (AdapterNormal.atom atom)) ↔ _
      rw [FamilyAtomProperty.shift_iff]
      exact ih atom
    | sort | fn | pi | family | ctor | record => rfl

theorem FamilyAtomProperty.raise_iff
    {property : {n : Nat} → FamilyData (Profile n) → Prop} (bound : n ≤ N) (atom : Atom n) :
    FamilyAtomProperty property (raiseAtom N bound atom) ↔ FamilyAtomProperty property atom := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; rw [raiseAtom_self]
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact ih small

theorem FamilyOccurrence.normal_eq (found : FamilyOccurrence family atom) :
    AdapterNormal.atom atom = atom := by
  induction found with
  | here => rfl
  | pad found ih =>
    change AdapterNormal.shiftAtom (AdapterNormal.atom _) = _
    rw [ih]
    cases found <;> rfl

theorem FamilyOccurrence.raise (bound : n ≤ N)
    {atom : Atom n} (found : FamilyOccurrence family atom) :
    FamilyOccurrence family (raiseAtom N bound atom) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact found
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseAtom_self] using found
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact .pad (ih small)

theorem FamilyOccurrence.notFn {atom : Atom (m + 1)}
    (found : FamilyOccurrence family atom) {key : Key m} {output : Atom m} :
    atom ≠ .fn key output := by
  cases found <;> intro equal <;> cases equal

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

theorem GeneralAtomAdapter.familyProperty
    {a b : Atom n} (adapter : GeneralAtomAdapter env U registry target a b)
    {property : {n : Nat} → FamilyData (Profile n) → Prop}
    (padFamily : ∀ {n} {family : FamilyData (Profile n)}, property family → property family.pad)
    (origin : FamilyAtomProperty property a) : FamilyAtomProperty property b := by
  match n, a, b, adapter with
  | _, _, _, .refl _ => exact origin
  | _, _, _, .code action _ =>
    exact action.familyProperty (property := property) padFamily (fun atom member => by
      cases List.mem_singleton.mp member
      exact origin) _ (List.mem_singleton_self _)
  | _ + 1, _, _, .fn .. => trivial
  | _ + 1, _, _, .pad child => exact GeneralAtomAdapter.familyProperty child padFamily origin
termination_by n

theorem GeneralNormalAtomAdapter.familyProperty
    {a b : Atom n} (adapter : GeneralNormalAtomAdapter env U registry target a b)
    {property : {n : Nat} → FamilyData (Profile n) → Prop}
    (padFamily : ∀ {n} {family : FamilyData (Profile n)}, property family → property family.pad)
    (origin : FamilyAtomProperty property a) : FamilyAtomProperty property b :=
  (FamilyAtomProperty.normal_iff b).mp
    (GeneralAtomAdapter.familyProperty adapter padFamily ((FamilyAtomProperty.normal_iff a).mpr origin))

theorem GeneralNormalProfileAdapter.familyProperty
    {source requested : Profile n}
    (adapter : GeneralNormalProfileAdapter env U registry target source requested)
    {property : {n : Nat} → FamilyData (Profile n) → Prop}
    (padFamily : ∀ {n} {family : FamilyData (Profile n)}, property family → property family.pad)
    (origins : FamilyProfileProperty property source) : FamilyProfileProperty property requested := by
  intro atom member
  obtain ⟨normal, present, ⟨entry⟩⟩ := adapter.origin (List.mem_map_of_mem member)
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp present
  exact GeneralNormalAtomAdapter.familyProperty entry padFamily (origins original originalMember)

theorem GeneralNormalProfileAdapter.familyOrigins
    {source requested : Profile n}
    (adapter : GeneralNormalProfileAdapter env U registry target source requested) :
    FamilyProfileProperty (FamilyProfileOrigin source) requested := by
  apply GeneralNormalProfileAdapter.familyProperty adapter
  · rintro n family ⟨k, original, atom, member, found, path⟩
    exact ⟨k, original, atom, member, found, .pad path⟩
  · exact (SortableCodeAction.id (env := env) (U := U) (registry := registry)
      (target := target) (relevant := true) (profile := source)).familyOrigins

theorem GeneralNormalProfileAdapter.familyOrigin
    {source requested : Profile (n + 1)} {family : FamilyData (Profile n)}
    (adapter : GeneralNormalProfileAdapter env U registry target source requested)
    (member : AtomData.family family ∈ requested.atoms) : FamilyProfileOrigin source family :=
  GeneralNormalProfileAdapter.familyOrigins adapter _ member

theorem GeneralNormalAtomAdapter.family_not_fn
    {family : FamilyData (Profile n)} {key : Key m} {output : Atom m}
    (bound : n + 1 ≤ m + 1)
    (adapter : GeneralNormalAtomAdapter env U registry target
      (raiseAtom (m + 1) bound (.family family)) (.fn key output)) : False := by
  have found := (FamilyOccurrence.here family).raise bound
  change GeneralAtomAdapter env U registry target (n := m + 1) (AdapterNormal.atom _)
    (.fn (AdapterNormal.key key) (AdapterNormal.atom output)) at adapter
  rw [found.normal_eq] at adapter
  obtain ⟨key, output, equal, _, _⟩ := adapter.fn_inv
  exact found.notFn equal

theorem GeneralNormalAtomAdapter.fn_not_family
    {family : FamilyData (Profile n)} {key : Key m} {output : Atom m}
    (bound : n + 1 ≤ m + 1)
    (adapter : GeneralNormalAtomAdapter env U registry target (n := m + 1)
      (.fn key output) (raiseAtom (m + 1) bound (.family family))) : False := by
  have result := GeneralNormalAtomAdapter.familyProperty adapter
    (property := fun {_} _ => False) (fun impossible => impossible) True.intro
  exact (FamilyAtomProperty.raise_iff bound (.family family)).mp result

end Lean4Lean.AnchoredSemantics
