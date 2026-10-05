import Lean4Lean.Theory.Typing.CanonicalHeadRegistry
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection

/-! Canonical dispatch need not retain native descriptors with no owned rules.
Removing precisely those entries preserves every computational equation and
makes the native-table condition for rigid-head observations constructible. -/
namespace Lean4Lean.CanonicalHead
open VEnv InductiveSignature
set_option Elab.async false

/-- An empty recursor has a declaration but no native equation to dispatch.
Keep all entries that own at least one constructor rule. -/
def Registry.removeEmptyNatives (registry : Registry) : Registry :=
  { registry with natives := fun name => do
      let data ← registry.natives name
      if data.constructorIndices.isEmpty then none else some data }

theorem Registry.removeEmptyNatives_lookup
    (registry : Registry) :
    registry.removeEmptyNatives.natives name = some data ↔
      registry.natives name = some data ∧ data.constructorIndices ≠ [] := by
  cases lookup : registry.natives name with
  | none => simp [removeEmptyNatives, lookup]
  | some selected =>
    by_cases empty : selected.constructorIndices = []
    · simp [removeEmptyNatives, lookup, empty]
      rintro rfl
      exact empty
    · simp [removeEmptyNatives, lookup, empty]
      rintro rfl
      exact empty

/-- Every actual owned equation keeps its exact descriptor and lookup. -/
theorem Registry.removeEmptyNatives_preserves_owned
    (registry : Registry) (lookup : registry.natives name = some data)
    {index : Fin data.schema.signature.constructors.size}
    (owner : data.schema.signature.constructors[index].owner = data.owner) :
    registry.removeEmptyNatives.natives name = some data := by
  apply registry.removeEmptyNatives_lookup.mpr
  refine ⟨lookup, ?_⟩
  have member := NativeRecursorData.mem_constructorIndices.mpr owner
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

theorem Registry.Scoped.removeEmptyNatives
    {registry : Registry}
    (hscoped : registry.Scoped) : registry.removeEmptyNatives.Scoped := by
  refine ⟨hscoped.definition, ?_, ?_, hscoped.caseEquation⟩
  · intro name data lookup
    exact hscoped.native name data (registry.removeEmptyNatives_lookup.mp lookup).1
  · intro name data lookup
    exact hscoped.nativeEquation name data (registry.removeEmptyNatives_lookup.mp lookup).1

/-- A rigid name cannot retain a nonempty native descriptor in a sound table.
The argument uses an actual installed owned equation, not the false claim that
every native declaration has a computational rule. -/
theorem Registry.removeEmptyNatives_none_of_rigid
    (registry : Registry)
    (registered : ∀ name data, registry.natives name = some data →
      NativeRecursorRegistered env data ∧ data.name = name)
    (rigid : env.Rigid name) : registry.removeEmptyNatives.natives name = none := by
  cases lookup : registry.removeEmptyNatives.natives name with
  | none => rfl
  | some data =>
    obtain ⟨original, nonempty⟩ := registry.removeEmptyNatives_lookup.mp lookup
    obtain ⟨sound, nameEq⟩ := registered name data original
    obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    have owner := NativeRecursorData.mem_constructorIndices.mp member
    obtain ⟨equation, selected⟩ := sound.equation_exists index
    have head := sound.equation_head owner selected
    rw [nameEq] at head
    exact False.elim (rigid equation (sound.equation_present selected) _ head)

/-- Sound registration, including the enabled quotient rule, supplies the
concrete inertness required by the rigid-family observation grammar. -/
theorem Registry.removeEmptyNatives_headInert
    (registry : Registry)
    (definitions : ∀ name value, registry.definitions name = some value →
      DefinitionRegistered env value ∧ value.name = name)
    (natives : ∀ name data, registry.natives name = some data →
      NativeRecursorRegistered env data ∧ data.name = name)
    (quotient : registry.quotient = true → env.defeqs quotDefEq)
    (rigid : env.Rigid name) : CanonicalDataHead.HeadInert registry.removeEmptyNatives name := by
  refine ⟨?_, registry.removeEmptyNatives_none_of_rigid natives rigid, ?_⟩
  · change registry.definitions name = none
    cases lookup : registry.definitions name with
    | none => rfl
    | some value =>
      obtain ⟨sound, nameEq⟩ := definitions name value lookup
      apply False.elim
      apply rigid value.toDefEq sound.2 (VLevel.params value.uvars)
      change VExpr.const value.name (VLevel.params value.uvars) = _
      rw [nameEq]
  · change registry.quotient = false ∨ name ≠ ``Quot.lift
    cases enabled : registry.quotient with
    | false => exact Or.inl rfl
    | true =>
      apply Or.inr
      intro same
      subst name
      exact rigid quotDefEq (quotient enabled) _ rfl

end Lean4Lean.CanonicalHead
