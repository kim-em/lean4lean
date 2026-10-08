import Lean4Lean.Theory.Typing.Confluence.HeadRegistryScope
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.Confluence.QuotPrefixTyping
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift

/-! Canonical dispatch need not retain native descriptors with no owned rules.
Removing precisely those entries preserves every computational equation and
makes the native-table condition for rigid-head observations constructible. -/
namespace Lean4Lean.CanonicalHead
open VEnv InductiveSignature
set_option Elab.async false

/-- An empty recursor has a declaration but no native equation to dispatch.
Keep all entries that own at least one constructor rule. -/
def Registry.removeEmptyNatives (registry : Registry) : Registry :=
  { registry with recursors := fun name => do
      let data ← registry.recursors name
      if data.constructorIndices.isEmpty then none else some data }

theorem Registry.removeEmptyNatives_lookup
    (registry : Registry) :
    registry.removeEmptyNatives.recursors name = some data ↔
      registry.recursors name = some data ∧ data.constructorIndices ≠ [] := by
  cases lookup : registry.recursors name with
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
    (registry : Registry) (lookup : registry.recursors name = some data)
    {index : Fin data.schema.signature.constructors.size}
    (owner : data.schema.signature.constructors[index].owner = data.owner) :
    registry.removeEmptyNatives.recursors name = some data := by
  apply registry.removeEmptyNatives_lookup.mpr
  refine ⟨lookup, ?_⟩
  have member := RecursorData.mem_constructorIndices.mpr owner
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
    (registered : ∀ name data, registry.recursors name = some data →
      RecursorRegistered env data ∧ data.name = name)
    (rigid : env.Rigid name) : registry.removeEmptyNatives.recursors name = none := by
  cases lookup : registry.removeEmptyNatives.recursors name with
  | none => rfl
  | some data =>
    obtain ⟨original, nonempty⟩ := registry.removeEmptyNatives_lookup.mp lookup
    obtain ⟨sound, nameEq⟩ := registered name data original
    obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    have owner := RecursorData.mem_constructorIndices.mp member
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
    (recursors : ∀ name data, registry.recursors name = some data →
      RecursorRegistered env data ∧ data.name = name)
    (quotient : registry.quotient = true → env.defeqs quotDefEq)
    (rigid : env.Rigid name) : CanonicalDataHead.HeadInert registry.removeEmptyNatives name := by
  refine ⟨?_, registry.removeEmptyNatives_none_of_rigid recursors rigid, ?_⟩
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

/-! Priority exclusions follow from real installation freshness and equation
ownership. Empty native descriptors are removed before asserting computational
head disjointness. -/
namespace Lean4Lean.VEnv
open InductiveSignature RecursorData
open private declaration_le from Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
set_option Elab.async false
variable {env : VEnv} {table : Name → Option RecursorData}

/-- An actual quotient declaration supplies its constants and rule. Its head
cannot also occur in the actual native table, before or after that declaration. -/
theorem NativeRegistryHistory.quotient
    (history : NativeRegistryHistory env declarations table)
    (member : .quot ∈ declarations) :
    QuotRegistered env ∧ table ``Quot.lift = none := by
  induction history with
  | empty => cases member
  | decl previous declaration ih =>
    rename_i d current extended oldDeclarations oldTable
    rcases List.mem_cons.mp member with same | member
    · cases same
      cases declaration with
      | quot ready installed =>
        refine ⟨.of_addQuot installed, ?_⟩
        cases lookup : oldTable ``Quot.lift with
        | none => rfl
        | some data =>
          obtain ⟨registered, nameEq⟩ := previous.registered lookup
          obtain ⟨value, present⟩ := registered.constant_exists
          rw [nameEq] at present
          simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at installed
          obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := installed
          have retained := ((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)).constants present
          simp only [VEnv.addConst, retained] at hc
          cases hc
    · obtain ⟨registered, absent⟩ := ih member
      exact ⟨registered.mono (declaration_le declaration), absent⟩
  | native previous original compiled formed eliminatorsWF installed compilation specializations
      below ih =>
    have oldMember : VDecl.quot ∈ _ := (List.mem_cons.mp member).resolve_left (by intro h; cases h)
    obtain ⟨registered, absent⟩ := ih oldMember
    refine ⟨registered.mono (declaration_le (.induct original
      (.intro original compiled formed eliminatorsWF installed))), ?_⟩
    cases lookup : installEntries _ _ ``Quot.lift with
    | none => rfl
    | some data =>
      have oldLookup := compilation.installEntries_previous installed registered.lift lookup
      rw [absent] at oldLookup
      cases oldLookup
  | eliminators _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨registered, absent⟩ := ih member
    exact ⟨registered.mono VEnv.addEliminator_le, absent⟩
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨registered, absent⟩ := ih member
    exact ⟨registered.mono VEnv.addProjections_le, absent⟩

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalHead
open VEnv InductiveSignature
variable {env : VEnv} {registry : Registry}

/-- An owned constructor equation precludes a transparent definition at the
same selected name. The real equation supplies the exclusion witness. -/
theorem Registry.removeEmptyNatives_notDefinition
    (formed : env.WF)
    (definitions : ∀ name value, registry.definitions name = some value →
      DefinitionRegistered env value ∧ value.name = name)
    (recursors : ∀ name data, registry.recursors name = some data →
      RecursorRegistered env data ∧ data.name = name)
    (lookup : registry.removeEmptyNatives.recursors name = some data) :
    registry.removeEmptyNatives.definitions name = none := by
  obtain ⟨original, nonempty⟩ := registry.removeEmptyNatives_lookup.mp lookup
  obtain ⟨registered, nameEq⟩ := recursors name data original
  obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨equation, generated⟩ := registered.equation_exists index
  have owner := RecursorData.mem_constructorIndices.mp member
  change registry.definitions name = none
  cases definition : registry.definitions name with
  | none => rfl
  | some value =>
    obtain ⟨definitionRegistered, definitionName⟩ := definitions name value definition
    apply False.elim
    apply definitionRegistered.not_constructor_equation formed (registered.equation_present generated)
      (ctorName := data.ruleConstructor index)
    · exact (VExpr.equationHead_eq _).trans
        ((registered.equation_head owner generated).trans (by rw [nameEq, definitionName]))
    · exact registered.equation_major generated

end Lean4Lean.CanonicalHead
