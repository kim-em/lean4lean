import Lean4Lean.Theory.Typing.NativeDeclarationProvenance
import Lean4Lean.Theory.Typing.CanonicalRegistryRigidHeads
import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Lean4Lean.Theory.Typing.DefinitionHeadExclusivity

/-! Priority exclusions follow from real installation freshness and equation
ownership. Empty native descriptors are removed before asserting computational
head disjointness. -/
namespace Lean4Lean.VEnv
open InductiveSignature NativeRecursorData
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory
set_option Elab.async false
variable {env : VEnv} {table : Name → Option NativeRecursorData}

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
  | eliminators _ _ _ _ _ _ _ _ ih =>
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
    (natives : ∀ name data, registry.natives name = some data →
      NativeRecursorRegistered env data ∧ data.name = name)
    (lookup : registry.removeEmptyNatives.natives name = some data) :
    registry.removeEmptyNatives.definitions name = none := by
  obtain ⟨original, nonempty⟩ := registry.removeEmptyNatives_lookup.mp lookup
  obtain ⟨registered, nameEq⟩ := natives name data original
  obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨equation, generated⟩ := registered.equation_exists index
  have owner := NativeRecursorData.mem_constructorIndices.mp member
  change registry.definitions name = none
  cases definition : registry.definitions name with
  | none => rfl
  | some value =>
    obtain ⟨definitionRegistered, definitionName⟩ := definitions name value definition
    apply False.elim
    apply definitionRegistered.not_constructor_equation formed (registered.equation_present generated)
      (ctorName := data.ruleConstructor index)
    · exact (VExpr.nativeEquationHead_eq _).trans
        ((registered.equation_head owner generated).trans (by rw [nameEq, definitionName]))
    · exact registered.equation_major generated

end Lean4Lean.CanonicalHead
