import Lean4Lean.Theory.Typing.NativeRegistryPrefix
import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance
import Lean4Lean.Theory.Typing.SourceConstantProvenance

/-! Existing source constants force transparent definitions back into the
actual earlier history. No agreement assumption on a semantic registry's
definition table is needed: actual equation registration identifies the value. -/
namespace Lean4Lean.VEnv
open VExpr
variable {base header installed : VEnv} {values : List VDefVal}
  {name : Name} {constant : VConstant} {value : VDefVal} {old : Name → Option VDefVal}
open private addConsts_as_values from Lean4Lean.Theory.Typing.NativeConstructorRigidity

private theorem installDefinitions_previous
    (headers : base.addConsts values = some header)
    (present : base.constants name = some constant)
    (lookup : installDefinitions old values name = some value) : old name = some value := by
  unfold installDefinitions at lookup
  cases selected : values.find? (fun entry => entry.name == name) with
  | none => simpa only [selected, Option.orElse_none] using lookup
  | some entry =>
    have fresh := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ headers)
      entry.toVConstVal (List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some selected, rfl⟩)
    have nameEq : entry.name = name := by
      simpa only [beq_iff_eq] using List.find?_some selected
    change base.constants entry.name = none at fresh
    rw [nameEq, present] at fresh
    cases fresh

private theorem declaration_previous (original : VDecl.WF base declaration installed)
    (present : base.constants name = some constant)
    (lookup : installDefinitions old declaration.definitionEntries name = some value) :
    old name = some value := by
  cases original with
  | «def» _ headers =>
    exact installDefinitions_previous (by simpa [VEnv.addConsts, VDecl.definitionEntries] using headers) present lookup
  | mutualDef _ headers _ => exact installDefinitions_previous headers present lookup
  | «axiom» | «opaque» | «example» | quot | induct => exact lookup

namespace NativeRegistryHistory.Prefix
variable {base env : VEnv} {before declarations : List VDecl}
  {old table : Name → Option InductiveSignature.NativeRecursorData}
  {first : NativeRegistryHistory base before old} {last : NativeRegistryHistory env declarations table}

theorem previous_definition (continuation : Prefix first last)
    (present : base.constants name = some constant)
    (lookup : definitionRegistry declarations name = some value) :
    definitionRegistry before name = some value := by
  induction continuation with
  | refl => exact lookup
  | decl continuation declaration ih =>
    exact ih (declaration_previous declaration (continuation.le.constants present) lookup)
  | native _ _ _ _ _ _ _ _ ih => exact ih lookup
  | eliminators _ _ _ _ _ _ _ ih => exact ih lookup
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih lookup

end NativeRegistryHistory.Prefix

private theorem definition_eq {left right : VDefVal} (equal : left.toDefEq = right.toDefEq) : left = right := by
  cases left with
  | mk leftConstant leftBody =>
    cases right with
    | mk rightConstant rightBody =>
      cases leftConstant with
      | mk leftInfo leftName =>
        cases rightConstant with
        | mk rightInfo rightName =>
          cases leftInfo
          cases rightInfo
          simp only [VDefVal.toDefEq, VDefEq.mk.injEq, VExpr.const.injEq] at equal
          rcases equal with ⟨rfl, ⟨rfl, _⟩, rfl, rfl⟩
          rfl

/-- Final registration itself identifies the exact history-table entry. -/
theorem WF'.definitionLookup {env : VEnv} {declarations : List VDecl}
    (history : env.WF' declarations) (registered : DefinitionRegistered env value) :
    definitionRegistry declarations value.name = some value := by
  obtain ⟨stored, lookup, equation⟩ := history.definitionRegistry_of_constantEquation registered.2 rfl
  have same := definition_eq equation
  cases same
  exact lookup

namespace DefinitionDeclarationOrigin

theorem bodyConstants (origin : DefinitionDeclarationOrigin env declarations value) :
    value.value.ConstantsIn origin.stage.header := origin.bodyStrong.constantsIn.1

theorem typeConstants (origin : DefinitionDeclarationOrigin env declarations value) :
    value.type.ConstantsIn origin.base := by
  obtain ⟨_, formation⟩ := origin.typeStrong
  exact formation.constantsIn.1

end DefinitionDeclarationOrigin
end Lean4Lean.VEnv
