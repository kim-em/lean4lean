import Lean4Lean.Theory.Typing.TelescopeTransport
import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.CanonicalEq
import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.ProjectionCornerSubst
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness

/-! # Field types of the one-family view of a case schema

The constructors of the one-family view `schema.view owner` of a case schema have only external
fields, whose types are the constructor's field types in the schema's signature. -/

namespace Lean4Lean
namespace InductiveSignature

theorem fieldTypes_external (s : InductiveSignature) {c : Constructor s.families.size}
    {l : List VExpr} (h : c.fields = l.map Field.external) : s.fieldTypes c = l := by
  simp only [fieldTypes, h]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, fieldType]

namespace CaseSchema
variable {schema : CaseSchema} {owner : Fin schema.signature.families.size}

theorem view_fieldTypes_case (c : Constructor schema.signature.families.size) :
    (schema.view owner).fieldTypes (schema.caseConstructor c) = schema.signature.fieldTypes c :=
  fieldTypes_external _ rfl

theorem caseConstructor_recursiveFields (c : Constructor schema.signature.families.size) :
    Instance.recursiveFields (s := schema.view owner) (schema.caseConstructor c) = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  change field ∈ (schema.signature.fieldTypes c).map Field.external at hfield
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hfield
  rfl

end CaseSchema

end InductiveSignature
end Lean4Lean
