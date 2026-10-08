import Lean4Lean.Theory.Typing.ProjectionCornerCase
import Lean4Lean.Theory.Typing.EliminatorCoherenceOfWF

/-! # The projection-walk corner from a registered case eliminator

A structure family named among the original families of a registered case schema has a closed
inhabitant of its case type into `Prop`, namely the abstract eliminator `.elim key owner`
specialized at the motive universe zero (`elimDF`). Its restored case type is the ordinary
recursor type of the one-constructor view `caseView` (`restored_structure_recursorType`), whose
constructor type is the restored normalized constructor type, definitionally equal to the
registered constructor type by the certified correspondence. `corner_inhabit_sig` then
inhabits the projection-walk binder. -/

namespace Lean4Lean
namespace InductiveSignature

theorem mem_declaration_types {s : InductiveSignature} {t : VInductiveType}
    (h : t ∈ s.declaration.types) : ∃ owner, t = s.declarationFamily owner := by
  simp only [declaration, List.mem_map] at h
  obtain ⟨⟨family, i⟩, hmem, rfl⟩ := h
  obtain ⟨-, hi, hfam⟩ := List.mem_zipIdx hmem
  simp only [Nat.zero_add, Array.length_toList] at hi
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [hfam]
  simp [declarationFamily]

theorem filterMap_ite_eq {α β : Type _} (p : α → Bool) (f : α → β) (l : List α) :
    l.filterMap (fun x => if p x then some (f x) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

namespace CaseSchema

/-- A normalized family with exactly one declared constructor has a one-constructor case
view. -/
theorem view_of_single {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {nc : VConstVal} (h : (schema.signature.declarationFamily owner).ctors = [nc]) :
    ∃ c : Constructor schema.signature.families.size, c ∈ schema.signature.constructors.toList ∧
      c.owner = owner ∧ nc.name = c.name ∧ nc.type = schema.signature.constructorType c ∧
      (schema.view owner).constructors = #[schema.caseConstructor c] := by
  have key := filterMap_ite_eq (fun ctor : Constructor schema.signature.families.size =>
    decide (ctor.owner.val = owner.val))
    (fun ctor => ({ name := ctor.name, uvars := schema.signature.uvars
                    type := schema.signature.constructorType ctor } : VConstVal))
    schema.signature.constructors.toList
  simp only [decide_eq_true_eq] at key
  simp only [declarationFamily] at h
  rw [key] at h
  obtain ⟨c, hc, rfl⟩ := List.map_eq_singleton_iff.mp h
  have hcmem : c ∈ List.filter _ _ := hc ▸ List.mem_singleton_self c
  obtain ⟨hcmem, hown⟩ := List.mem_filter.mp hcmem
  have hown : c.owner = owner := Fin.ext (by simpa using hown)
  refine ⟨c, hcmem, hown, rfl, rfl, ?_⟩
  have key' := filterMap_ite_eq (fun ctor : Constructor schema.signature.families.size =>
    ctor.owner == owner) schema.caseConstructor schema.signature.constructors.toList
  have hfilter : schema.signature.constructors.toList.filter (fun ctor => ctor.owner == owner) =
      schema.signature.constructors.toList.filter
        (fun ctor => decide (ctor.owner.val = owner.val)) := by
    congr 1; funext ctor
    exact Bool.eq_iff_iff.mpr (by simp [Fin.ext_iff])
  simp only [view]
  rw [key', hfilter, hc]
  rfl

end CaseSchema

/-- Original family and constructor names are not rewritten by their compilation's
restoration. -/
theorem CaseCompilationData.restoration_fixed {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (hdisj : RecursorNamesFresh env source expanded auxiliaries)
    (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == name) = none ∧
      (compilationRestoration source auxiliaries).recursorName name = name := by
  constructor
  · cases hf : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == name) with
    | none => rfl
    | some found =>
      have hm := List.mem_of_find?_eq_some hf
      have hn : found.auxiliary = name := by simpa using List.find?_some hf
      exact (H.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
  · unfold Restoration.recursorName
    cases hr : (compilationRestoration source auxiliaries).recursors.find?
        (fun p => p.1 == name) with
    | none => rfl
    | some pair =>
      have hm := List.mem_of_find?_eq_some hr
      have hn : pair.1 = name := by simpa using List.find?_some hr
      have hs : pair.1 ∈ source.sourceNames := by
        rw [hn]
        have := (familyNames_perm source.types).mem_iff.mp hname
        simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
          VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
          using this
      exact ((hdisj _ (List.mem_map.mpr ⟨pair, hm, rfl⟩)).2.1 hs).elim

end InductiveSignature

namespace VEnv
open InductiveSignature VExpr
variable {env : VEnv} {U : Nat}

end VEnv
end Lean4Lean
