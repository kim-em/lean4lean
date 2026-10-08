import Lean4Lean.Theory.Typing.EnvTables.EnvSigSyntax
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness

/-!
# The shape of generic eliminator equations

The analogue of `CompilationData.rule_shape` (T2) for the generic equations of a registered
eliminator schema: a lambda telescope `Ds` shared by both sides; the left body applies the
abstract head `.elim key owner (.param 0 :: genericLevels)` to the prefix variables (parameters,
the motive, the minors), the index expressions, and the restored constructor application whose
trailing arguments are the field variables; the right body is a minor applied to the fields.
-/

namespace Lean4Lean.EnvTables
open InductiveSignature CaseSchema

/-- The family of a declared constant's type (`familyOfType`). -/
def ctorFamily (env : VEnv) (c : Name) : Option Name :=
  (env.constants c).bind fun ci => familyOfType ci.type

theorem CtorShape.family {env : VEnv} {c : Name} {k : CtorData} (h : CtorShape env c k) :
    ctorFamily env c = some k.family := by
  obtain ⟨ci, doms, idx, hc, _, ht, _⟩ := h
  simp [ctorFamily, hc, ht, familyOfType_shape]

theorem view_ctor_name_mem {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (j : Fin schema.signature.constructors.size) (hj : schema.signature.constructors[j].owner = owner) :
    schema.signature.constructors[j].name ∈
      (schema.view owner).constructors.toList.map (·.name) := by
  simp only [CaseSchema.view, List.toList_toArray, List.map_filterMap, List.mem_filterMap]
  refine ⟨schema.signature.constructors[j], Array.mem_toList_iff.mpr (Array.getElem_mem _), ?_⟩
  have hj' : schema.signature.constructors[j.val].owner = owner := hj
  simp [hj', CaseSchema.caseConstructor]

/-- The major constructor of a generic equation of a registered schema is in the constructor
table, or it is a source constructor of the schema at a source slot whose original family is
the constructor's family. -/
theorem generic_major_origin {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ctorOf env c ≠ none ∨ (schema.originalFamilies[owner.val]? = ctorFamily env c ∧
      c ∈ (schema.view owner).constructors.toList.map (·.name)) := by
  obtain ⟨base, source, block, _, hle, hcert, _, hconsts⟩ := H.eliminator_origin hreg
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hr, hnames, hrfresh⟩ := hcert'
  obtain ⟨j, hown, e, _, hrestore⟩ := Certified.generic_major hcert hgen hdf hm
  rw [hr] at hrestore
  rcases CaseCompilationData.ctorApp_cases hdata hrfresh j hrestore with
    ⟨F, hF, hFget, c', hc', hcn, hmaj⟩ | ⟨a, ha, hge, haget, c', hc', _, hmaj⟩
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    rw [hown] at hFget
    have hconst : env.constants c'.name = some c'.toVConstant :=
      hconsts c' (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    have hshape := ctorShape_of_raw (hraw F hF c' hc')
      (hdata.sourceWF.2.2.2.1 c' (List.mem_flatMap.mpr ⟨F, hF, hc'⟩)) hconst
    refine .inr ⟨?_, ?_⟩
    · rw [hshape.family, hnames, List.getElem?_map, hFget]; rfl
    · rw [hcn]; exact view_ctor_name_mem j hown
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    have hk := container_ctor (envTables_inv H) hprior hle ha hc'
    exact .inl (by simp [ctorOf, hk])

end Lean4Lean.EnvTables
