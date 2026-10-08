import Lean4Lean.Theory.Typing.ShapeModel.EnvSigSyntax
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness

/-!
# The shape of generic eliminator equations

The analogue of `CompilationData.rule_shape` (T2) for the generic equations of a registered
eliminator schema: a lambda telescope `Ds` shared by both sides; the left body applies the
abstract head `.elim key owner (.param 0 :: genericLevels)` to the prefix variables (parameters,
the motive, the minors), the index expressions, and the restored constructor application whose
trailing arguments are the field variables; the right body is a minor applied to the fields.
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature CaseSchema

theorem view_constructor_external' {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (index : Fin (schema.view owner).constructors.size) :
    Instance.recursiveFields (schema.view owner).constructors[index] = [] := by
  obtain ⟨ctor, _, _, hc⟩ := view_constructor_origin index
  rw [hc]
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  obtain ⟨domain, _, hd⟩ := List.mem_map.mp hfield
  cases field with
  | external => rfl
  | recursive => cases hd

/-- The shape of a generic case equation of a certified schema. -/
theorem Certified.generic_shape {base : VEnv} {source : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} (hcert : schema.Certified base source block)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules) :
    ∃ (index : Fin (schema.view owner).constructors.size) (Ds idx : List VExpr) (c : Name)
      (lv : List VLevel) (ps : List VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps (.elim key owner.val (.param 0 :: schema.genericLevels))
        (vars (schema.signature.params.length + (1 + (schema.view owner).constructors.size))
            (schema.view owner).constructors[index].fields.length ++ idx ++
          [VExpr.mkApps (.const c lv) (ps ++ vars (schema.view owner).constructors[index].fields.length 0)])) ∧
      df.rhs = VExpr.wrapLams Ds (VExpr.mkApps
        (.bvar ((schema.view owner).constructors[index].fields.length +
          (schema.view owner).constructors.size - 1 - index.val))
        (vars (schema.view owner).constructors[index].fields.length 0)) ∧
      Ds.length = schema.signature.params.length + (1 + (schema.view owner).constructors.size) +
        (schema.view owner).constructors[index].fields.length ∧
      idx.length = (schema.view owner).constructors[index].indices.length ∧
      idx.length = schema.signature.families[owner].indices.length ∧
      ∃ j : Fin schema.signature.constructors.size, schema.signature.constructors[j].owner = owner ∧
        schema.signature.constructors[j].fields.length =
          (schema.view owner).constructors[index].fields.length ∧
        ∃ e, 1 ≤ e ∧ schema.restoration.expr (VExpr.mkApps
          (.const schema.signature.constructors[j].name schema.genericLevels)
          (vars schema.signature.params.length (e + schema.signature.constructors[j].fields.length) ++
            vars schema.signature.constructors[j].fields.length 0)) =
          some (VExpr.mkApps (.const c lv) (ps ++ vars (schema.view owner).constructors[index].fields.length 0)) := by
  obtain ⟨index, hrestore⟩ := CaseSchema.equation_origin hgen hdf
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨ds', lhs', rhs', _, hl', hr', _, hel, her, _, hlen⟩ := restored_common_telescope hl hr ht
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  have hlhs0 : schema.restoration.expr
      (VExpr.mkApps (.elim key owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices ++ [g.constructorApp ctor extra 0])) = some lhs' := by
    simpa only [Instance.recursorHead, hzero, Nat.add_zero] using hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp only [List.mapM_append, restoration_vars', List.mapM_cons, List.mapM_nil, bind,
    Option.bind_eq_some_iff, pure, Option.some.injEq] at hlhs0
  obtain ⟨_, ⟨_, ⟨_, rfl, idx', hi, rfl⟩, _, ⟨major', hmajor, _, rfl, rfl⟩, rfl⟩, hout⟩ := hlhs0
  simp only [List.append_nil, Restoration.expr.go, Option.some.injEq] at hout
  have hnoRec := view_constructor_external' (schema := schema) (owner := owner) index
  have hrhs : rhs' = VExpr.mkApps (.bvar (nf + (schema.view owner).constructors.size - 1 - index.val))
      (vars nf 0) := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some rhs' at hr'
    simp only [hnoRec, List.map_nil, List.append_nil] at hr'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hr'
    rw [restoration_mkApps] at hr'
    simp [restoration_vars', Restoration.expr.go] at hr'
    exact hr'.symm
  -- the major
  obtain ⟨sc, hsc, hown, hview⟩ := CaseSchema.view_constructor_origin index
  obtain ⟨jn, hjn, hjget⟩ := List.mem_iff_getElem.mp hsc
  let j : Fin schema.signature.constructors.size := ⟨jn, by simpa using hjn⟩
  have hj : schema.signature.constructors[j] = sc := by simpa [j] using hjget
  have hc : ctor = schema.caseConstructor sc := hview
  have hnf : sc.fields.length = nf := by
    simp [nf, hc, CaseSchema.caseConstructor, fieldTypes]
  have hmajor' : schema.restoration.expr (VExpr.mkApps
      (.const schema.signature.constructors[j].name schema.genericLevels)
      (vars schema.signature.params.length (extra + schema.signature.constructors[j].fields.length) ++
        vars schema.signature.constructors[j].fields.length 0)) = some major' := by
    rw [← hmajor]
    change _ = schema.restoration.expr (VExpr.mkApps (.const ctor.name g.levels)
      (vars (schema.view owner).params.length (extra + ctor.fields.length + 0) ++
        vars ctor.fields.length 0))
    rw [hc, hj]
    simp [CaseSchema.caseConstructor, fieldTypes, CaseSchema.view, g, CaseSchema.specialize]
  obtain ⟨_, _, hdata, _, hr, _, _⟩ := hcert
  have hparams : ∀ h ∈ schema.restoration.heads, h.nparams = schema.signature.params.length := by
    intro h hh
    rw [hr] at hh
    rw [compilationRestoration_nparams h hh, hdata.model.nparams, hdata.nparams]
  have hcases := restored_ctorApp hparams hmajor'
  have hform : ∃ c lv ps, major' = VExpr.mkApps (.const c lv)
      (ps ++ vars schema.signature.constructors[j].fields.length 0) := by
    rcases hcases with ⟨_, h⟩ | ⟨_, _, _, _, h⟩ <;> exact ⟨_, _, _, h⟩
  obtain ⟨c, lv, ps, hm⟩ := hform
  have hfj : schema.signature.constructors[j].fields.length = nf := by rw [hj, hnf]
  rw [hfj] at hm hmajor'
  rw [hm] at hmajor'
  have hidx : idx'.length = ctor.indices.length := by
    have := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hi)
    simpa [indices] using this.symm
  have hidx2 : idx'.length = schema.signature.families[owner].indices.length := by
    rw [hidx, hc]
    have := hdata.model.constructorArity sc hsc
    simp only [CaseSchema.caseConstructor]
    rw [this]; subst hown; rfl
  refine ⟨index, ds', idx', c, lv, ps, ?_, ?_, ?_, hidx, hidx2, j, by rw [hj, hown], hfj, extra,
    by simp [extra], ?_⟩
  · rw [hel, ← hout, hm]
    rfl
  · rw [her, hrhs]
  · rw [hlen]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders, fieldTypes,
      CaseSchema.specialize, CaseSchema.view]
    omega
  · rw [hfj]; exact hmajor'

/-- The family of a declared constant's type (`familyOfType`). -/
def ctorFamily (env : VEnv) (c : Name) : Option Name :=
  (env.constants c).bind fun ci => familyOfType ci.type

theorem CtorShape.family {env : VEnv} {c : Name} {k : CtorData} (h : CtorShape env c k) :
    ctorFamily env c = some k.family := by
  obtain ⟨ci, doms, idx, hc, _, ht, _⟩ := h
  simp [ctorFamily, hc, ht, familyOfType_shape]

/-- The major of a generic equation of a registered schema in terms of the compilation: a source
constructor of the owner's family at the generic levels, or a constructor of the owner's
container at the container's levels. -/
theorem generic_major_class {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) :
    ∃ (lvOf : Fin schema.signature.families.size → List VLevel)
      (famOf' : Fin schema.signature.families.size → Name),
      ∀ {owner : Fin schema.signature.families.size} {rules : List VDefEq} {df : VDefEq}
        {fn : VExpr} {c : Name} {ls : List VLevel} {args : List VExpr},
        schema.genericEquations key owner = some rules → df ∈ rules →
        df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args) →
        ls = lvOf owner ∧ ctorFamily env c = some (famOf' owner) := by
  classical
  obtain ⟨base, source, block, _, hle, hcert, _, hconsts⟩ := H.eliminator_origin hreg
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hr, _, hrfresh⟩ := hcert'
  let lvOf : Fin schema.signature.families.size → List VLevel := fun o =>
    if h : o.val < source.types.length then schema.genericLevels
    else match aux[o.val - source.types.length]? with
      | some a => a.levels.map (·.inst schema.genericLevels)
      | none => []
  let famOf' : Fin schema.signature.families.size → Name := fun o =>
    if h : o.val < source.types.length then source.types[o.val].name
    else match aux[o.val - source.types.length]? with
      | some a => a.source.name
      | none => default
  refine ⟨lvOf, famOf', ?_⟩
  intro owner rules df fn c ls args hgen hdf hm
  obtain ⟨j, hown, e, _, hrestore⟩ := Certified.generic_major hcert hgen hdf hm
  rw [hr] at hrestore
  rcases CaseCompilationData.ctorApp_cases hdata hrfresh j hrestore with
    ⟨F, hF, hFget, c', hc', _, hmaj⟩ | ⟨a, ha, hge, haget, c', hc', _, hmaj⟩
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    rw [hown] at hFget
    have hlt := (List.getElem?_eq_some_iff.mp hFget).1
    have hFeq := (List.getElem?_eq_some_iff.mp hFget).2
    have hconst : env.constants c'.name = some c'.toVConstant :=
      hconsts c' (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    have hshape := ctorShape_of_raw (hraw F hF c' hc')
      (hdata.sourceWF.2.2.2.1 c' (List.mem_flatMap.mpr ⟨F, hF, hc'⟩)) hconst
    refine ⟨by simp [lvOf, hlt], ?_⟩
    rw [hshape.family]
    simp [famOf', hlt, hFeq, ctorView]
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    rw [hown] at hge haget
    have hlt : ¬ owner.val < source.types.length := by omega
    have hk := container_ctor (envTables_inv H) hprior hle ha hc'
    have hshape := ((envTables_inv H).views.ctor hk).1
    refine ⟨by simp [lvOf, hlt, haget], ?_⟩
    rw [hshape.family]
    simp [famOf', hlt, haget, ctorView]

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

end Lean4Lean.ShapeModel
