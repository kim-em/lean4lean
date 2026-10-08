import Lean4Lean.Theory.Typing.ShapeModel.EnvMajors

/-!
# Majors of generic eliminator-schema equations (M4a, T1 (c) for schemas)

The schema's own view of a family can disagree with the recorded one (see the counterexample in
`EnvTables.lean`), so for schema equations the constructor data are given in the schema's own
view `kS`; the table agrees with it unless the family was recorded first with a different
parameter count or without the constructor.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

/-- Two constructor shapes of the same constant with the same family and parameter count are
equal. -/
theorem CtorShape.eq {env : VEnv} {c : Name} {k k' : CtorData} (h : CtorShape env c k)
    (h' : CtorShape env c k') (hf : k.family = k'.family) (hp : k.nparams = k'.nparams) :
    k = k' := by
  obtain ⟨ci, doms, idx, hc, huv, ht, hl⟩ := h
  obtain ⟨ci', doms', idx', hc', huv', ht', hl'⟩ := h'
  rw [hc] at hc'
  cases hc'
  have harity : ∀ {doms : List VExpr} {f ls args},
      (VExpr.wrapForalls doms (VExpr.mkApps (.const f ls) args)).forallArity = doms.length := by
    intro doms f ls args
    rw [VExpr.forallArity_wrapForalls,
      VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)]
    rfl
  have h1 := congrArg VExpr.forallArity ht
  have h2 := congrArg VExpr.forallArity ht'
  rw [harity] at h1 h2
  obtain ⟨f, u, p, n⟩ := k
  obtain ⟨f', u', p', n'⟩ := k'
  simp only at hf hp huv huv' hl hl'
  simp only [CtorData.mk.injEq]
  exact ⟨hf, huv.symm.trans huv', hp, by omega⟩

/-- Restoration of the constructor application of a signature constructor. -/
theorem CaseCompilationData.ctorApp_cases {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hrfresh : RecursorNamesFresh base src exp aux)
    (j : Fin s.constructors.size) {lv : List VLevel} {e : Nat} {major : VExpr}
    (hr : (compilationRestoration src aux).expr (VExpr.mkApps (.const s.constructors[j].name lv)
      (vars s.params.length (e + s.constructors[j].fields.length) ++
        vars s.constructors[j].fields.length 0)) = some major) :
    (∃ F ∈ src.types, src.types[s.constructors[j].owner.val]? = some F ∧
        ∃ c ∈ F.ctors, c.name = s.constructors[j].name ∧
        major = VExpr.mkApps (.const c.name lv)
          (vars s.params.length (e + s.constructors[j].fields.length) ++
            vars s.constructors[j].fields.length 0)) ∨
    (∃ a ∈ aux, src.types.length ≤ s.constructors[j].owner.val ∧
        aux[s.constructors[j].owner.val - src.types.length]? = some a ∧
        ∃ c ∈ a.source.ctors, s.constructors[j].name = a.constructorName c ∧
        major = VExpr.mkApps (.const c.name (a.levels.map (·.inst lv)))
          (a.arguments.map (fun arg => instantiateParams (arg.instL lv)
            (vars s.params.length (e + s.constructors[j].fields.length))) ++
            vars s.constructors[j].fields.length 0)) := by
  have hparams : ∀ h ∈ (compilationRestoration src aux).heads, h.nparams = s.params.length := by
    intro h hh
    rw [compilationRestoration_nparams h hh, ← hdata.nparams, ← hdata.model.nparams]
  have hmaj := restored_ctorApp hparams hr
  by_cases ho : s.constructors[j].owner.val < src.types.length
  · obtain ⟨_, _, hctors⟩ := CaseCompilationData.source_slot hdata _ ho
    obtain ⟨c, hc, hcn⟩ := hctors j rfl
    have hF := List.getElem_mem (l := src.types) ho
    have hcn' : c.name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨_, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
    left
    refine ⟨_, hF, List.getElem?_eq_getElem ho, c, hc, hcn, ?_⟩
    rcases hmaj with ⟨hnone, rfl⟩ | ⟨spec, hspec, hsome, _, _⟩
    · have hhn := hdata.headName_source hrfresh hcn'
      unfold Restoration.headName at hhn
      rw [hcn, hnone] at hhn
      simp only at hhn
      rw [hhn, hcn]
    · exfalso
      have : spec.auxiliary = c.name := by
        rw [hcn]; simpa using List.find?_some hsome
      exact hdata.source_head_disjoint hcn' (List.mem_map.mpr ⟨spec, hspec, this⟩)
  · right
    obtain ⟨envTypes, direct, _, hdirect, hlt, hrel⟩ :=
      CaseCompilationData.family_slot hdata s.constructors[j].owner
    have ho' : src.types.length ≤ s.constructors[j].owner.val := by omega
    have hlt2 : s.constructors[j].owner.val < src.types.length + direct.length := by
      simpa using hlt
    rw [List.getElem_append_right ho'] at hrel
    have hrel' := List.mapM_eq_some.mp hdirect
    have hlen := Lean4Lean.List.Forall₂.length_eq hrel'
    have hjb : s.constructors[j].owner.val - src.types.length < aux.length := by omega
    obtain ⟨_, hdf⟩ := forall₂_getElem_exists hrel' (s.constructors[j].owner.val - src.types.length) hjb
    have ha := List.getElem_mem hjb
    obtain ⟨dc, hdc, hdcn, _⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
      (s.declarationCtor_family j)
    obtain ⟨c, hc, t, _, hdcname, _⟩ := directFamily_ctor hdf hdc
    have hjn : s.constructors[j].name = _ := hdcn.trans hdcname
    refine ⟨_, ha, ho', List.getElem?_eq_getElem hjb, c, hc, hjn, ?_⟩
    have hhead := auxCtor_head_mem (src := src) ha hc
    rcases hmaj with ⟨hnone, _⟩ | ⟨spec, hspec, hsome, _, rfl⟩
    · exfalso
      have := List.find?_eq_none.mp hnone _ hhead
      simp at this
      exact this hjn.symm
    · have hsa : spec.auxiliary =
          aux[s.constructors[j].owner.val - src.types.length].constructorName c := by
        rw [← hjn]; simpa using List.find?_some hsome
      have := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1 hspec hhead hsa
      subst this
      rfl

/-- The major of a generic case equation of a certified schema. -/
theorem Certified.generic_major {base : VEnv} {source : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} (hcert : schema.Certified base source block)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ j : Fin schema.signature.constructors.size, schema.signature.constructors[j].owner = owner ∧
      ∃ e, 1 ≤ e ∧ schema.restoration.expr (VExpr.mkApps
        (.const schema.signature.constructors[j].name schema.genericLevels)
        (vars schema.signature.params.length (e + schema.signature.constructors[j].fields.length) ++
          vars schema.signature.constructors[j].fields.length 0)) =
        some (VExpr.mkApps (.const c ls) args) := by
  obtain ⟨index, hrestore⟩ := CaseSchema.equation_origin hgen hdf
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨ds', lhs', _, _, hl', _, _, hel, _, _, _⟩ := restored_common_telescope hl hr ht
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  change schema.restoration.expr (VExpr.mkApps _ (vars np nf ++ indices ++
    [g.constructorApp ctor extra 0])) = some lhs' at hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hl'
  rw [restoration_mkApps] at hl'
  simp only [List.mapM_append, restoration_vars', List.mapM_cons, List.mapM_nil, bind,
    Option.bind_eq_some_iff, pure, Option.some.injEq] at hl'
  obtain ⟨_, ⟨_, ⟨_, rfl, idx', _, rfl⟩, _, ⟨major', hmajor, _, rfl, rfl⟩, rfl⟩, hout⟩ := hl'
  simp only [List.append_nil, Instance.recursorHead, Restoration.expr.go,
    Option.some.injEq] at hout
  rw [hel, stripLams_wrapLams', ← hout, mkApps_snoc] at hm
  have hmaj : major' = VExpr.mkApps (.const c ls) args := (VExpr.app.inj hm).2
  obtain ⟨sc, hsc, hown, hview⟩ := CaseSchema.view_constructor_origin index
  obtain ⟨jn, hjn, hjget⟩ := List.mem_iff_getElem.mp hsc
  let j : Fin schema.signature.constructors.size := ⟨jn, by simpa using hjn⟩
  have hj : schema.signature.constructors[j] = sc := by simpa [j] using hjget
  refine ⟨j, by rw [hj, hown], extra, by simp [extra], ?_⟩
  rw [← hmaj, ← hmajor]
  change _ = schema.restoration.expr (VExpr.mkApps (.const ctor.name g.levels)
    (vars (schema.view owner).params.length (extra + ctor.fields.length + 0) ++
      vars ctor.fields.length 0))
  have hc : ctor = schema.caseConstructor sc := hview
  rw [hc, hj]
  simp [CaseSchema.caseConstructor, fieldTypes, CaseSchema.view, g, CaseSchema.specialize]

/-- T1 (c) for generic equations of registered eliminator schemas, restated: the major is a
constructor of the schema's own view `kS` (a source constructor of the schema's declaration,
or a container constructor), applied to `kS.nparams` parameter arguments and the field
variables (with `nf = kS.nfields` under `ForallArityRigid`). The table records `kS`
(`ctorOf env c = some kS`) except when the family is an original family of the schema that was
recorded first under another view: with a different parameter count, or without this
constructor (the structure registration of the counterexample in `EnvTables.lean`). -/
theorem schema_major {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} (hgen : schema.genericEquations key owner = some rules)
    (hdf : df ∈ rules) (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ kS ps nf, args = ps ++ vars nf 0 ∧ ps.length = kS.nparams ∧ CtorShape env c kS ∧
      (ForallArityRigid env → nf = kS.nfields) ∧
      (ctorOf env c = some kS ∨ (kS.family ∈ schema.originalFamilies ∧
        ∀ d, famOf env kS.family = some d → kS.nparams ≠ d.nparams ∨ c ∉ d.ctors)) := by
  obtain ⟨base, source, block, hbase, hle, hcert, _, hconsts⟩ := H.eliminator_origin hreg
  obtain ⟨j, _, e, he, hrestore⟩ := Certified.generic_major hcert hgen hdf hm
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hr, hnames, hrfresh⟩ := hcert'
  rw [hr] at hrestore
  have htypes : ∀ t ∈ source.types, env.constants t.name = some t.toVConstant := fun t ht =>
    hconsts t.toVConstVal (List.mem_append_left _ (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
  have hnp : schema.signature.params.length = source.nparams := by
    rw [hdata.model.nparams, hdata.nparams]
  rcases CaseCompilationData.ctorApp_cases hdata hrfresh j hrestore with
    ⟨F, hF, _, c', hc', hcn, hmaj⟩ | ⟨a, ha, _, _, c', hc', hcn, hmaj⟩
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    have hconst : env.constants c'.name = some c'.toVConstant :=
      hconsts c' (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    have hshape := ctorShape_of_raw (hraw F hF c' hc')
      (hdata.sourceWF.2.2.2.1 c' (List.mem_flatMap.mpr ⟨F, hF, hc'⟩)) hconst
    refine ⟨ctorView source F c', _, _, rfl, by simp [vars_length, ctorView, hnp], hshape,
      fun hP => ?_, ?_⟩
    · have := CaseCompilationData.source_arity hdata hrfresh hprior hP hle htypes j hF hc' hcn
      simp only [ctorView]
      omega
    · by_cases hk : ctorOf env c'.name = some (ctorView source F c')
      · exact .inl hk
      · refine .inr ⟨by rw [hnames]; exact List.mem_map.mpr ⟨F, hF, rfl⟩, fun d hd => ?_⟩
        by_cases hnpd : (ctorView source F c').nparams = d.nparams
        · refine .inr fun hcd => hk ?_
          obtain ⟨k, hkc, hkf⟩ := (famOf_mem_ctors H hd).mp hcd
          obtain ⟨d', hd', _, hdnp⟩ := ctorOf_famOf H hkc
          rw [hkf, hd] at hd'
          cases hd'
          rw [hkc, CtorShape.eq (ctorOf_shape H hkc) hshape hkf (hdnp.symm.trans hnpd.symm)]
        · exact .inl hnpd
  · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj.symm
    have hk := container_ctor (envTables_inv H) hprior hle ha hc'
    obtain ⟨_, _, _, _, hwf, _⟩ := hdata.correspondence
    have hargs : a.arguments.length = a.container.nparams := (hwf a ha).1
    refine ⟨ctorView a.container a.source c', _, _, rfl, by simp [ctorView, hargs],
      ctorOf_shape H hk, fun hP => ?_, .inl hk⟩
    have := CaseCompilationData.container_arity hdata hrfresh hprior hP hle htypes j ha hc' hcn
    simp only [ctorView]
    omega

end Lean4Lean.ShapeModel
