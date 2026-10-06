import Lean4Lean.Theory.Typing.NativeIotaPatterns
import Lean4Lean.Theory.Typing.NativeMajorFamily
import Lean4Lean.Verify.Inductive.Nested.RecursorProvenance
import Lean4Lean.Verify.Inductive.Nested.AssemblyNativeWhnf

/-! Soundness of native iota patterns.

A native iota pattern is generated from an actual restored recursor equation.
Its soundness is the iota theorem `VIotaRuleShape.iota` for the restored
recursor, constructor and rule shapes. The shapes are read off the finite
compilation that registered the recursor; the restoration lemmas for nested
specializations are shared with the executable verification. -/

namespace Lean4Lean
open InductiveSignature

namespace InductiveSignature

theorem mem_familyNames {types : List VInductiveType} {n : Name} :
    n ∈ familyNames types ↔
      (∃ t ∈ types, t.name = n) ∨ ∃ t ∈ types, ∃ c ∈ t.ctors, c.name = n := by
  unfold familyNames
  simp only [List.mem_flatMap, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact .inl ⟨t, ht, h.symm⟩
    · exact .inr ⟨t, ht, c, hc, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩)
    · exact ⟨t, ht, .inl rfl⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩

theorem familyNames_append (l₁ l₂ : List VInductiveType) :
    familyNames (l₁ ++ l₂) = familyNames l₁ ++ familyNames l₂ := by
  simp [familyNames, List.flatMap_append]

/-- Restoration-only names are absent from the environment holding the source
types and constructors. Auxiliary heads are lowered family and constructor
names, fresh by the expanded formation; auxiliary recursor names are fresh
generated recursors. -/
theorem CompilationData.restorableNames_fresh
    {base envTypes envCtors : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hadded : base.addConstVals source.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals source.constructorConstants = some envCtors) :
    ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none := by
  intro n hn
  -- every name of the source block
  have hsrc : ∀ v, envCtors.constants n = some v → base.constants n = some v ∨
      n ∈ familyNames source.types := by
    intro v hv
    rcases VEnv.addConstVals_lookup_origin hctors hv with h | ⟨e, he, hname, _⟩
    · rcases VEnv.addConstVals_lookup_origin hadded h with h | ⟨e, he, hname, _⟩
      · exact .inl h
      · right
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
        exact mem_familyNames.mpr (.inl ⟨t, ht, hname⟩)
    · right
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp he
      exact mem_familyNames.mpr (.inr ⟨t, ht, e, hc, hname⟩)
  -- expanded names
  obtain ⟨envT, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hexpNames : familyNames expanded.types = familyNames source.types ++ familyNames direct := by
    rw [← H.model.familyNames, RestoresFamily.familyNames hfamilies, familyNames_append]
  obtain ⟨envExpT, envExpC, hexpT, hexpC, _⟩ := H.recursiveTypesWF
  have hfreshExp : ∀ m ∈ familyNames expanded.types, base.constants m = none := by
    intro m hm
    rcases mem_familyNames.mp hm with ⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩
    · exact VEnv.addConstVals_names_fresh hexpT t.toVConstVal (List.mem_map.mpr ⟨t, ht, rfl⟩)
    · have h := VEnv.addConstVals_names_fresh hexpC c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
      cases hb : base.constants c.name with
      | none => rfl
      | some v => rw [(VEnv.addConstVals_le hexpT).constants hb] at h; cases h
  cases hv : envCtors.constants n with
  | none => rfl
  | some v =>
  rcases List.mem_append.mp hn with hhead | hrec
  · have hdir : n ∈ familyNames direct := by
      rw [← compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect]
      exact hhead
    rcases hsrc v hv with hb | hs
    · rw [hfreshExp n (by rw [hexpNames]; exact List.mem_append_right _ hdir)] at hb
      cases hb
    · exact (H.source_head_disjoint hs hhead).elim
  · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hrec
    have hg := H.recursor_source_mem hpair
    rcases hsrc v hv with hb | hs
    · obtain ⟨rc, hrc, hname⟩ := List.mem_map.mp hg
      rw [← hname, H.recursorsFresh rc hrc] at hb
      cases hb
    · exfalso
      have hnd := H.generatedNames
      simp only [List.map_append, List.nodup_append] at hnd
      have hin : pair.1 ∈ (expanded.typeConstants.map (·.name) ++
          expanded.constructorConstants.map (·.name)) := by
        have he : pair.1 ∈ familyNames expanded.types := by
          rw [hexpNames]; exact List.mem_append_left _ hs
        rcases mem_familyNames.mp he with ⟨t, ht, h⟩ | ⟨t, ht, c, hc, h⟩
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨t.toVConstVal,
            List.mem_map.mpr ⟨t, ht, rfl⟩, h⟩)
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨c,
            List.mem_flatMap.mpr ⟨t, ht, hc⟩, h⟩)
      exact hnd.2.2 _ hin _ hg rfl

end InductiveSignature

namespace VEnv

private theorem stripLams_wrap' (domains : List VExpr) (e : VExpr) :
    (VExpr.wrapLams domains e).stripLams = e.stripLams := by
  induction domains with
  | nil => rfl
  | cons d ds ih => exact ih

/-- The restored recursor, constructor and rule shapes of an installed native
rule, at the restored head of its owner family. -/
theorem NativeRecursorRegistered.iota_shapes {data : NativeRecursorData} (henv : env.WF)
    (hr : NativeRecursorRegistered env data)
    {index : Fin data.schema.signature.constructors.size}
    (ho : data.schema.signature.constructors[index].owner = data.owner)
    (hg : data.equation index = some equation) :
    ∃ head : RestoredFamilyHead,
      Nonempty (VRecursorShape env data.name data.uvars data.schema.signature.params.length
        head.arguments.length data.schema.signature.families.size
        data.schema.signature.constructors.size data.numIndices head.name head.levels
        head.arguments) ∧
      Nonempty (VConstructorShape env (data.ruleConstructor index) head.levels.length
        head.arguments.length data.schema.signature.constructors[index].fields.length
        data.numIndices head.name) ∧
      Nonempty (VIotaRuleShape env data.name data.uvars data.schema.signature.params.length
        head.arguments.length data.schema.signature.families.size
        data.schema.signature.constructors.size data.numIndices (data.ruleConstructor index)
        head.levels data.schema.signature.constructors[index].fields.length equation
        head.arguments) ∧
      env.Rigid head.name := by
  have hr₀ := hr
  have hdef := hr.equation_present hg
  have hmajor₀ := hr.equation_major hg
  obtain ⟨base, installBase, source, expanded, g, aux, block, installed,
    hdata, hprior, hbase, hres, _, hu, hlv, htg, hi, he⟩ := hr
  have hinst : data.nativeInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [NativeRecursorData.nativeInstance, Instance.mk.injEq]
      exact ⟨hu, hlv, htg, funext fun owner => (hdata.recursorNames owner).symm⟩
  let r := compilationRestoration source aux
  have heq : r.equation (g.equation index) = some equation := by
    have := hg
    unfold NativeRecursorData.equation at this
    rwa [hres, hinst] at this
  obtain ⟨-, -, -, -, envTypes, envCtors, hadded, hctorsAdded, -, -⟩ := hdata.sourceWF
  have hfreshC := hdata.restorableNames_fresh hadded hctorsAdded
  have hfreshT : ∀ n ∈ r.restorableNames, envTypes.constants n = none := by
    intro n hn
    cases h : envTypes.constants n with
    | none => rfl
    | some v =>
      have := (VEnv.addConstVals_le hctorsAdded).constants h
      rw [hfreshC n hn] at this; cases this
  have hbaseEnv : base ≤ env := hbase.trans ((VInductBlock.install_le hi).trans he)
  have hinstalled := VInductBlock.install_constants hi
  have hle : envCtors ≤ env := by
    apply VEnv.addConstVals_le_target (VEnv.addConstVals_le_target hbaseEnv hadded ?_) hctorsAdded
    · intro v hv
      exact he.constants (hinstalled v (List.mem_append_right _ (by rw [hdata.ctors]; exact hv)))
    · intro v hv
      exact he.constants (hinstalled v (List.mem_append_left _ (by rw [hdata.types]; exact hv)))
  obtain ⟨head, hhead, _, _, hargs, happ, Hctors⟩ :=
    hdata.restoredFamilyHead_spec hadded hctorsAdded hfreshT hfreshC data.owner
  obtain ⟨-, happC⟩ := Hctors index ho
  have hindices := hdata.model.constructorArity _
    (Array.getElem_mem_toList (xs := data.schema.signature.constructors) index.isLt)
  have hnotHead : r.heads.find? (fun h => h.auxiliary ==
      g.recursorName data.schema.signature.constructors[index].owner) = none := by
    apply Restoration.heads_find?_eq_none
    intro hm
    obtain ⟨h, hh, he'⟩ := List.mem_map.mp hm
    exact hdata.heads_not_recursors _ h hh he'
  obtain ⟨I⟩ := Restoration.restored_iota_shape g r index heq hdef hindices hnotHead happC
  obtain ⟨head2, hhead2, fields, ⟨hctorShape⟩⟩ := hdata.restoredConstructorShape hprior
    hadded hctorsAdded hfreshT hfreshC hle index data.owner ho
  cases Option.some.inj (hhead2.symm.trans hhead)
  -- names and counts
  have hname : data.name = r.recursorName (g.recursorName data.owner) := by
    unfold NativeRecursorData.name
    rw [hres, hdata.recursorNames]
  have I : VIotaRuleShape env data.name data.uvars data.schema.signature.params.length
      head.arguments.length data.schema.signature.families.size
      data.schema.signature.constructors.size data.numIndices
      (r.restoredHeadName data.schema.signature.constructors[index].name)
      head.levels data.schema.signature.constructors[index].fields.length equation
      head.arguments := by
    have := I
    simp only [ho] at this
    rw [hname, hu]
    exact this
  -- the constructor name
  have hctorName : data.ruleConstructor index =
      r.restoredHeadName data.schema.signature.constructors[index].name := by
    obtain ⟨fn, lv, args, hfn⟩ := hmajor₀
    have hl := I.lhs_eq
    have hb := I.lhs_pattern
    have hs : equation.lhs.stripLams = I.lhsBody := by
      rw [hl, stripLams_wrap', hb]
      exact VExpr.stripLams_of_head_const (VExpr.getAppFnArgs_mkApps_head _ _)
    rw [hs, hb, VExpr.mkApps_append, VExpr.mkApps] at hfn
    simp only [List.foldl_cons, List.foldl_nil, VExpr.app.injEq] at hfn
    have h2 := congrArg (fun e : VExpr => e.getAppFnArgs.1) hfn.2
    rw [VExpr.getAppFnArgs_mkApps_head, VExpr.getAppFnArgs_mkApps_head] at h2
    unfold NativeRecursorData.ruleConstructor
    exact (VExpr.const.inj h2).1.symm
  rw [← hctorName] at I hctorShape
  -- the recursor shape
  obtain ⟨type, htype⟩ := hr₀.recursorType_exists
  have hcst := hr₀.recursorType htype
  have htype' : r.expr (g.recursorType data.owner) = some type := by
    unfold NativeRecursorData.recursorType at htype
    rwa [hres, hinst] at htype
  obtain ⟨pre, major, hpre, hm, rfl⟩ := r.expr_recursorType_eq_some htype'
  have hprelen : pre.length = data.schema.signature.params.length +
      data.schema.signature.families.size + data.schema.signature.constructors.size +
      data.numIndices := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)),
      g.recursorPrefix_length data.owner]
    rfl
  have hmaj := Option.some.inj (hm.symm.trans happ)
  have Hrec : VRecursorShape env data.name data.uvars data.schema.signature.params.length
      head.arguments.length data.schema.signature.families.size
      data.schema.signature.constructors.size data.numIndices head.name head.levels
      head.arguments := {
    ctorParams_length := rfl
    ctorParams_closed := hargs
    type := _
    const := hcst
    doms := pre ++ [major]
    result := g.recursorBody data.owner
    type_eq := rfl
    doms_length := by simp [hprelen]
    major_eq := by
      rw [← hprelen, List.getElem?_concat_length, hmaj, vars_eq_bvarRange, Nat.add_zero]
      rfl }
  -- rigidity of the major family
  have hrigid : env.Rigid head.name := by
    have hm' : equation.HasConstructorMajor (data.ruleConstructor index) := by
      unfold NativeRecursorData.ruleConstructor; exact hmajor₀
    obtain ⟨ci, hci, F, ls, hF, _, hFr⟩ := henv.native_constructor_result_rigid hdef hm'
    rw [hctorShape.const] at hci
    cases hci
    rw [hctorShape.type_eq, VExpr.forallResult_wrapForalls,
      VExpr.forallResult_of_head (VExpr.getAppFnArgs_mkApps_head _ _),
      VExpr.getAppFnArgs_mkApps_head] at hF
    cases hF
    exact hFr
  have hfields := VIotaRuleShape.fieldCount henv I (henv.ordered.defEqWF hdef) Hrec hctorShape hrigid
  subst hfields
  exact ⟨head, ⟨Hrec⟩, ⟨hctorShape⟩, ⟨I⟩, hrigid⟩

private theorem argumentRHS_var {p : Pattern} :
    ∀ {n} {x : (p.varN n).RHS}, x ∈ p.argumentRHS n → ∃ path, x = .var path
  | 0, _, h => by cases h
  | n + 1, x, h => by
    simp only [Pattern.argumentRHS, List.mem_append, List.mem_map, List.mem_singleton] at h
    rcases h with ⟨y, hy, rfl⟩ | rfl
    · obtain ⟨path, rfl⟩ := argumentRHS_var hy
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

private theorem argumentRHS_apply_levels {p : Pattern} {n : Nat} (l l' : List VLevel)
    (v : (p.varN n).Path → VExpr) :
    (p.argumentRHS n).map (·.apply l v) = (p.argumentRHS n).map (·.apply l' v) := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨path, rfl⟩ := argumentRHS_var hx
  rfl

/-- The major arguments of a restored native rule: the specialized parameters
and the field variables. -/
private theorem ruleMajorArguments_eq
    (I : VIotaRuleShape env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams) :
    NativeRecursorData.ruleMajorArguments df =
      (ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
        VExpr.bvarRange nfields nfields := by
  unfold NativeRecursorData.ruleMajorArguments
  rw [I.lhs_eq, stripLams_wrap', I.lhs_pattern,
    VExpr.stripLams_of_head_const (VExpr.getAppFnArgs_mkApps_head _ _),
    VerifyInductive.VExpr.getAppFnArgs_mkApps]
  simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.nil_append,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
  have h := VerifyInductive.VExpr.getAppFnArgs_mkApps (.const ctorName ctorLevels)
    ((ctorParams.map fun p => p.liftN (nmotives + nminors + nfields)) ++
      VExpr.bvarRange nfields nfields)
  simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, List.nil_append] at h
  rw [h]

/-- Native iota patterns are sound: a matched redex is definitionally equal
to the captured instance of the installed native equation. -/
theorem NativeIotaPattern.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (_hregistry : ∀ name data, registry name = some data →
      NativeRecursorRegistered env data ∧ data.name = name)
    (H : NativeIotaPattern env registry p rhs)
    (hm : p.Matches e levels values) (ht : env.HasType U Γ e type) :
    env.IsDefEqU U Γ e (rhs.1.apply levels values) := by
  cases H with
  | @intro data index equation _ hr _ ho hg =>
  obtain ⟨head, ⟨Hrec⟩, ⟨Hctor⟩, ⟨Hrule⟩, hrigid⟩ := hr.iota_shapes henv ho hg
  have hargsEq := ruleMajorArguments_eq Hrule
  simp only [NativeRecursorData.rulePattern, SimplePattern.toPattern] at hm
  cases hm with
  | @app _ F _ g1 _ M lsc g2 hF hM =>
  have hFe := hF.const_arguments
  have hMe := hM.const_arguments
  generalize hpre : ((Pattern.const data.name).argumentRHS data.majorOffset).map
    (·.apply levels g1) = pre at hFe
  generalize hcargs : ((Pattern.const (data.ruleConstructor index)).argumentRHS
    (NativeRecursorData.ruleMajorArguments equation).length).map (·.apply lsc g2) = cargs at hMe
  subst hFe hMe
  have hpreLen : pre.length = data.majorOffset := by
    rw [← hpre]; simp [Pattern.argumentRHS_length]
  have hcLen : cargs.length = head.arguments.length +
      data.schema.signature.constructors[index].fields.length := by
    rw [← hcargs]; simp [Pattern.argumentRHS_length, hargsEq]
  have happ : VExpr.mkApps (.const data.name levels)
      (pre ++ VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs :: []) =
      .app (VExpr.mkApps (.const data.name levels) pre)
        (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs) := by
    simp [VExpr.mkApps, List.foldl_append]
  have hwf : VExpr.WF env U Γ (VExpr.mkApps (.const data.name levels)
      (pre ++ VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs :: [])) := by
    rw [happ]; exact ⟨_, ht⟩
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hwf
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
  rw [Hrec.const] at hci
  cases hci
  have hfa : VExpr.WF env U Γ (.app (VExpr.mkApps (.const data.name levels) pre)
      (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs)) := ⟨_, ht⟩
  obtain ⟨_, _, _, hMt⟩ := hfa.app_inv henv.ordered hΓ
  obtain ⟨_, hcc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ (⟨_, hMt⟩ :
    VExpr.WF env U Γ (VExpr.mkApps (.const (data.ruleConstructor index) lsc) cargs))
  obtain ⟨cci, hcci, hcw, hcl⟩ := HasType.const_inv henv.ordered hΓ hcc
  rw [Hctor.const] at hcci
  cases hcci
  have key := VIotaRuleShape.iota henv hΓ Hrec Hctor Hrule hrigid rfl hw hl
    (by rw [hpreLen]; rfl) hwf hcl hcw
    (P' := cargs.take head.arguments.length) (fields := cargs.drop head.arguments.length)
    (by rw [List.length_take, hcLen]; omega) (by rw [List.length_drop, hcLen]; omega)
    (by rw [List.take_append_drop]; exact ⟨_, hMt⟩)
  rw [happ] at key
  have hrhs : ∀ hcl, @Pattern.RHS.apply (data.rulePattern index equation) levels (Sum.elim g1 g2)
        (data.ruleRHS index equation hcl) =
      VExpr.mkApps (equation.rhs.instL levels)
        (pre.take (data.schema.signature.params.length + data.schema.signature.families.size +
          data.schema.signature.constructors.size) ++ cargs.drop head.arguments.length ++ []) := by
    intro hcl
    simp only [NativeRecursorData.ruleRHS, NativeRecursorData.ruleCaptures]
    refine (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).trans ?_
    simp only [List.map_append, List.map_map, Function.comp_def, List.append_nil]
    have h1 : ∀ x : ((Pattern.const data.name).varN data.majorOffset).RHS,
        Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2)
          (x.mapPaths Sum.inl) = x.apply levels g1 := fun x =>
      Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inl x
    have h2 : ∀ x : ((Pattern.const (data.ruleConstructor index)).varN
        (NativeRecursorData.ruleMajorArguments equation).length).RHS,
        Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2)
          (x.mapPaths Sum.inr) = x.apply levels g2 := fun x =>
      Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
    simp only [h1, h2]
    show VExpr.mkApps (equation.rhs.instL levels) _ = _
    have hk : (NativeRecursorData.ruleMajorArguments equation).length -
        data.schema.signature.constructors[index].fields.length = head.arguments.length := by
      rw [hargsEq]; simp
    rw [hk, List.map_take, List.map_drop, hpre, argumentRHS_apply_levels levels lsc, hcargs]
    rfl
  exact (hrhs _) ▸ key

end VEnv

end Lean4Lean
