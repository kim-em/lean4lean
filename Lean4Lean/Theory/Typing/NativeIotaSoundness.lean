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

end VEnv

end Lean4Lean
