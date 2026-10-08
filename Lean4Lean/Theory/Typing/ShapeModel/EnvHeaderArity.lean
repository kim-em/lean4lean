import Lean4Lean.Theory.Typing.ShapeModel.EnvSchemaMajors

/-!
# The weakest arity hypothesis for field counts

The field count of a native or generic equation is the normalized signature's, tied to the
source constructor only by `RestoresType` (`Models.constructors`, `RestoresFamily`): a
definitional equality in the compilation's header environment `E = base + family headers`. No
syntactic record pins the count. `HeaderArityRigid E U` is exactly what is used: two
definitionally equal telescopes ending in the *same* rigid constant at the *same* universe
levels have the same length.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

/-- Definitionally equal (at some type) closed telescopes ending in applications of the same
rigid constant at the same levels have the same length. -/
def HeaderArityRigid (E : VEnv) (U : Nat) : Prop :=
  ∀ {I : Name} {ls : List VLevel} {doms₁ doms₂ args₁ args₂ : List VExpr}, E.Rigid I →
    E.IsDefEqU U [] (VExpr.wrapForalls doms₁ (VExpr.mkApps (.const I ls) args₁))
      (VExpr.wrapForalls doms₂ (VExpr.mkApps (.const I ls) args₂)) →
    doms₁.length = doms₂.length

theorem ForallArityRigid.headerArityRigid {E : VEnv} (H : ForallArityRigid E) (U : Nat) :
    HeaderArityRigid E U := fun _ h => H teleArity_ctorShape teleArity_ctorShape h

/-- Restoration of a telescope ending in a constant application. -/
theorem restore_teleConst {r : Restoration} {doms : List VExpr} {n : Name} {ls : List VLevel}
    {args : List VExpr} {T : VExpr}
    (h : r.expr (VExpr.wrapForalls doms (VExpr.mkApps (.const n ls) args)) = some T) :
    ∃ doms' args', doms'.length = doms.length ∧
      ((r.heads.find? (fun h => h.auxiliary == n) = none ∧
        T = VExpr.wrapForalls doms' (VExpr.mkApps (.const (r.recursorName n) ls) args')) ∨
      (∃ spec, r.heads.find? (fun h => h.auxiliary == n) = some spec ∧
        T = VExpr.wrapForalls doms'
          (VExpr.mkApps (.const spec.target (spec.levels.map (·.inst ls))) args'))) := by
  induction doms generalizing T with
  | nil =>
    change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at h
    rw [restoration_mkApps] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨args', _, h⟩ := h
    simp only [List.append_nil, Restoration.expr.go] at h
    split at h
    · rename_i spec hspec
      unfold HeadSpecialization.apply at h
      split at h
      · cases h
      · cases h
        exact ⟨[], _, rfl, .inr ⟨spec, hspec, rfl⟩⟩
    · rename_i hnone
      cases h
      exact ⟨[], args', rfl, .inl ⟨hnone, rfl⟩⟩
  | cons d ds ih =>
    change (do let d' ← Restoration.expr.go r d []
               let b' ← Restoration.expr.go r (VExpr.wrapForalls ds _) []
               pure (VExpr.mkApps (.forallE d' b') [])) = some T at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨d', _, b', hb, rfl⟩ := h
    obtain ⟨doms', args', hlen, hc⟩ := ih hb
    refine ⟨d' :: doms', args', by simp [hlen], ?_⟩
    rcases hc with ⟨h1, rfl⟩ | ⟨spec, h1, rfl⟩
    · exact .inl ⟨h1, rfl⟩
    · exact .inr ⟨spec, h1, rfl⟩

theorem subst_teleConst (ds : List VExpr) (c : Name) (ls : List VLevel) (args : List VExpr)
    (σ : VExpr.Subst) :
    ∃ ds' args', ds'.length = ds.length ∧
      (VExpr.wrapForalls ds (VExpr.mkApps (.const c ls) args)).subst σ =
        VExpr.wrapForalls ds' (VExpr.mkApps (.const c ls) args') := by
  induction ds generalizing σ with
  | nil => exact ⟨[], _, rfl, by simp [VExpr.wrapForalls]; rfl⟩
  | cons d ds ih =>
    obtain ⟨ds', args', hlen, he⟩ := ih σ.lift
    refine ⟨d.subst σ :: ds', args', by simp [hlen], ?_⟩
    simp only [VExpr.wrapForalls, List.foldr_cons] at he ⊢
    simp only [VExpr.subst, he]

theorem instL_teleConst (ds : List VExpr) (c : Name) (ls : List VLevel) (args : List VExpr)
    (lv : List VLevel) :
    ∃ ds' args', ds'.length = ds.length ∧
      (VExpr.wrapForalls ds (VExpr.mkApps (.const c ls) args)).instL lv =
        VExpr.wrapForalls ds' (VExpr.mkApps (.const c (ls.map (·.inst lv))) args') := by
  induction ds with
  | nil => exact ⟨[], _, rfl, by simp [VExpr.wrapForalls, VExpr.instL]; rfl⟩
  | cons d ds ih =>
    obtain ⟨ds', args', hlen, he⟩ := ih
    refine ⟨d.instL lv :: ds', args', by simp [hlen], ?_⟩
    simp only [VExpr.wrapForalls, List.foldr_cons] at he ⊢
    simp only [VExpr.instL, he]

theorem specialize_teleConst {ds : List VExpr} {c : Name} {ls : List VLevel}
    {args xs : List VExpr} {t : VExpr}
    (h : specializeType (VExpr.wrapForalls ds (VExpr.mkApps (.const c ls) args)) xs = some t) :
    ∃ ds' args', ds'.length + xs.length = ds.length ∧
      t = VExpr.wrapForalls ds' (VExpr.mkApps (.const c ls) args') := by
  simp only [specializeType, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨pre, body⟩, ht, rfl⟩ := h
  have hle : xs.length ≤ ds.length := by
    have := teleArity_takeForalls (teleArity_ctorShape (doms := ds) (c := c) (ls := ls)
      (args := args)) ht
    exact this.1
  have hsplit : ds = ds.take xs.length ++ ds.drop xs.length := (List.take_append_drop _ _).symm
  have ht' := ht
  rw [hsplit, VExpr.wrapForalls_append] at ht'
  have h2 := VExpr.takeForalls_wrapForalls_append (ds.take xs.length) (ds.drop xs.length)
    (VExpr.mkApps (.const c ls) args)
  rw [List.length_take, Nat.min_eq_left hle, VExpr.wrapForalls_append] at h2
  rw [h2] at ht'
  cases Option.some.inj ht'
  obtain ⟨ds', args', hlen, he⟩ := subst_teleConst (ds.drop xs.length) c ls args
    (fun i => if hi : i < xs.length then xs[xs.length - 1 - i] else .bvar (i - xs.length))
  refine ⟨ds', args', by rw [hlen]; simp; omega, ?_⟩
  exact he

/-- The container constructor's own raw shape: a telescope ending in the container family at the
container's universe parameters. -/
theorem container_raw {env : VEnv} {aux : List ContainerSpecialization}
    (hprior : CertifiedSpecializations env aux) {a : ContainerSpecialization} (ha : a ∈ aux)
    {c : VConstVal} (hc : c ∈ a.source.ctors) :
    ∃ doms args, c.type = VExpr.wrapForalls doms
      (VExpr.mkApps (.const a.source.name (VLevel.params a.container.uvars)) args) ∧
      doms.length = c.type.forallArity := by
  obtain ⟨_, _, _, hcomp, _, _⟩ := CertifiedSpecializations.member hprior ha
  obtain ⟨_, _, _, _, _, _, hdata, _⟩ := hcomp.compilationOrigin
  obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
  obtain ⟨doms, result, heq, _, _, hhead, harity⟩ :=
    (hraw a.source (List.getElem_mem a.family.isLt) c hc).forallArity
  refine ⟨doms, result.getAppFnArgs.2, ?_, harity.symm⟩
  rw [heq, ← hhead, mkApps_getAppFnArgs]

/-- Field counts against constructor arities, from `HeaderArityRigid` in the compilation's
header environment `E` (base plus the source family headers), for the source families and the
container families, which must be rigid there. -/
theorem CaseCompilationData.ctor_arity_header {base E : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock}
    (hdata : CaseCompilationData base src exp s aux block)
    (hrfresh : RecursorNamesFresh base src exp aux)
    (hprior : CertifiedSpecializations base aux)
    (hE : base.addConstVals src.typeConstants = some E) (hP : HeaderArityRigid E src.uvars)
    (hrigF : ∀ F ∈ src.types, E.Rigid F.name) (hrigN : ∀ a ∈ aux, a.source.ctors ≠ [] → E.Rigid a.source.name)
    (index : Fin s.constructors.size) :
    (∃ F ∈ src.types, ∃ c ∈ F.ctors, s.constructors[index].name = c.name ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.params.length + s.constructors[index].fields.length = c.type.forallArity) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, s.constructors[index].name = a.constructorName c ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.constructors[index].fields.length + a.arguments.length = c.type.forallArity) := by
  obtain ⟨envTypes, direct, hT, hdirect, hwf, hfamilies⟩ := hdata.correspondence
  cases Option.some.inj (hT.symm.trans hE)
  have huv : s.uvars = src.uvars := hdata.model.uvars.trans hdata.uvars
  obtain ⟨fam, hfam, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨sc, hsc, hname, _, restored, hres, hdefeq⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ (s.declarationCtor_family index)
  have hfamName : s.families[s.constructors[index].owner].name = fam.name := hrel.name
  have hres' : (compilationRestoration src aux).expr (VExpr.wrapForalls
      (s.params ++ s.fieldTypes s.constructors[index])
      (VExpr.mkApps (.const fam.name (VLevel.params src.uvars))
        (vars s.params.length s.constructors[index].fields.length ++
          s.constructors[index].indices))) = some restored := by
    rw [← hfamName, ← huv]
    simpa [declarationCtor, constructorType, familyApp] using hres
  obtain ⟨doms', args', hlen', hcases⟩ := restore_teleConst hres'
  have hnorm : (s.params ++ s.fieldTypes s.constructors[index]).length =
      s.params.length + s.constructors[index].fields.length := by
    simp [fieldTypes]
  have hname' : s.constructors[index].name = sc.name := hname
  rcases List.mem_append.mp hfam with hsrc | hdir
  · left
    refine ⟨fam, hsrc, sc, hsc, hname', ?_, ?_⟩
    · rw [hname']
      exact hdata.headName_source hrfresh (List.mem_flatMap.mpr ⟨fam, hsrc,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨sc, hsc, rfl⟩)⟩)
    · have hfn : fam.name ∈ familyNames src.types := List.mem_flatMap.mpr ⟨fam, hsrc, List.mem_cons_self⟩
      have hrestored : restored = VExpr.wrapForalls doms'
          (VExpr.mkApps (.const fam.name (VLevel.params src.uvars)) args') := by
        rcases hcases with ⟨hnone, rfl⟩ | ⟨spec, hsome, _⟩
        · have hhn := hdata.headName_source hrfresh hfn
          unfold Restoration.headName at hhn
          rw [hnone] at hhn
          simp only at hhn
          rw [hhn]
        · exfalso
          have hsa : spec.auxiliary = fam.name := by simpa using List.find?_some hsome
          exact hdata.source_head_disjoint hfn
            (List.mem_map.mpr ⟨spec, List.mem_of_find?_eq_some hsome, hsa⟩)
      obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
      obtain ⟨doms, result, heq, _, _, hhead, harity⟩ := (hraw fam hsrc sc hsc).forallArity
      have hsct : sc.type = VExpr.wrapForalls doms
          (VExpr.mkApps (.const fam.name (VLevel.params src.uvars)) result.getAppFnArgs.2) := by
        rw [heq, ← hhead, mkApps_getAppFnArgs]
      rw [hrestored, hsct] at hdefeq
      have := hP (hrigF fam hsrc) hdefeq
      omega
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) fam hdir
    obtain ⟨c, hc, t, hspec, hdcn, hdct⟩ := directFamily_ctor hdf hsc
    refine ⟨a, ha, c, hc, hname'.trans hdcn, ?_, ?_⟩
    · rw [hname', hdcn]
      exact hdata.headName_auxiliary_constructor ha hc
    · have hfa : fam.name = a.auxiliary := ContainerSpecialization.directFamily_name hdf
      have hhead : HeadSpecialization.mk a.auxiliary src.uvars src.nparams a.source.name
          a.levels a.arguments ∈ (compilationRestoration src aux).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
      have hwfa := hwf a ha
      have hlv : a.levels.map (·.inst (VLevel.params src.uvars)) = a.levels := by
        conv => rhs; rw [← List.map_id a.levels]
        exact List.map_congr_left fun l hl => VLevel.inst_id (hwfa.2.2.2.1 l hl)
      have hrestored : restored = VExpr.wrapForalls doms'
          (VExpr.mkApps (.const a.source.name a.levels) args') := by
        rcases hcases with ⟨hnone, _⟩ | ⟨spec, hsome, rfl⟩
        · exfalso
          have := List.find?_eq_none.mp hnone _ hhead
          simp [hfa] at this
        · have hsa : spec.auxiliary = a.auxiliary := by
            rw [← hfa]; simpa using List.find?_some hsome
          have := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1
            (List.mem_of_find?_eq_some hsome) hhead hsa
          subst this
          simp only [hlv]
      obtain ⟨cd, cargs, hct, hcar⟩ := container_raw hprior ha hc
      obtain ⟨cd', cargs', hcdl, hci⟩ := instL_teleConst cd a.source.name
        (VLevel.params a.container.uvars) cargs a.levels
      rw [VLevel.inst_map_id hwfa.2.2.1] at hci
      rw [hct, hci] at hspec
      obtain ⟨ds, targs, hdsl, rfl⟩ := specialize_teleConst hspec
      rw [hdct, ← VExpr.wrapForalls_append, hrestored] at hdefeq
      have := hP (hrigN a ha (List.ne_nil_of_mem hc)) hdefeq
      simp only [List.length_append] at this
      omega

theorem CaseCompilationData.source_arity_of {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hprior : CertifiedSpecializations base aux)
    (j : Fin s.constructors.size) (hcases : (∃ F ∈ src.types, ∃ c ∈ F.ctors, s.constructors[j].name = c.name ∧
      (compilationRestoration src aux).headName s.constructors[j].name = c.name ∧
      s.params.length + s.constructors[j].fields.length = c.type.forallArity) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, s.constructors[j].name = a.constructorName c ∧
      (compilationRestoration src aux).headName s.constructors[j].name = c.name ∧
      s.constructors[j].fields.length + a.arguments.length = c.type.forallArity)) {F : VInductiveType} (hF : F ∈ src.types)
    {c : VConstVal} (hc : c ∈ F.ctors) (hcn : c.name = s.constructors[j].name) :
    s.params.length + s.constructors[j].fields.length = c.type.forallArity := by
  have hnd := hdata.sourceWF.2.1
  have hcn' : c.name ∈ familyNames src.types :=
    List.mem_flatMap.mpr ⟨F, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  rcases hcases with
    ⟨F', hF', c', hc', hn', _, harity⟩ | ⟨a, ha, c', hc', hn', _, _⟩
  · have hcc : c' = c := by
      have hnd' := (List.nodup_append.mp hnd).2.1
      exact List.eq_of_mem_of_nodup_map hnd' (List.mem_flatMap.mpr ⟨F', hF', hc'⟩)
        (List.mem_flatMap.mpr ⟨F, hF, hc⟩) (hn'.symm.trans hcn.symm)
    rw [← hcc]; exact harity
  · exfalso
    exact hdata.source_head_disjoint hcn'
      (List.mem_map.mpr ⟨_, auxCtor_head_mem (src := src) ha hc', (hn'.symm.trans hcn.symm)⟩)

/-- The field count of a container-constructor equation, under `ForallArityRigid`. -/
theorem CaseCompilationData.container_arity_of {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hprior : CertifiedSpecializations base aux)
    (j : Fin s.constructors.size) (hcases : (∃ F ∈ src.types, ∃ c ∈ F.ctors, s.constructors[j].name = c.name ∧
      (compilationRestoration src aux).headName s.constructors[j].name = c.name ∧
      s.params.length + s.constructors[j].fields.length = c.type.forallArity) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, s.constructors[j].name = a.constructorName c ∧
      (compilationRestoration src aux).headName s.constructors[j].name = c.name ∧
      s.constructors[j].fields.length + a.arguments.length = c.type.forallArity)) {a : ContainerSpecialization} (ha : a ∈ aux)
    {c : VConstVal} (hc : c ∈ a.source.ctors) (hcn : s.constructors[j].name = a.constructorName c) :
    s.constructors[j].fields.length + a.arguments.length = c.type.forallArity := by
  rcases hcases with
    ⟨F', hF', c', hc', hn', _, _⟩ | ⟨a', ha', c', hc', hn', _, harity⟩
  · exfalso
    have hcn' : c'.name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨F', hF', List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)⟩
    exact hdata.source_head_disjoint hcn'
      (List.mem_map.mpr ⟨_, auxCtor_head_mem (src := src) ha hc, (hcn.symm.trans hn')⟩)
  · have heq := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1
      (auxCtor_head_mem (src := src) ha' hc') (auxCtor_head_mem (src := src) ha hc)
      (hn'.symm.trans hcn)
    simp only [HeadSpecialization.mk.injEq] at heq
    obtain ⟨_, _, _, htarget, _, hargs⟩ := heq
    rw [← hargs]
    have h1 := (hprior.container_ctor a' ha' c' hc').1
    have h2 := (hprior.container_ctor a ha c hc).1
    rw [htarget, h2] at h1
    have : c'.type = c.type := congrArg VConstant.type (Option.some.inj h1).symm
    rw [← this]; exact harity


theorem Rigid.of_sub {E E' : VEnv} (hsub : ∀ df, E.defeqs df → E'.defeqs df) (h : E'.Rigid n) :
    E.Rigid n := fun df hdf ls hh => h df (hsub df hdf) ls hh

theorem container_family_rigid {T : Tables} {env base : VEnv} {aux : List ContainerSpecialization}
    (HT : T.Inv env) (hprior : CertifiedSpecializations base aux) (hle : base ≤ env)
    {a : ContainerSpecialization} (ha : a ∈ aux) (hne : a.source.ctors ≠ []) :
    env.Rigid a.source.name := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  have hk := container_ctor HT hprior hle ha hc
  obtain ⟨_, d, hd, _⟩ := HT.views.ctor hk
  exact HT.views.rigid (.inl (by simp [ctorView] at hd; simp [hd]))

/-- The header-environment form of `defeq_major`: the field count of a constructor major of an
installed equation is the table's, provided `HeaderArityRigid E U` holds for an environment `E`
below `env` that does not contain the equation (the compilation's header environment, i.e. the
equation's stratum; for the quotient equation the conclusion is unconditional). -/
theorem defeq_major_header {env : VEnv} (H : env.WF) (hdf : env.defeqs df)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ k ps nf, ctorOf env c = some k ∧ args = ps ++ vars nf 0 ∧ ps.length = k.nparams ∧
      ∃ E U, E ≤ env ∧ ¬ E.defeqs df ∧ (HeaderArityRigid E U → nf = k.nfields) := by
  have HT := envTables_inv H
  rcases HT.equations hdf with ⟨v, _, rfl⟩ | ⟨hq, rfl⟩ | ⟨dX, hdX, iX, hiX, hgX⟩
  · cases hm
  · have h1 : quotDefEq.lhs.stripLams = .app _
        (VExpr.mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]) := rfl
    rw [h1] at hm
    obtain ⟨_, hm⟩ := VExpr.app.inj hm
    obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hm.symm
    exact ⟨quotCtor, [.bvar 5, .bvar 4], 1, (HT.quot hq).2.2.1, rfl, rfl, VEnv.empty, 0,
      VEnv.empty_le env, fun h => h, fun _ => rfl⟩
  · obtain ⟨_, hevX⟩ := HT.natives hdX
    obtain ⟨bX, ibX, srcX, expX, auxX, blockX, instX, hdataX, hpriorX, hbX, hrX, _, hinstX,
      hleX, hibWF, _, hfamX⟩ := hevX
    have hgX' : (compilationRestoration srcX auxX).equation (dX.nativeInstance.equation iX) =
        some df := by
      simpa only [NativeRecursorData.equation, hrX] using hgX
    have htypesE : ∀ t ∈ srcX.types, env.constants t.name = some t.toVConstant := fun t ht =>
      hleX.constants (install_type_lookup hinstX (by
        rw [hdataX.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hbE : bX ≤ env := hbX.trans ((install_le hinstX).trans hleX)
    have hnp : dX.schema.signature.params.length = srcX.nparams := by
      rw [hdataX.model.nparams, hdataX.nparams]
    obtain ⟨E, _, hE, _, _, _⟩ := hdataX.correspondence
    have hEle : E ≤ env := addConstVals_le_of hE hbE (fun ci hci => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci; exact htypesE t ht)
    have hEsub : ∀ df', E.defeqs df' → ibX.defeqs df' := fun df' h' => by
      rw [VEnv.addConstVals_defeqs hE] at h'; exact hbX.defeqs h'
    have hfreshT : ∀ t ∈ srcX.types, ibX.constants t.name = none := by
      intro t ht
      obtain ⟨_, _, _, ht', _⟩ := install_parts hinstX
      exact VEnv.addConstVals_names_fresh ht' t.toVConstVal (by
        rw [hdataX.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hrigF : ∀ F ∈ srcX.types, E.Rigid F.name := fun F hF =>
      Rigid.of_sub hEsub (hibWF.ordered.rigid_of_absent (hfreshT F hF))
    have hrigN : ∀ a ∈ auxX, a.source.ctors ≠ [] → E.Rigid a.source.name := fun a ha hne =>
      Rigid.of_sub (fun df' h' => hleX.defeqs ((install_le hinstX).defeqs (hEsub df' h')))
        (container_family_rigid HT hpriorX hbE ha hne)
    have hnot : ¬ E.defeqs df := by
      intro hmem
      have hentry : NativeRecursorData.ofInstance default
          (CaseSchema.ofCompilation srcX dX.schema.signature auxX) dX.nativeInstance dX.owner ∈
            NativeRecursorData.compilationEntries default srcX dX.schema.signature auxX
              dX.nativeInstance :=
        List.mem_map.mpr ⟨dX.owner, List.mem_finRange _, rfl⟩
      have hname : (NativeRecursorData.ofInstance default
          (CaseSchema.ofCompilation srcX dX.schema.signature auxX) dX.nativeInstance
            dX.owner).name = dX.name := by
        simp only [NativeRecursorData.name, NativeRecursorData.ofInstance,
          CaseSchema.ofCompilation, hrX]
      have hfresh := hdataX.nativeEntries_fresh hinstX hentry
      rw [hname] at hfresh
      exact hibWF.ordered.rigid_of_absent hfresh df (hEsub df hmem) _ (native_head HT hdX hiX hgX)
    have harity := fun hP => CaseCompilationData.ctor_arity_header hdataX.toCaseCompilationData hdataX.recursorNamesFresh hpriorX hE hP hrigF hrigN iX
    obtain ⟨Ds, idx, major, hlhs, _, hcases⟩ := CompilationData.major_cases hdataX iX hgX'
    have hmaj : major = VExpr.mkApps (.const c ls) args := by
      rw [hlhs, ruleBody_stripLams] at hm
      exact (VExpr.app.inj hm).2
    rcases hcases with ⟨F, hF, _, c', hc', hcn, rfl⟩ | ⟨a, ha, _, _, c', hc', hcn, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj
      have hconst : env.constants c'.name = some c'.toVConstant :=
        hleX.constants (VInductBlock.install_ctor_lookup hinstX (by
          rw [hdataX.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
      obtain ⟨k, hk, _, _, hknp, hkar, _⟩ :=
        ctor_entry_of_fam HT (hfamX F hF (List.ne_nil_of_mem hc')) hc' hconst
      refine ⟨k, _, _, hk, rfl, by rw [vars_length, hknp, hnp], E, srcX.uvars, hEle, hnot,
        fun hP => ?_⟩
      have := CaseCompilationData.source_arity_of hdataX.toCaseCompilationData hpriorX iX (harity hP) hF hc' hcn
      omega
    · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj
      have hk := container_ctor HT hpriorX hbE ha hc'
      obtain ⟨_, _, _, _, hwf, _⟩ := hdataX.correspondence
      have hargs : a.arguments.length = a.container.nparams := (hwf a ha).1
      refine ⟨_, _, _, hk, rfl, by simp [ctorView, hargs], E, srcX.uvars, hEle, hnot,
        fun hP => ?_⟩
      have := CaseCompilationData.container_arity_of hdataX.toCaseCompilationData hpriorX iX (harity hP) ha hc' hcn
      simp only [ctorView]
      omega

/-- The header-environment form of `schema_major`. -/
theorem schema_major_header {env : VEnv} (H : env.WF) {schema : CaseSchema}
    (hreg : env.eliminators key schema) {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} (hgen : schema.genericEquations key owner = some rules)
    (hdf : df ∈ rules) (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ kS ps nf, args = ps ++ vars nf 0 ∧ ps.length = kS.nparams ∧ CtorShape env c kS ∧
      (∃ E U, E ≤ env ∧ (HeaderArityRigid E U → nf = kS.nfields)) ∧
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
  obtain ⟨E, _, hE, _, _, _⟩ := hdata.correspondence
  have hEle : E ≤ env := addConstVals_le_of hE hle (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci; exact htypes t ht)
  have hEdf : E.defeqs = base.defeqs := VEnv.addConstVals_defeqs hE
  have hrigF : ∀ F ∈ source.types, E.Rigid F.name := by
    intro F hF
    obtain ⟨_, _, _, _, _, _, ht', _⟩ := hdata.sourceWF
    have hfr := VEnv.addConstVals_names_fresh ht' F.toVConstVal (List.mem_map.mpr ⟨F, hF, rfl⟩)
    exact Rigid.of_sub (fun df' h' => by rwa [hEdf] at h') (hbase.ordered.rigid_of_absent hfr)
  have hrigN : ∀ a ∈ aux, a.source.ctors ≠ [] → E.Rigid a.source.name := fun a ha hne =>
    Rigid.of_sub (fun df' h' => hle.defeqs (by rwa [hEdf] at h'))
      (container_family_rigid (envTables_inv H) hprior hle ha hne)
  have harity := fun hP => CaseCompilationData.ctor_arity_header hdata hrfresh hprior hE hP hrigF hrigN j
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
      ⟨E, source.uvars, hEle, fun hP => ?_⟩, ?_⟩
    · have := CaseCompilationData.source_arity_of hdata hprior j (harity hP) hF hc' hcn
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
      ctorOf_shape H hk, ⟨E, source.uvars, hEle, fun hP => ?_⟩, .inl hk⟩
    have := CaseCompilationData.container_arity_of hdata hprior j (harity hP) ha hc' hcn
    simp only [ctorView]
    omega

end Lean4Lean.ShapeModel
