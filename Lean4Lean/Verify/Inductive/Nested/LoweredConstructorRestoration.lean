import Lean4Lean.Verify.Inductive.Nested.ConstructorRestoration
import Lean4Lean.Verify.Inductive.Nested.RestorationAgreement

/-! Restoration of the lowered constructor types of the source families of a
validated nested run (the `loweredConstructors` field of
`NestedConstructorRestorationGaps`).

`NestedValidatedRunResult.restorationTablesRestoring` expands every source
constructor type into the corresponding lowered constructor type by leaves
that `compilationRestoration` inverts (`Restoration.RestoringLeaf`), so
restoration maps each lowered constructor type syntactically back to its
source constructor type (`VExpr.NestedExprExpansion.restore`), given that

* the source constructor types avoid the restorable names (they are typed in
  the source header environment, where these names are fresh), and
* every restoration head occurs in the lowered constructor types at the
  declaration's own universe parameters (`VExpr.ConstLevelsAt`).

The second fact is not derived here: the executable lowering emits each
auxiliary occurrence at `state.lvls`, which is initialised to the declaration's
level parameters and never modified, but the relational traces of the run
(`LoweredConstructorMapping`, `NestedLoweringRun`) do not record `lvls`.
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

private theorem nodup_map_inj'' {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj'' hnd.2 hx' hy' hxy

/-- The restorable names of the compilation restoration of a validated nested
run (the auxiliary family and constructor names, and the auxiliary recursor
names) are fresh in the source header environment. -/
theorem NestedValidatedRunResult.restorableNames_fresh
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup) :
    ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envTypes.constants name = none := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.production.loweredDecl.typeConstants =
        some E.production.constructors.completed.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.completed.headerVEnv) hinit)
      E.production.constructors.completed.core.typesAdded
  have hloweredCtors := E.production.constructors.completed.core.ctorsAdded
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hprefix : sourceDecl.typeConstants =
      E.production.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.nativeSource.sourceTypeValues
    rw [E.nativeSourceDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hsourceTypesEq : sourceDecl.types.map VInductiveType.toVConstVal =
      (E.production.loweredDecl.types.take sourceDecl.types.length).map
        VInductiveType.toVConstVal := by
    have := hprefix
    simp only [VInductDecl.typeConstants] at this
    rw [this, List.map_take]
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.consumedGeneration.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hsourceEntry : ∀ entry ∈ sourceDecl.typeConstants, ∃ t ∈
      E.production.loweredDecl.types.take sourceDecl.types.length,
        entry = t.toVConstVal := by
    intro entry hentry
    rw [VInductDecl.typeConstants, hsourceTypesEq] at hentry
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
    exact ⟨t, ht, rfl⟩
  have hbaseLE : (ves.venv (if isUnsafe then .unsafe else .safe)) ≤
      E.production.constructors.completed.headerVEnv := VEnv.addConstVals_le hloweredTypes
  have hbaseFresh : ∀ name ∈ familyNames
      (E.production.loweredDecl.types.drop sourceDecl.types.length),
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants name = none := by
    intro name hname
    obtain ⟨t, ht, rfl | ⟨c, hc, rfl⟩⟩ := mem_familyNames.mp hname
    · exact (VEnv.addConstVals_names_fresh hloweredTypes).2 t.toVConstVal
        (List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, rfl⟩)
    · have hmem : c ∈ E.production.loweredDecl.constructorConstants :=
        List.mem_flatMap.mpr ⟨t, List.mem_of_mem_drop ht, hc⟩
      exact VEnv.LE.constants_eq_none_left hbaseLE
        ((VEnv.addConstVals_names_fresh hloweredCtors).2 c hmem)
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary),
      envTypes.constants name = none := by
    rw [hheadNames]
    intro name hname
    cases hc : envTypes.constants name with
    | none => rfl
    | some ci =>
      exfalso
      rcases VEnv.addConstVals_lookup_origin hadded hc with hbase | ⟨entry, hentry, hn, -⟩
      · rw [hbaseFresh name hname] at hbase; cases hbase
      · obtain ⟨t, ht, rfl⟩ := hsourceEntry entry hentry
        have h1 : name ∈ familyNames
            (E.production.loweredDecl.types.take sourceDecl.types.length) :=
          mem_familyNames.mpr ⟨t, ht, .inl hn.symm⟩
        exact (List.nodup_append.mp hfamNodup).2.2 _ h1 _ hname rfl
  have hrecursorsAdded := E.production.production.installed.abstract
  have hrecursorValues : E.production.production.entries.map Prod.snd =
      E.production.compilationInstance.recursors :=
    E.production.production.completed.canonicalRecursors
  rw [hrecursorValues] at hrecursorsAdded
  have hrecursorsFresh := VEnv.addConstVals_names_fresh hrecursorsAdded
  simp only [VEnv.addProjections_constants] at hrecursorsFresh
  have hctorFresh : ∀ recursor ∈ E.production.compilationInstance.recursors,
      E.production.constructors.completed.ctorVEnv.constants recursor.name = none :=
    hrecursorsFresh.2
  have hbaseCtorLE : (ves.venv (if isUnsafe then .unsafe else .safe)) ≤
      E.production.constructors.completed.ctorVEnv :=
    hbaseLE.trans (VEnv.addConstVals_le hloweredCtors)
  have hrecBase : ∀ t ∈ E.production.loweredDecl.types,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants (t.name.str "rec") = none := by
    intro t ht
    obtain ⟨d, hd, hdname, -⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hmodels.families t ht
    simp only [InductiveSignature.declaration, List.mem_map] at hd
    obtain ⟨⟨f, i⟩, hfi, rfl⟩ := hd
    have hf : f ∈ E.production.compilationSignature.families.toList :=
      List.fst_mem_of_mem_zipIdx hfi
    obtain ⟨j, hj, hjf⟩ := List.getElem_of_mem hf
    let owner : Fin E.production.compilationSignature.families.size :=
      ⟨j, by simpa using hj⟩
    have hname : E.production.compilationInstance.recursorName owner = t.name.str "rec" := by
      have h := E.production.loweredConstruction.consumedGeneration.names owner
      change E.production.compilationInstance.recursorName owner =
        E.production.compilationSignature.families[owner].name.str "rec" at h
      rw [h, ← hdname]
      simp only [owner, ← hjf, Array.getElem_toList, Fin.getElem_fin]
    have hmem : E.production.compilationInstance.recursor owner ∈
        E.production.compilationInstance.recursors :=
      List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩
    have := hctorFresh _ hmem
    change E.production.constructors.completed.ctorVEnv.constants
      (E.production.compilationInstance.recursorName owner) = none at this
    rw [hname] at this
    exact VEnv.LE.constants_eq_none_left hbaseCtorLE this
  have hrecFresh : ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
      envTypes.constants p.1 = none := by
    intro p hp
    have hp1 : p.1 ∈ auxiliaries.map (fun a => a.auxiliary.str "rec") := by
      rw [← compilationRestoration_recursors_fst]
      exact List.mem_map_of_mem hp
    obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp1
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    rw [← hpa, ← hta]
    cases hc : envTypes.constants (t.name.str "rec") with
    | none => rfl
    | some ci =>
      exfalso
      rcases VEnv.addConstVals_lookup_origin hadded hc with hbase | ⟨entry, hentry, hn, -⟩
      · rw [hrecBase t (List.mem_of_mem_drop ht)] at hbase; cases hbase
      · obtain ⟨t', ht', rfl⟩ := hsourceEntry entry hentry
        have h1 : t'.name ∈ familyNames E.production.loweredDecl.types :=
          mem_familyNames.mpr ⟨t', List.mem_of_mem_take ht', .inl rfl⟩
        have h2 : t.name.str "rec" ∈ E.production.loweredDecl.types.map
            (fun t => t.name.str "rec") :=
          List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
            (List.mem_of_mem_drop ht)
        exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 hn
  intro name hname
  rcases List.mem_append.mp hname with h | h
  · exact hfresh name h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hrecFresh p hp

/-- **Restoration of the lowered constructor types of a validated nested run**
(the `loweredConstructors` field of `NestedConstructorRestorationGaps`), for
the specialisations of `restorationTablesRestoring`. The existential prefix
repeats that of `NestedValidatedRunResult.sourceConstructors_of`. The
restoration is syntactic: it returns the source constructor type itself.

The premise states that every restoration head occurs in the lowered
constructor types of the source families at the universe parameters of the
declaration; see the module documentation. -/
theorem NestedValidatedRunResult.loweredConstructors_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      auxiliaries.flatMap (·.headNames) =
        familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
      CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (∀ params : List VExpr,
        VEnv.IsDefEqCtx envTypes sourceDecl.uvars [] params.reverse
          E.production.headers.commonParameterContext →
        ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl params) ∧
      (∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
        E.production.constructors.completed.parameterScope.toCtx.reverse) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ (U : Nat) (params : List VExpr), ∃ direct,
        auxiliaries.mapM (fun a => a.directFamily U params) = some direct ∧
        List.Forall₂ (DirectFamilyShape U) auxiliaries direct) ∧
      (∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
        result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            (a.constructorName ctor)) ∧
      (∀ name, (compilationRestoration sourceDecl auxiliaries).recursorName name =
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.find? name).getD
          name) ∧
      ((∀ lowered ∈ E.production.loweredDecl.types.take sourceDecl.types.length,
          ∀ lc ∈ lowered.ctors,
            lc.type.ConstLevelsAt
              ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
              (VLevel.params sourceDecl.uvars)) →
        List.Forall₂ (fun lowered source : VInductiveType =>
            List.Forall₂ (fun lc sc : VConstVal =>
                (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                  some sc.type ∧
                ∃ restored,
                  (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                    some restored ∧
                  envTypes.SimAt sourceDecl.uvars [] restored sc.type)
              lowered.ctors source.ctors)
          (E.production.loweredDecl.types.take sourceDecl.types.length)
          sourceDecl.types) := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoring wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      _hparamsSize, D, Hrestoring⟩
  let r := compilationRestoration sourceDecl auxiliaries
  have hsuffixNodup :
      (familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ++
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (fun t => t.name.str "rec")).Nodup := by
    refine hnodup.sublist (List.Sublist.append ?_ ((List.drop_sublist _ _).map _))
    conv => rhs; rw [← List.take_append_drop sourceDecl.types.length
      E.production.loweredDecl.types]
    simp only [familyNames, List.flatMap_append]
    exact List.sublist_append_right _ _
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.production.constructors.completed.parameterScope.toCtx.reverse).reverse
      E.production.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorPhasesResult.completed_parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  -- executable constructor names agree with the table
  have hheadsNodup' : (r.heads.map (·.auxiliary)).Nodup := by
    rw [compilationRestoration_heads_auxiliary]
    exact D.headNodup
  have hctorNames : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
        r.restoredHeadName (a.constructorName ctor) := by
    intro a ha ctor hctor
    obtain ⟨info, hfind, hinduct⟩ := D.ctorInstalled a ha ctor hctor
    obtain ⟨nested, hn⟩ := D.familyLookup a ha
    have hget : result.getNestedIfAuxCtor E.loweredEnv (a.constructorName ctor) =
        some (nested, a.auxiliary) := by
      rw [← hinduct]
      exact getNestedIfAuxCtor_of hfind (hinduct ▸ hn)
    obtain ⟨b, hb, hba, envS, domains, lvls, Ys, -, hab, -, -⟩ := D.familyKey _ nested hn
    have hmemA : InductiveSignature.HeadSpecialization.mk a.auxiliary sourceDecl.uvars
        sourceDecl.nparams a.source.name a.levels a.arguments ∈ r.heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hmemB : InductiveSignature.HeadSpecialization.mk b.auxiliary sourceDecl.uvars
        sourceDecl.nparams b.source.name b.levels b.arguments ∈ r.heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have hsame := nodup_map_inj'' hheadsNodup' hmemB hmemA hba
    have hsrc : b.source.name = a.source.name :=
      congrArg InductiveSignature.HeadSpecialization.target hsame
    have hhead : nested.getAppFn = .const a.source.name lvls := by
      obtain ⟨xs, hxs⟩ := D.paramsFVars
      rw [hxs, Expr.abstractN_eq] at hab
      rw [← hsrc]
      exact abstractN_getAppFn_const nested 0
        (by rw [hab, Expr.getAppFn_mkAppList_const])
    exact restoreCtorName_eq_restoredHeadName D.headNodup ha hctor
      (D.ctorRenamed a ha ctor hctor) result E.loweredEnv hget hhead
  -- freshness of the restorable names and the source constructor types
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have htypesEq : E.nativeSource.envTypes = envTypes := by
    exact Option.some.inj (Hsource.typesAdded.symm.trans hadded)
  have hordered := henvTypes.ordered
  have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      sc.type.containsAnyConst r.restorableNames = false := by
    intro family hfamily sc hsc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types family hfamily
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
    obtain ⟨u, hu⟩ := hC.wf
    rw [htypesEq] at hu
    exact (hu.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
  refine ⟨envTypes, auxiliaries, hadded, henvTypes,
    auxiliarySpecializations_names Haux Hexpansion,
    auxiliarySpecializations_headNames Haux Hexpansion,
    auxiliarySpecializations_certified Haux,
    fun params hparams => auxiliarySpecializations_wellFormed Haux henvTypes params hparams,
    auxiliarySpecializations_wellFormed Haux henvTypes _ hlink,
    auxiliarySpecializations_scoped Haux Hexpansion hsuffixNodup,
    fun U params => auxiliarySpecializations_directFamilies Haux U params,
    hctorNames, D.recursorName, ?_⟩
  intro Huniform
  refine Lean4Lean.List.Forall₂.flip ?_
  refine Lean4Lean.List.Forall₂.imp (fun family lowered h => ?_)
    (Lean4Lean.List.Forall₂.and_mem Hrestoring)
  obtain ⟨h, hfamily, hlowered⟩ := h
  refine Lean4Lean.List.Forall₂.flip ?_
  refine Lean4Lean.List.Forall₂.imp (fun sc lc hc => ?_)
    (Lean4Lean.List.Forall₂.and_mem h)
  obtain ⟨hc, hsc, hlc⟩ := hc
  have hr : r.expr lc.type = some sc.type :=
    hc.restore (hsourceFree family hfamily sc hsc) (Huniform lowered hlowered lc hlc)
  exact ⟨hr, sc.type, hr, fun _ h => h⟩

end VerifyInductive

end Lean4Lean
