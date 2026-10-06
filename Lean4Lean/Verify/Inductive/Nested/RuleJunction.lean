import Lean4Lean.Verify.Inductive.Nested.AssemblyNativeWhnf

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The restorable names of any restoration table of a run are restorable
names of any other one: both tables are keyed by the same auxiliary families
(`familyKey`, `familyLookup`) and constructors (`ctorInstalled`,
`ctorLookup`) of the lowered environment. -/
theorem RestorationTableData.restorableNames_subset
    {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}
    {auxiliaries auxiliaries' : List ContainerSpecialization}
    (D : RestorationTableData decl auxiliaries result env auxRec Us₀)
    (D' : RestorationTableData decl auxiliaries' result env auxRec Us₀) :
    ∀ n ∈ (compilationRestoration decl auxiliaries).restorableNames,
      n ∈ (compilationRestoration decl auxiliaries').restorableNames := by
  have hfamily : ∀ a ∈ auxiliaries, ∃ a' ∈ auxiliaries', a'.auxiliary = a.auxiliary := by
    intro a ha
    obtain ⟨nested, hnested⟩ := D.familyLookup a ha
    obtain ⟨a', ha', heq, -⟩ := D'.familyKey _ _ hnested
    exact ⟨a', ha', heq⟩
  intro n hn
  simp only [Restoration.restorableNames, compilationRestoration_heads_auxiliary,
    compilationRestoration_recursors_fst, List.mem_append, List.mem_flatMap,
    List.mem_map] at hn ⊢
  rcases hn with ⟨a, ha, hn⟩ | ⟨a, ha, rfl⟩
  · obtain ⟨a', ha', heq⟩ := hfamily a ha
    simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact .inl ⟨a', ha', by simp [ContainerSpecialization.headNames, heq]⟩
    · obtain ⟨info, hfind, hinduct⟩ := D.ctorInstalled a ha ctor hctor
      obtain ⟨ctor', hctor', hname⟩ :=
        D'.ctorLookup _ info hfind a' ha' (hinduct.trans heq.symm)
      refine .inl ⟨a', ha', ?_⟩
      simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map]
      exact .inr ⟨ctor', hctor', hname.symm⟩
  · obtain ⟨a', ha', heq⟩ := hfamily a ha
    exact .inr ⟨a', ha', by rw [heq]⟩

theorem _root_.Lean4Lean.InductiveSignature.Restoration.recursorName_cases (r : Restoration) (c : Name) :
    r.recursorName c = c ∨ ∃ p ∈ r.recursors, p.1 = c ∧ r.recursorName c = p.2 := by
  unfold Restoration.recursorName
  cases h : r.recursors.find? (fun pair => pair.1 == c) with
  | none => exact .inl rfl
  | some p =>
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    exact .inr ⟨p, hmem, by simpa using hp, rfl⟩

/-- **Freshness of the restorable names in a final assembly shape.** For any
final assembly shape of a validated nested run and any restoration table of
the run, the restorable names (auxiliary family and constructor names and
the lowered auxiliary recursor names) are absent from the shape's final
abstract environment: they are fresh in the source constructor environment
(`restorableNames_fresh_ctors`), the primary restored recursors keep their
lowered names `T.rec` (distinct from the auxiliary names by the lowered
declaration's name uniqueness), and the restored auxiliary recursor names
`Main.rec_k` are excluded by `HauxRecNames`. -/
theorem NestedValidatedRunResult.finalBaseVEnv_restorableNames_fresh
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HauxRecNames : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
        p.2 ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      C.finalBaseVEnv.constants n = none := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D', -, -⟩
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, hheadNames, -, -, -, hscoped, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have htypesEq : C.canonical.venvTypes = envTypes := by
    have h := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.canonical.venvCtors := by
    have h := C.canonical.ctorsAdded.abstract
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.canonical.recursorsAdded.abstract
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D' hscoped hwf
  let r' := compilationRestoration sourceDecl aux'
  intro n hn
  have hn' : n ∈ r'.restorableNames := D.restorableNames_subset D' n hn
  cases hc : C.finalBaseVEnv.constants n with
  | none => rfl
  | some ci =>
  exfalso
  rcases VEnv.addConstVals_lookup_origin hrecAdded hc with hbase | ⟨entry, hentry, hname, -⟩
  · simp only [VEnv.addProjections_constants] at hbase
    rw [hfreshCtors n hn'] at hbase
    cases hbase
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hentry
  obtain ⟨owner, -, s, t, Hstep, -, hrec, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hinfos e he
  -- the restored recursor name
  have hename : e.2.name = r'.recursorName
      (E.production.production.completed.canonicalGeneration.recursorName owner) := by
    simp only [Restoration.recursor, Option.pure_def, Option.bind_eq_bind] at hrec
    cases hty : r'.expr
        (E.production.production.completed.canonicalGeneration.recursor owner).type with
    | none => simp [r', hty] at hrec
    | some ty =>
      simp only [r', hty, Option.bind_some, Option.some.injEq] at hrec
      rw [← hrec]
      rfl
  have hgenName : E.production.production.completed.canonicalGeneration.recursorName owner =
      E.production.production.completed.generationSignature.families[owner].name.str "rec" :=
    E.production.loweredConstruction.consumedGeneration.names owner
  rw [hgenName] at hename
  obtain ⟨c, hcdef⟩ : ∃ c, c =
      E.production.production.completed.generationSignature.families[owner].name.str "rec" :=
    ⟨_, rfl⟩
  rw [← hcdef] at hename
  have hnoRec : ∀ p ∈ r'.recursors, p.2 ≠ n := by
    intro p hp hpn
    exact HauxRecNames aux' D' p hp (hpn ▸ hn')
  rcases r'.recursorName_cases c with hsame | ⟨p, hp, -, hpname⟩
  · rw [hsame] at hename
    have hnc : n = c := hname.symm.trans hename
    -- `c` is the lowered recursor name of a lowered family
    obtain ⟨src, hsrc, hsrcName, -⟩ :=
      E.production.loweredConstruction.consumedGeneration.models.family owner
    have hcRec : c ∈ E.production.loweredDecl.types.map (fun t => t.name.str "rec") :=
      List.mem_map.mpr ⟨src, hsrc, by
        rw [hcdef]; exact (congrArg (fun n : Name => n.str "rec") hsrcName).symm⟩
    simp only [Restoration.restorableNames, List.mem_append] at hn'
    rcases hn' with hhead | hfst
    · rw [compilationRestoration_heads_auxiliary, hheadNames] at hhead
      have hfam : n ∈ familyNames E.production.loweredDecl.types := by
        obtain ⟨t, ht, h⟩ := mem_familyNames.mp hhead
        exact mem_familyNames.mpr ⟨t, List.mem_of_mem_drop ht, h⟩
      exact (List.nodup_append.mp hnodup).2.2 _ hfam _ (hnc ▸ hcRec) rfl
    · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hfst
      have hsome : (r'.recursors.find? (fun pair => pair.1 == c)).isSome := by
        rw [List.find?_isSome]
        exact ⟨q, hq, by simp [hqn, hnc]⟩
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hsome
      have hrn : r'.recursorName c = q'.2 := by
        unfold Restoration.recursorName
        rw [hq']
      exact hnoRec q' (List.mem_of_find?_eq_some hq') (hrn.symm.trans (hsame.trans hnc.symm))
  · exact hnoRec p hp (hpname ▸ hename ▸ hname)

/-- **The rule junction `Hrules` of `assemblyNative_of_run`**, from the
restored-auxiliary-recursor name hypothesis `HauxRecNames` (see
`finalBaseVEnv_restorableNames_fresh`) and the rule-realization hypothesis
`HruleShape`: some final assembly shape of the run has rule lists realizing
the executable restored rules in its final abstract environment. The
freshness conjunct is derived for that shape. -/
theorem NestedValidatedRunResult.hrules_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HauxRecNames : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
        p.2 ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (HruleShape : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules)) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          C.finalBaseVEnv.constants n = none) ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) := by
  intro auxiliaries D
  obtain ⟨C, hC, HC⟩ := HruleShape auxiliaries D
  exact ⟨C, hC, E.finalBaseVEnv_restorableNames_fresh wf Hsources HauxRecNames C hC D, HC⟩

end VerifyInductive
end Lean4Lean
