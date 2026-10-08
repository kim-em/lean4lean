import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructorTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryHeaders
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryConstructors
import Lean4Lean.Std.List

/-! Constructor restoration and `CompilationData` of a validated nested run,
for the specializations of `NestedValidatedRunResult.restorationTablesRestoring`.

`NestedValidatedRunResult.sourceConstructors_of_evidence`,
`NestedValidatedRunResult.loweredConstructors_of` and
`NestedValidatedRunResult.auxiliaryFamilies_of` each speak about a
specialization list obtained from an existential, so their conclusions cannot
be combined directly. Here all three arguments are run on the single list
supplied by `restorationTablesRestoring`. The proofs of the lowered
constructor restoration and of the auxiliary family correspondence are the
tails of `loweredConstructors_of` and `auxiliaryFamilies_of`, instantiated at
that list.

The universe-level premise of `loweredConstructors_of` (`ConstLevelsAt`) is
`NestedValidatedRunResult.loweredConstructorLevels_heads`, and the
restoration of the auxiliary constructor types is
`NestedValidatedRunResult.auxiliaryConstructors_of_evidence`. What remains
open for `NestedCompilationPending` (`compilationData_of_pending'`):

* `normalizedTotal`: restoration is defined on the normalized constructor
  types (of the source and of the auxiliary families),
* the restored recursor and equation lists. -/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- The facts of `containerSpecializationFacts` (as repeated in the prefix of
`NestedValidatedRunResult.loweredConstructors_of`), for the specializations of
`restorationTablesRestoring`, conjoined with an arbitrary further fact. -/
theorem NestedValidatedRunResult.restorationPrefix_of {X : Prop}
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hX : X) :
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      auxiliaries.flatMap (·.headNames) =
        familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
      ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (∀ params : List VExpr,
        VEnv.IsDefEqCtx envTypes sourceDecl.uvars [] params.reverse
          E.production.headers.commonParameterContext →
        ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl params) ∧
      (∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
        E.production.constructors.completed.parameterScope.toCtx.reverse) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ (U : Nat) (params : List VExpr), ∃ direct,
        auxiliaries.mapM (fun a => a.specializedFamily U params) = some direct ∧
        List.Forall₂ (DirectFamilyShape U) auxiliaries direct) ∧
      (∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
        result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            (a.constructorName ctor)) ∧
      (∀ name, (compilationRestoration sourceDecl auxiliaries).recursorName name =
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.find? name).getD
          name) ∧
      X := by
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
    have hsame := Lean4Lean.List.nodup_map_inj hheadsNodup' hmemB hmemA hba
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
  exact ⟨hadded, henvTypes,
    auxiliarySpecializations_names Haux Hexpansion,
    auxiliarySpecializations_headNames Haux Hexpansion,
    auxiliarySpecializations_certified Haux,
    fun params hparams => auxiliarySpecializations_wellFormed Haux henvTypes params hparams,
    auxiliarySpecializations_wellFormed Haux henvTypes _ hlink,
    auxiliarySpecializations_scoped Haux Hexpansion hsuffixNodup,
    fun U params => auxiliarySpecializations_directFamilies Haux U params,
    hctorNames, D.recursorName, hX⟩

/-- The lowered constructor types of the source families restore
syntactically to the source constructor types, for the specializations of
`restorationTablesRestoring`, given the universe-level premise of
`NestedValidatedRunResult.loweredConstructors_of`. -/
theorem NestedValidatedRunResult.loweredConstructors_of_evidence
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envTypes.constants name = none)
    (Hrestoring : List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length))
    (hlevels : ∀ lowered ∈ E.production.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
          (VLevel.params sourceDecl.uvars)) :
    List.Forall₂ (fun lowered source : VInductiveType =>
        List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
            envTypes.SimAt sourceDecl.uvars [] restored sc.type)
          lowered.ctors source.ctors)
      (E.production.loweredDecl.types.take sourceDecl.types.length) sourceDecl.types := by
  let r := compilationRestoration sourceDecl auxiliaries
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
  refine Lean4Lean.List.Forall₂.flip ?_
  refine Lean4Lean.List.Forall₂.imp (fun family lowered h => ?_)
    (Lean4Lean.List.Forall₂.and_mem Hrestoring)
  obtain ⟨h, hfamily, hlowered⟩ := h
  refine Lean4Lean.List.Forall₂.flip ?_
  refine Lean4Lean.List.Forall₂.imp (fun sc lc hc => ?_)
    (Lean4Lean.List.Forall₂.and_mem h)
  obtain ⟨hc, hsc, hlc⟩ := hc
  have hr : r.expr lc.type = some sc.type :=
    hc.restore (hsourceFree family hfamily sc hsc) (hlevels lowered hlowered lc hlc)
  exact ⟨sc.type, hr, fun _ h => h⟩

/-- The `auxiliaryFamilies` field of `NestedCompilationPending` for any
specialization list with exact lowering evidence, modulo the restoration of
the auxiliary constructor types (the tail of
`NestedValidatedRunResult.auxiliaryFamilies_of`). -/
theorem NestedValidatedRunResult.auxiliaryFamiliesField_of_evidence
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (Hrestores : ∀ envTypes direct,
        (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
          sourceDecl.typeConstants = some envTypes →
        auxiliaries.mapM (fun a => a.specializedFamily sourceDecl.uvars
          E.production.compilationSignature.params) = some direct →
        List.Forall₂ (fun normalized family : VInductiveType =>
            List.Forall₂ (fun normalized ctor : VConstVal =>
              RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes
                sourceDecl.uvars normalized.type ctor.type)
              normalized.ctors family.ctors)
          (E.production.compilationSignature.declaration.types.drop
            sourceDecl.types.length) direct) :
    ∀ envTypes direct,
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes →
      auxiliaries.mapM (fun a => a.specializedFamily sourceDecl.uvars
        E.production.compilationSignature.params) = some direct →
      List.Forall₂ (fun normalized family : VInductiveType =>
          normalized.numIndices = family.numIndices ∧
          normalized.resultLevel ≈ family.resultLevel ∧
          (∃ domains body level exprType, level ≈ normalized.resultLevel ∧
            envTypes.IsDefEq sourceDecl.uvars [] family.type
              (VExpr.wrapForalls domains body) exprType ∧
            envTypes.IsDefEq sourceDecl.uvars domains.reverse body (.sort level)
              (.sort (.succ level))) ∧
          List.Forall₂ (fun normalized ctor : VConstVal =>
            normalized.name = ctor.name ∧ normalized.uvars = ctor.uvars ∧
            RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes
              sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (E.production.compilationSignature.declaration.types.drop
          sourceDecl.types.length) direct := by
  intro envTypes' direct htypes' hmapM
  have henvEq : envTypes' = envTypes := Option.some.inj (htypes'.symm.trans hadded)
  subst envTypes'
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.production.constructors.completed.parameterScope.toCtx.reverse).reverse
      E.production.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorPhasesResult.completed_parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.consumedGeneration.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  have hsourceUvars : sourceDecl.uvars = E.production.c.lparams.length := by
    have h := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production_c, E.productionContext_lparams]
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars :=
    E.production.constructors.core.uvars.trans hsourceUvars.symm
  have hloweredNparams : E.production.loweredDecl.nparams = sourceDecl.nparams := by
    have h := E.nativeSource.core.nparams
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production.constructors.core.nparams, E.production_nparams]
  have hparams : E.production.compilationSignature.params =
      E.production.constructors.completed.parameterScope.toCtx.reverse :=
    E.production.loweredConstruction.consumedGeneration.params
  refine auxiliaryFamilies_of_evidence (base := ves.venv (if isUnsafe then .unsafe else .safe))
    (headerParams := E.production.headers.headers.params)
    henvTypes (VEnv.addConstVals_le hadded) Haux Hexpansion ?_ ?_ hloweredUvars
    hloweredNparams (hparams ▸ hlink) ?_ hmapM (Hrestores envTypes direct htypes' hmapM)
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      (Lean4Lean.List.forall₂_drop Hmodels.families sourceDecl.types.length)
  · intro t ht
    have h := E.production.headers.headers.typeShapes t (List.mem_of_mem_drop ht)
    generalize E.production.headers.headers.params = hp at h ⊢
    rwa [hinit] at h
  · intro n hn c hc
    rw [E.production.compilationSignature.declaration_ctor_uvars n
      (List.mem_of_mem_drop hn) c hc, Hmodels.uvars, hloweredUvars]

end VerifyInductive

end Lean4Lean
