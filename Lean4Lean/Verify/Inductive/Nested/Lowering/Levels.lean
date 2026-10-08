import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructorTypes

/-! Universe arguments of the auxiliary occurrences in the lowered constructor
types of a validated nested run.

The executable lowering emits every auxiliary occurrence at `state.lvls`,
which is initialised to the declaration's level parameters and never modified.
The relational traces record this through `NestedAuxLE` (which fixes `lvls`),
the `lvls` fields of `LoweredConstructorTranslation`,
`LoweredConstructorMapping` and `NestedLoweringRun`, and the universe-argument
premise of the replacement leaves in
`NestedLoweringResultClosed.originalExpansionsAboveLvls`. Projected through
the translation, every replacement hit is a level leaf
(`NestedReplacementFinalTrace.levelLeaf`), so the lowered constructor types of
the source families use the auxiliary family and constructor names only at
`VLevel.params sourceDecl.uvars` (`NestedValidatedRunResult.loweredConstructorLevels`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- **Every replacement hit at the declaration's universe parameters is a
level leaf.** A hit emitted while the lowering state carries the universe
arguments `lparams.map .param` translates to an auxiliary head at
`VLevel.params`; its common-parameter arguments are bound variables, and its
trailing arguments copy the source's up to an expansion whose leaves are level
leaves again. -/
theorem NestedReplacementFinalTrace.levelLeaf
    {names : List Name} {sourceDecl : VInductDecl} {lparams : List Name}
    {result : Lean4Lean.ElimNestedInductive.Result}
    (hlparams : lparams.Nodup) (huvars : sourceDecl.uvars = lparams.length)
    (hparamsSize : result.params.size = sourceDecl.nparams)
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)))
    {lctx : LocalContext} {As : Array Expr}
    {input state output nextState traceFinalState depth fieldDepth sourceValue
      targetValue sourceCtx targetCtx}
    (Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input state
      output nextState result traceFinalState)
    (Hctx : NestedExpansionLookupCtx
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)) depth sourceCtx targetCtx)
    (selection : LocalForallSelection lctx As)
    (Harity : As.size = result.params.size)
    (Hdepth : depth = selection.fvars.length + fieldDepth)
    (HtargetParams : SelectedParameterTargets selection.fvars fieldDepth targetCtx)
    (HsourceExpr : TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue)
    (HtargetExpr : TrExprS targetTypesVEnv lparams targetCtx output targetValue)
    (hlvls : state.lvls = lparams.map Level.param) :
    VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars) depth sourceValue
      targetValue := by
  have hselectionLength : selection.fvars.length = sourceDecl.nparams := by
    calc
      selection.fvars.length = As.size := selection.size.symm
      _ = result.params.size := Harity
      _ = sourceDecl.nparams := hparamsSize
  have HbaseDepth : sourceDecl.nparams ≤ depth := by
    rw [Hdepth, ← hselectionLength]
    omega
  rcases Htrace.targetSpine selection Harity HtargetParams hparamsSize HtargetExpr with ⟨T⟩
  rcases T.sourceSpine HsourceExpr with ⟨S⟩
  have Htrailing := TrExprS.forall₂_abstractExpansionAbove Hlift Hctx HbaseDepth
    S.trailingTranslation T.trailingTranslation
  have hauxLevels : T.auxiliaryLevels = VLevel.params sourceDecl.uvars := by
    have h := T.auxiliaryLevelsTranslation
    rw [T.concreteAuxLevels_eq, hlvls,
      checkInductiveTypes.loopInd.VLevel.mapM_ofLevel_paramNames,
      Lean4Lean.VerifyInductive.List.map_param_idxOf_eq_params hlparams] at h
    rw [huvars]
    exact (Option.some.inj h).symm
  intro hs
  rw [S.sourceValue_eq, VExpr.containsAnyConst_mkApps_eq_false_iff] at hs
  rw [T.targetValue_eq, VExpr.constLevelsAt_mkApps]
  refine ⟨fun _ => hauxLevels, ?_⟩
  intro arg harg
  rcases List.mem_append.mp harg with hparam | htrailing
  · simp only [VInductDecl.paramVars, List.mem_map] at hparam
    obtain ⟨_, _, rfl⟩ := hparam
    trivial
  · obtain ⟨source, hsource, Hexp⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Htrailing arg htrailing
    exact Hexp.constLevelsAt (fun h => h)
      (hs.2 source (List.mem_append_right _ hsource))

/-- `FinalLoweredGeneratedFamilyOrigin.abstractExpansion` for an arbitrary
liftable leaf relation, with every replacement hit known to be emitted at the
universe arguments of the final lowering state. -/
theorem FinalLoweredGeneratedFamilyOrigin.abstractExpansionAboveLvls
    {prodEnv : Environment} {params : Array Expr} {nparams : Nat}
    {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType} {baseVEnv sourceTypesVEnv targetTypesVEnv : VEnv}
    {lparams : List Name} {target : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {decl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove decl.nparams leaf)
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      targetConcrete)
    (Hsource : FinalLoweredGeneratedFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (Htarget : TrInductiveType baseVEnv targetTypesVEnv lparams targetConcrete
      target)
    (Hmap : NestedAuxMapModels result finalState)
    (henv : baseVEnv.WF)
    (huvars : decl.uvars = lparams.length)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (HtargetTypesWF : targetTypesVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState' depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState' →
      NestedExpansionLookupCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue →
      TrExprS targetTypesVEnv lparams targetCtx output targetValue →
      state.lvls = finalState.lvls →
      leaf depth sourceValue targetValue) :
    VInductDecl.NestedTypeExpansion baseVEnv decl leaf Hsource.source target := by
  have Hmapping := H.finalMapping Hmap
  have Hheader : NestedTypeExpansionHeader baseVEnv decl Hsource.source target :=
    Hmapping.abstractHeaderExpansion Hsource.translation Htarget henv huvars
      Hsource.numIndices Hsource.resultLevel
  have hstep : H.stepState.lvls = finalState.lvls :=
    H.lowered.nestedAuxLE.lvls.symm.trans H.later.lvls.symm
  exact Hmapping.abstractExpansionAbove Hlift hstep Hsource.translation Htarget Hheader
    (Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.constructorsClosed
      Hsource.translation)
    HsourceTypesWF HtargetTypesWF hparamsSize hnparams Hhit

/-- **Universe arguments of the lowered constructor types of a validated
nested run.** Every auxiliary family or auxiliary constructor name occurs in
every lowered constructor type (of the source families and of the auxiliary
families alike) at the universe parameters of the declaration. -/
theorem NestedValidatedRunResult.loweredConstructorLevelsAll
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ lowered ∈ E.production.loweredDecl.types, ∀ lc ∈ lowered.ctors,
      lc.type.ConstLevelsAt
        (familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length))
        (VLevel.params sourceDecl.uvars) := by
  let names := familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)
  -- the auxiliary names are fresh in the source header environment
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoring wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      _hparamsSize, _D, _Hrestoring⟩
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hnames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      names := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ names, envTypes.constants name = none := by
    intro name hname
    apply hfreshAll
    rw [← hnames] at hname
    exact List.mem_append_left _ hname
  have HsourceCore := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at HsourceCore
  have htypesEq : E.nativeSource.envTypes = envTypes :=
    Option.some.inj (HsourceCore.typesAdded.symm.trans hadded)
  have hordered := henvTypes.ordered
  -- the lowering run and its translations
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.production
  have hc : P.c = E.productionContext := E.production_c
  have henv : P.c.env = sourceProdEnv :=
    (congrArg AddInductive.Context.env hc).trans E.productionContext_env
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams hc).trans
      E.productionContext_lparams
  have hnparams : P.nparams = nparams := E.production_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.production_initialEnv
  have hindTypes : P.indTypes = result.types.toArray := E.production_indTypes
  have hisUnsafe : P.isUnsafe = isUnsafe := E.production_isUnsafe_source
  have HcP : ContextWF P.c := by
    rw [hc]
    exact E.productionContextWF
  let initialState : Lean4Lean.ElimNestedInductive.State :=
    { lvls := P.c.lparams.map .param, newTypes := #[] }
  have Hlower : NestedLoweringResultClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := by
    simpa only [henv, hnparams, hlparams, initialState] using E.lowering
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let PhasePack := fun indTypes =>
    Sigma fun Hheaders : HeaderEnvironment P.c P.stats P.loweredDecl
        P.nparams P.isUnsafe P.depth P.initialEnv indTypes P.headerEnv =>
      Sigma fun R : OrdinaryConstructorCheck Hheaders P.ctorEnv =>
        RecursorCheck R.toConstructorCheck E.loweredEnv
  let Hpack : PhasePack result.types.toArray :=
    Eq.mp (congrArg PhasePack hindTypes)
      (⟨P.headers, P.constructors, P.production⟩ : PhasePack P.indTypes)
  let R := Hpack.2.1
  let Hprod := Hpack.2.2
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.nativeSource.envTypes
        E.nativeSource.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.nativeSourceDecl_eq] using E.nativeSource.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.1.context.venv
        R.declared.venvCtors := R.core
  have Hmetadata : MaterializedInductivePrefix sourceDecl P.loweredDecl := by
    simpa only [E.nativeSourceDecl_eq] using E.nativeSource.materialized
  have wfP : ves.WFCore P.c.env := by
    simpa only [henv] using wf
  have HbaseWF : P.initialEnv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.nativeSource.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.nativeSource.envTypes := by
    simpa only [hinitial, safety] using E.nativeSource.sourceAdded
  have HsourceTypesWF : E.nativeSource.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource HbaseWF
  have HtargetTypesWF : Hpack.1.context.venv.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget HbaseWF
  have Htranslations : ClosedNestedAuxiliaryTranslations
      E.nativeSource.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_native]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := rfl
  rcases Hrun.nativeGeneratedFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, -⟩
  have hparamsSize : result.params.size = P.nparams := Hrun.resultParamsSize
  have HliftLv : NestedExpansionLeafLiftAbove sourceDecl.nparams
      (VExpr.LevelLeaf names (VLevel.params sourceDecl.uvars)) :=
    VExpr.levelLeaf_liftAbove names (VLevel.params sourceDecl.uvars) sourceDecl.nparams
  have hsourceLength : sourceTypes.length = sourceDecl.types.length :=
    TrInductDeclCore.types_length Hsource
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  -- the source families
  have hprefix : ∀ lowered ∈ P.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors, lc.type.ConstLevelsAt names
        (VLevel.params sourceDecl.uvars) := by
    have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
        sc.type.containsAnyConst names = false := by
      intro family hfamily sc hsc
      obtain ⟨T, -, hT⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_r HsourceCore.types family hfamily
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
      obtain ⟨u, hu⟩ := hC.wf
      rw [htypesEq] at hu
      exact (hu.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
    have Hexpansions := NestedLoweringResultClosed.originalExpansionsAboveLvls HliftLv
      ⟨finalState, Hrun, Hcache, Hparams⟩ Hsource Htarget Hmetadata Hsources hempty
      HbaseWF
      (fun Htrace Hctx selection _ Harity Hdepth _ HtargetParams _ HsourceExpr
          HtargetExpr hlvls =>
        Htrace.levelLeaf P.production.lparamsNodup Hsource.uvars
          (hparamsSize.trans Hsource.nparams.symm) HliftLv Hctx selection Harity
          Hdepth HtargetParams HsourceExpr HtargetExpr hlvls)
    intro lowered hlowered lc hlc
    obtain ⟨family, hfamily, Hfamily⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hexpansions lowered hlowered
    obtain ⟨sc, hsc, Hctor⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hfamily.constructors lc hlc
    exact Hctor.type.constLevelsAt (fun h => h) (hsourceFree family hfamily sc hsc)
  -- the auxiliary families
  have hsuffix : ∀ lowered ∈ P.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors, lc.type.ConstLevelsAt names
        (VLevel.params sourceDecl.uvars) := by
    intro lowered hlowered lc hlc
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hlowered
    have hgeneratedLength := N.length
    simp only [List.length_drop] at hi
    have hresult : sourceTypes.length + i < result.types.length := by omega
    have htarget : sourceTypes.length + i < P.loweredDecl.types.length := by omega
    have hgenerated : i < N.generated.length := by omega
    have hloweredEq : lowered = P.loweredDecl.types[sourceTypes.length + i] := by
      rw [← hget, List.getElem_drop]
      congr 1
      omega
    rcases N.sourceAt i hgenerated hresult htarget with ⟨Horigin, Nsource, -⟩
    have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
      Htarget (sourceTypes.length + i) hresult htarget
    have Hmap := Hrun.resultAuxMapModelsFresh (by simpa using hempty)
    have Hexpansion := Horigin.abstractExpansionAboveLvls HliftLv Nsource.payload
      HtargetType Hmap HbaseWF Hsource.uvars HsourceTypesWF HtargetTypesWF
      Hrun.resultParamsSize Hsource.nparams.symm
      (fun Htrace Hctx selection _ Harity Hdepth _ HtargetParams _ HsourceExpr
          HtargetExpr hlvls =>
        Htrace.levelLeaf P.production.lparamsNodup Hsource.uvars
          (hparamsSize.trans Hsource.nparams.symm) HliftLv Hctx selection Harity
          Hdepth HtargetParams HsourceExpr HtargetExpr (hlvls.trans Hrun.lvls))
    rw [hloweredEq] at hlc
    obtain ⟨sc, hsc, Hctor⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hexpansion.constructors lc hlc
    have hscFree : sc.type.containsAnyConst names = false := by
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r
        Nsource.payload.translation.ctors sc hsc
      have h := hC.type
      rw [htypesEq] at h
      exact checkPositivityStep.TrExprS.noFreshConstsAtCheckingEnv hordered hfresh
        (Delta := []) (by trivial) h
    exact Hctor.type.constLevelsAt (fun h => h) hscFree
  intro lowered hlowered
  rw [← List.take_append_drop sourceDecl.types.length P.loweredDecl.types] at hlowered
  rcases List.mem_append.mp hlowered with h | h
  · exact hprefix lowered h
  · exact hsuffix lowered h

/-- `loweredConstructorLevelsAll` for the source families. -/
theorem NestedValidatedRunResult.loweredConstructorLevels
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ lowered ∈ E.production.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          (familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length))
          (VLevel.params sourceDecl.uvars) :=
  fun lowered hlowered =>
    E.loweredConstructorLevelsAll wf Hsources lowered (List.mem_of_mem_take hlowered)

/-- `loweredConstructorLevelsAll` for the auxiliary families. -/
theorem NestedValidatedRunResult.loweredAuxiliaryConstructorLevels
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ lowered ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          (familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length))
          (VLevel.params sourceDecl.uvars) :=
  fun lowered hlowered =>
    E.loweredConstructorLevelsAll wf Hsources lowered (List.mem_of_mem_drop hlowered)

/-- `loweredConstructorLevels` at the restoration heads of any specialisation
list whose head names are the auxiliary family and constructor names (as for
the specialisations of `NestedValidatedRunResult.loweredConstructors_of`): the
universe-level premise of `loweredConstructors_of`. -/
theorem NestedValidatedRunResult.loweredConstructorLevels_heads
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheadNames : auxiliaries.flatMap (·.headNames) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)) :
    ∀ lowered ∈ E.production.loweredDecl.types.take sourceDecl.types.length,
      ∀ lc ∈ lowered.ctors,
        lc.type.ConstLevelsAt
          ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
          (VLevel.params sourceDecl.uvars) := by
  rw [compilationRestoration_heads_auxiliary, hheadNames]
  exact E.loweredConstructorLevels wf Hsources

end VerifyInductive

end Lean4Lean
