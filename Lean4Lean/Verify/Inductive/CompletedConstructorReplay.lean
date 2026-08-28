import Lean4Lean.Verify.Inductive.CompletedConstructorPhases

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

def CompletedConstructorPhases.checkedRecursorParameterPrefixAt
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    exists tail, RecursorParamPrefix stats 0
      indTypes[familyIdx].ctors[ctorIdx].type tail :=
  R.parameterPrefixes.replay familyIdx hfamily ctorIdx hctor

def CompletedConstructorPhases.checkedRecursorConstructorTailAt
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    CheckedConstructorTailReplayAt R.headerVEnv c.lparams
      R.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] :=
  R.constructorTails.replay familyIdx hfamily ctorIdx hctor

/-- Select a mutual-family header after transporting its translation and
materialized certificate through either ordinary or atomic installation. -/
def CompletedConstructorPhases.checkedRecursorHeaderAt
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (hlparams : c.lparams.Nodup) :
    mkRecInfos.loopArgs1.CheckedRecursorHeaderAt R.context stats decl depth
      indTypes[familyIdx] familyIdx := by
  have htarget : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    familyIdx (by simpa using hfamily) htarget
  have hsourceLE : sourceEnv <= R.context.venv :=
    R.installation.headerLE.trans R.installation.constructorLE
  have Hsource := Htype.header.mono hsourceLE
  refine {
    target := decl.types[familyIdx]
    targetAt := by simp [htarget]
    materialized := R.materializedFinal
    sourceTranslation := Hsource
    targetLookup := ?_
    lparamsNodup := hlparams }
  have hheaderLookup : R.headerVEnv.constants decl.types[familyIdx].name =
      some decl.types[familyIdx].toVConstant := by
    apply VEnv.addConstVals_get R.installation.headerAbstract
    rw [R.headerValues]
    exact List.mem_map.mpr
      ⟨decl.types[familyIdx], List.getElem_mem htarget, rfl⟩
  exact R.installation.constructorLE.constants hheaderLookup

/-- The common constructor boundary supplies a typed constructor application
seed independently of whether its constants were installed ordinarily or as
an atomic primitive batch. -/
theorem CompletedConstructorPhases.checkedConstructorPrefixSeedAt
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    let Hbase := R.context
    let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
    let Hmaterialized := R.materializedFinal
    let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
    exists ctorVal tail tailTarget introTarget,
      ctorVal ∈ (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily)).ctors ∧
      ctorVal.name = indTypes[familyIdx].ctors[ctorIdx].name ∧
      RecursorParamPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls tail tailTarget ∧
      Rbase.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx tailTarget ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      introTarget = VExpr.mkApps
        (.const indTypes[familyIdx].ctors[ctorIdx].name
          (recursorDeclarationAbstractLevels c.lparams Helim))
        (recursorCanonicalVars stats.params.size) ∧
      Rbase.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx introTarget tailTarget ∧
      Nonempty
        (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Rbase.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams)
          (recursorConstructorTelescopeTarget ctorVal Helim)
          Hsuffix.parameterDecls tailTarget stats.params.size 0) := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.materializedFinal
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  have hheaderLE : R.headerVEnv <= Hbase.venv := by
    change R.headerVEnv <= R.context.venv
    exact R.installation.constructorLE
  have Hreplay := R.checkedRecursorConstructorTailAt
    familyIdx hfamily ctorIdx hctor
  have Hreplay' : CheckedConstructorTailReplayAt R.headerVEnv c.lparams
      Hmaterialized.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] := by
    rw [R.materializedFinal_parameterScope]
    exact Hreplay
  have Hrebased := Hreplay'.toRecursorContext
    Hmaterialized hheaderLE Helim
  change exists ctorVal tail tailTarget introTarget, _
  rcases Hrebased with
    ⟨ctorVal, tail, tailTarget, hctorMem, hctorName, hctorUvars,
      Hprefix, Htail, HtailType, ⟨Hsynthesis⟩⟩
  have hfamilyDecl : familyIdx < decl.types.length := by
    rw [← R.constructorTails.size_eq]
    exact hfamily
  have hctorConstantMem : ctorVal ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[familyIdx], List.getElem_mem hfamilyDecl, hctorMem⟩
  have hctorWFHeader : ctorVal.toVConstant.WF R.headerVEnv := by
    simpa [VConstant.WF, hctorUvars, R.materialized.uvars,
      R.materializedParams, R.headerParams] using
      R.checked.types ctorVal hctorConstantMem
  have hctorWF : ctorVal.toVConstant.WF Rbase.venv := by
    simpa [Rbase, Hbase] using hctorWFHeader.mono hheaderLE
  have hctorLookup : Rbase.venv.constants ctorVal.name =
      some ctorVal.toVConstant := by
    have hlookup : Hbase.venv.constants ctorVal.name =
        some ctorVal.toVConstant := by
      change R.context.venv.constants ctorVal.name =
        some ctorVal.toVConstant
      apply VEnv.addConstVals_get R.installation.constructorAbstract
      rw [R.constructorValues]
      exact hctorConstantMem
    simpa [Rbase] using hlookup
  let levels := recursorDeclarationAbstractLevels c.lparams Helim
  have hlevelsWF : ∀ level ∈ levels,
      level.WF (AddInductive.getRecLevelParams
        elimLevel c.lparams).length :=
    recursorDeclarationAbstractLevels_wf Helim
  have hlevelsLength : levels.length = ctorVal.uvars := by
    rw [recursorDeclarationAbstractLevels_length Helim, hctorUvars]
  have hsourceLevelsLength : stats.levels.length = ctorVal.uvars := by
    calc
      stats.levels.length = decl.uvars := Hmaterialized.levels
      _ = c.lparams.length := Hmaterialized.uvars.symm
      _ = ctorVal.uvars := hctorUvars.symm
  have htargetType : ctorVal.type.instL levels =
      (recursorConstructorTelescopeTarget ctorVal Helim).type :=
    VConstVal.type_instL_recursorDeclarationAbstractLevels
      hctorWF hctorUvars Helim
  have HintroType := Hsynthesis.canonicalApplication Rbase.checking.tr.wf
    hctorLookup hlevelsWF hlevelsLength htargetType
  have Hhead : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (.const ctorVal.name stats.levels) (.const ctorVal.name levels) := by
    exact TrExprS.const hctorLookup
      (Hmaterialized.recursorLevelTranslation hlparams Helim)
      hsourceLevelsLength
  have hcanonical :
      checkInductiveTypes.loopType.cachedParamVars stats.params.size 0 =
        recursorCanonicalVars Hsynthesis.params.length := by
    rw [checkInductiveTypes.loopType.cachedParamVars_zero_eq_recursorCanonicalVars,
      Hsynthesis.parameterCount]
  have Hargs : List.Forall₂
      (TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls)
      stats.params.toList
      (recursorCanonicalVars Hsynthesis.params.length) := by
    rw [← hcanonical]
    exact Hsuffix.narrowParams
  have Hintro : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (Expr.mkAppList (.const ctorVal.name stats.levels)
        stats.params.toList)
      (VExpr.mkApps (.const ctorVal.name levels)
        (recursorCanonicalVars Hsynthesis.params.length)) :=
    checkPositivityStep.TrExprS.mkAppList Rbase.checking.tr.wf.ordered
      Hsynthesis.scopeWF.toCtx Hhead Hargs ⟨tailTarget, HintroType⟩
  refine ⟨ctorVal, tail, tailTarget,
    VExpr.mkApps (.const ctorVal.name levels)
      (recursorCanonicalVars Hsynthesis.params.length),
    hctorMem, hctorName, Hprefix, Htail, HtailType, ?_, ?_, HintroType,
    ⟨Hsynthesis⟩⟩
  · simpa [Expr.mkAppN_eq_mkAppList, hctorName, Rbase, Hbase,
      Hmaterialized, Hsuffix] using Hintro
  · simp [levels, hctorName, Hsynthesis.parameterCount]

/-- Reinterpret the common checked seed in any later recursor context with
the retained parameter suffix. -/
theorem CompletedConstructorPhases.checkedConstructorRuntimeSeedAt
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    {current : AddInductive.Context}
    (Rcurrent : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henvCurrent : Rcurrent.venv = R.context.venv)
    {runtimeDepth : Nat}
    (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
      runtimeDepth)
    (hparameterDecls : HsuffixCurrent.parameterDecls =
      (R.materializedFinal.parameterSuffix.toRecursorContext
        Helim).parameterDecls)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    exists tail tailTarget introTarget,
      RecursorParamPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      Nonempty (CheckedConstructorOwnerNormalForm stats familyIdx tail) ∧
      tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx tail tailTarget ∧
      Rcurrent.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      Rcurrent.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let HsuffixBase := R.materializedFinal.parameterSuffix.toRecursorContext Helim
  rcases R.checkedConstructorPrefixSeedAt Helim hlparams familyIdx hfamily
      ctorIdx hctor with
    ⟨_ctorVal, tail, tailNarrow, introNarrow, _hmem, _hname,
      Hprefix, Htail, HtailType, Hintro, _HintroShape,
      HintroType, _Hsynthesis⟩
  rcases R.ownerNormalForms.replay familyIdx hfamily ctorIdx hctor with
    ⟨normalTail, HnormalPrefix, Hnormal⟩
  have htailEq : normalTail = tail := HnormalPrefix.tail_eq Hprefix
  subst normalTail
  have HtailCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls tail tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Htail
  have HtailTypeCurrent : Rcurrent.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HtailType
  have HtailParams : tail.FVarsIn
      (· ∈ ExprArrayFVarIds stats.params) := by
    exact HtailCurrent.fvarsIn.mono fun fv hfv => by
      rw [HsuffixCurrent.parameterDecls_fvars] at hfv
      simpa using hfv
  have HintroCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls
      (mkAppN
        (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
        stats.params) introNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Hintro
  have HintroTypeCurrent : Rcurrent.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx introNarrow tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HintroType
  rcases HsuffixCurrent.runtimeScope.transportTypedTerm
      Rcurrent.checking.tr.wf HintroCurrent HtailCurrent
      HintroTypeCurrent HtailTypeCurrent with
    ⟨introTarget, tailTarget, HintroRuntime, HtailRuntime,
      HintroTypeRuntime, HtailTypeRuntime⟩
  exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailParams,
    HtailRuntime, HtailTypeRuntime, HintroRuntime, HintroTypeRuntime⟩

/-- Enter the first mutual recursor pass from the completed constructor
boundary. -/
theorem CompletedConstructorPhases.loopInd1SemanticWF
    {alpha : Type} {Q : alpha -> Prop}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (k : Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams))
      (henvOut : Rout.venv = R.context.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut : HsuffixOut.parameterDecls =
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth)
      (Hbindings : RecInfoBindings cOut recInfos)
      (Horigins : RecInfoTypeOrigins cOut recInfos),
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes ->
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes ->
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes ->
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes ->
      (Hparams : BoundFVarArray cOut stats.params) ->
      Hbindings.NoAlias Hparams ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      RecInfoMinorsEmpty recInfos ->
      RecInfoBlueprintCounts recInfos ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      recInfos.size = indTypes.size ->
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] k
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.materializedFinal
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  let HstatsOrdinary :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader Hmaterialized
  let Hstats := HstatsOrdinary.toRecursorContext Helim
  let Hheaders : forall i (hi : i < indTypes.size),
      mkRecInfos.loopArgs1.CheckedRecursorHeaderAt Hbase stats decl depth
        indTypes[i] i := fun i hi =>
    R.checkedRecursorHeaderAt i hi hlparams
  have HparamsCtx : forall i (hi : i < indTypes.size),
      VEnv.IsDefEqCtx Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        ((Hheaders i hi).recursorParams Helim).reverse
        Hsuffix.parameterDecls.toCtx := by
    intro i hi
    have hmaterialized : (Hheaders i hi).materialized = Hmaterialized := rfl
    change VEnv.IsDefEqCtx Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      ((Hheaders i hi).recursorParams Helim).reverse
      (Hmaterialized.parameterSuffix.toRecursorContext
        Helim).parameterDecls.toCtx
    rw [← hmaterialized]
    exact (Hheaders i hi).recursorParamsContext Helim
  let HparamsBase : BoundFVarArray { c with env := ctorEnv } stats.params :=
    Hmaterialized.parameterSuffix.paramsBound
  let Hparams : BoundFVarArray { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } stats.params :=
    HparamsBase.monoFVars (by intro fv; exact id)
  have hparamsNodup : Hparams.fvars.Nodup := by
    change HparamsBase.fvars.Nodup
    exact Hmaterialized.parameterSuffix.paramsBound_nodup
  refine mkRecInfos.loopInd1.resultSemantics Hbase stats indTypes elimLevel
    Helim Hheaders hconsume 0 #[] k Rbase (by simp [Rbase, Hbase])
    Hsuffix HparamsCtx
    Hstats (RecInfoBindings.empty _) (RecInfoTypeOrigins.empty _)
    (RecursorTranslatedOriginTypes.empty Rbase)
    (RecInfoMajorTypeShapes.empty stats)
    (RecursorTranslatedOriginTypes.empty Rbase)
    (RecInfoMotiveTypeShapes.empty _ elimLevel)
    (RecInfoMotiveTelescopes.empty Rbase stats decl
      Hsuffix.parameterDecls.toCtx elimLevel)
    (RecursorTranslatedOriginTypeRows.empty Rbase) Hparams
    (RecInfoBindings.empty_noAlias _ Hparams hparamsNodup)
    (RecInfoOuterOrder.empty Hsuffix Hparams)
    (BindingContextLE.rebaseTypeCheckerLParams
      (BindingContextLE.refl { c with env := ctorEnv })
      c.typeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams))
    rfl (RecInfoArities.empty stats)
    RecInfoMinorsEmpty.empty RecInfoBlueprintCounts.empty ?_
  intro cOut outDepth recInfos Rout henvOut HsuffixOut hparameterDeclsOut
    HstatsOut Hbindings Horigins HmajorTypes HmajorShapes HmotiveTypes
    HmotiveShapes Htelescopes HindexRows HparamsOut HnoAlias Horder Harities
    Hempty Hblueprints Hroot hsize
  have Hroot' : BindingContextLE { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } cOut := by
    simpa using Hroot.rebaseTypeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams)
      cOut.typeCheckerLParams
  apply Hk recInfos Rout henvOut HsuffixOut hparameterDeclsOut HstatsOut
    Hbindings Horigins HmajorTypes HmajorShapes HmotiveTypes HmotiveShapes (by
      simpa [hparameterDeclsOut] using Htelescopes) HindexRows HparamsOut
    HnoAlias Horder Harities Hempty Hblueprints Hroot'
  simpa using hsize

theorem CompletedConstructorPhases.mkRecInfosWF
    {alpha : Type} {Q : alpha -> Prop}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : forall {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' ->
      e'.containsAnyConst (decl.types.map (·.name)) = false ->
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (k : Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.context.venv ->
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) ->
      HsuffixOut.parameterDecls =
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls ->
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth ->
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx ->
      (Hbindings : RecInfoBindings cOut recInfos) ->
      (Horigins : RecInfoTypeOrigins cOut recInfos) ->
      RecInfoRuleBlueprintOrigins stats recInfos Horigins ->
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins ->
      RecInfoMinorSourceAlignment stats indTypes Horigins ->
      RecInfoMinorSemanticAlignment Rout Horigins
        HsuffixOut.parameterDecls ->
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes ->
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes ->
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes ->
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes ->
      (Hparams : BoundFVarArray cOut stats.params) ->
      Hbindings.NoAlias Hparams ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      (forall i, i < recInfos.size ->
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) ->
      RecursorCardinalityCertificate stats recInfos decl ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  unfold AddInductive.mkRecInfos
  refine R.loopInd1SemanticWF elimLevel Helim hlparams hconsume
    (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) ?_
  intro cFrames frameDepth recInfos Rframes henvFrames HsuffixFrames
    hparameterDeclsFrames HstatsFrames HbindingsFrames HoriginsFrames
    HmajorTypesFrames HmajorShapesFrames HmotiveTypesFrames
    HmotiveShapesFrames HtelescopesFrames HindexRowsFrames HparamsFrames
    HnoAliasFrames HorderFrames HaritiesFrames HemptyFrames
    HblueprintCountsFrames HrootFrames hsizeFrames
  have hrecordsFrames : recInfos.size = stats.indConsts.size := by
    calc
      recInfos.size = indTypes.size := hsizeFrames
      _ = indTypes.toList.length := by simp
      _ = decl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = stats.indConsts.size := HstatsFrames.types_size.symm
  refine mkRecInfos.loopInd2.resultSemantics
    (root := { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams }) (Q := Q)
    stats indTypes 0 recInfos k Rframes HsuffixFrames
    HstatsFrames hconsume hlit.available
    (checkInductiveTypes.loopType.MLCtxOnlyLams.noIndConsts
      Rframes.onlyLams) hproj
    HbindingsFrames HoriginsFrames
    (RecInfoRuleBlueprintOrigins.ofEmpty HoriginsFrames HemptyFrames
      HblueprintCountsFrames)
    (RecInfoRuleBlueprintSemanticOrigins.ofEmpty Rframes decl HoriginsFrames
      HemptyFrames HblueprintCountsFrames elimLevel)
    (RecInfoMinorSourceAlignment.ofEmpty HoriginsFrames HemptyFrames)
    (RecInfoMinorSemanticAlignment.ofEmpty
      (parameterDecls := HsuffixFrames.parameterDecls)
      Rframes HoriginsFrames HemptyFrames)
    HmajorTypesFrames HmajorShapesFrames HmotiveTypesFrames
    HmotiveShapesFrames HtelescopesFrames HindexRowsFrames HparamsFrames
    HnoAliasFrames HorderFrames HrootFrames hsizeFrames hrecordsFrames
    HaritiesFrames ?_ ?_ ?_ ?_
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
      hparameterDeclsCurrent familyIdx hfamily ctor hctor
    rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
    rcases R.checkedConstructorRuntimeSeedAt elimLevel Helim hlparams
        Rcurrent (henvCurrent.trans henvFrames) HsuffixCurrent
        (hparameterDeclsCurrent.trans hparameterDeclsFrames) familyIdx
        hfamily ctorIdx hctorIdx with
      ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
        Htail, HtailType, Hintro, HintroType⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
      Htail, HtailType, Hintro, HintroType⟩
  · intro cOut outDepth out Rout henvOut HsuffixOut hparameterDeclsOut
      HstatsOut hctxOut HbindingsOut HoriginsOut HblueprintsOut
      HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut houtSize houtCounts
      HmajorTypesOut HmajorShapesOut
      HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
      HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
    exact Hk out Rout (henvOut.trans henvFrames) HsuffixOut
      (hparameterDeclsOut.trans hparameterDeclsFrames) HstatsOut hctxOut
      HbindingsOut HoriginsOut HblueprintsOut HblueprintSemanticsOut HminorSourcesOut
      HminorSemanticsOut
      HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
      HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
      HaritiesOut houtCounts
      (RecursorCardinalityCertificate.ofResult R.core R.materialized
        houtSize houtCounts HaritiesOut)
      HrootOut

/-- Exact recursor-info prefix from the completed constructor boundary. -/
theorem CompletedConstructorPhases.getElimLevelMkRecInfosWF
    {alpha : Type} {Q : alpha -> Prop}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : forall {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' ->
      e'.containsAnyConst (decl.types.map (·.name)) = false ->
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (k : Level -> Bool -> Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall elimLevel,
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) ->
      forall kTarget,
      forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.context.venv ->
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) ->
      HsuffixOut.parameterDecls =
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls ->
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth ->
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx ->
      (Hbindings : RecInfoBindings cOut recInfos) ->
      (Horigins : RecInfoTypeOrigins cOut recInfos) ->
      RecInfoRuleBlueprintOrigins stats recInfos Horigins ->
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins ->
      RecInfoMinorSourceAlignment stats indTypes Horigins ->
      RecInfoMinorSemanticAlignment Rout Horigins
        HsuffixOut.parameterDecls ->
      RecursorTranslatedOriginTypes Rout Horigins.majorTypes ->
      RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes ->
      RecursorTranslatedOriginTypes Rout Horigins.motiveTypes ->
      RecInfoMotiveTypeShapes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.materializedFinal.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      RecursorTranslatedOriginTypeRows Rout Horigins.indexTypes ->
      (Hparams : BoundFVarArray cOut stats.params) ->
      Hbindings.NoAlias Hparams ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      (forall i, i < recInfos.size ->
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) ->
      RecursorCardinalityCertificate stats recInfos decl ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      (k elimLevel kTarget recInfos cOut).WF Q) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel
          (k elimLevel kTarget)) { c with env := ctorEnv }).WF Q := by
  have Helim := AddInductive.getElimLevel.WF stats indTypes
    { c with env := ctorEnv }
  exact Helim.bind fun elimLevel hElim => by
    simp only [AddInductive.withTypeCheckerLParams, withReader]
    exact (show (AddInductive.isKTarget stats indTypes
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF
        fun _ => True from fun _ _ => trivial).bind fun kTarget _ =>
      R.mkRecInfosWF elimLevel hElim hlparams hconsume hlit hproj
        (k elimLevel kTarget) (Hk elimLevel hElim kTarget)

end VerifyInductive
end Lean4Lean
