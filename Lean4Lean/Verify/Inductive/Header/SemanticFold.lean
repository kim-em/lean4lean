import Lean4Lean.Verify.Inductive.Header.SemanticMaterialization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopInd

/-- The first successful family initializes declaration-independent semantic
header accumulation.  Both the telescope and zero-binder paths recover the
same payload: exact header translation, arity, result universe, common
parameters, and `SynthesizedHeader`. -/
theorem firstStep.initializesSemanticAccumulator
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams : Nat}
    {alpha : Type} (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel} {params : List VExpr},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      c'.lparams = c.lparams →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      Hc'.venv = Hc.venv →
      stats'.levels = stats.levels →
      stats'.nindices = stats.nindices →
      stats'.indConsts = stats.indConsts →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams params resultLevel [indTypes[0]]) →
      Hsemantic.metadata = [(nindices, resultLevel)] →
      VLevel.ofLevel c'.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats' nparams nindices →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' nindices →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' params nindices →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes 1
        (updatedStats stats' c'.lctx resultSort true nindices
          indTypes[0].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
      stats k c).WF Q := by
  let Hraw := CheckedSourceHeaderAccumulator.empty Hc.venv c.lparams
  apply stepPrefix.accumulatesRawHeaders
    (nparams := nparams) (stats := stats) (k := k) (Q := Q)
    Hc Hraw hidx
  intro checkedType Hchecked _Hprefix normalized _hbelow htype
  let sourceSkeleton :=
    checkInductiveTypes.loopType.headerSkeleton Hchecked.target
  by_cases hforall : ∃ name dom body bi,
      normalized = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have Htarget := CheckedSourceHeaderTranslation.checkedFirstForall
      Hchecked hctx htype
    have HtargetSkeleton : TrSourceConst Hc.venv c.lparams
        indTypes[0].name indTypes[0].type sourceSkeleton.toVConstVal := by
      change TrSourceConst Hc.venv c.lparams indTypes[0].name
        indTypes[0].type Hchecked.target
      exact Htarget
    rcases initialHeaderSynthesisState Hc hctx
        (target := sourceSkeleton) HtargetSkeleton
        Hchecked.typing htype with
      ⟨normalized', hnormalized', ⟨Hsynthesis⟩⟩
    have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
        Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
      checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
    let Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
        Hc stats 0 :=
      checkInductiveTypes.loopType.ParameterContextSuffix.empty
        Hc hctx hparams
    apply checkInductiveTypes.loopType.firstHeaderSynthesisWF
      (Us := c.lparams) (target := sourceSkeleton)
      (nparams := nparams) (stats := stats)
      (type := .forallE name dom body bi) (current := normalized')
      (i := 0) (nindices := 0) (c := c)
      (k := fun type stats nindices => show AddInductive.M alpha from do
        let type ← TypeChecker.ensureSort type
        let mut stats := stats
        let resultLevel := type.sortLevel!
        if stats.indConsts.isEmpty then
          let lctx := (← read).lctx
          stats := { stats with
            lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
        else if !resultLevel.isEquiv stats.resultLevel then
          throw <| .other
            "mutually inductive types must live in the same universe"
        stats := { stats with
          nindices := stats.nindices.push nindices
          indConsts := stats.indConsts.push
            (.const indTypes[0].name stats.levels) }
        AddInductive.checkInductiveTypes.loopInd nparams indTypes 1 stats k)
      (Q := Q) hconsume
      (Hresult := by
        intro c' stats' type' current' i' nindices' Hc' henv' hsafety'
          hlparams' hallowPrimitive' hfuel' hempty' hlevels' hnindices'
          hconsts' hvenv' hnotforall hi' Hcache' Hsuffix' Hsynthesis' htype'
        subst i'
        apply firstResult.synthesizesHeader k Q Hc' hempty'
          Hsynthesis' htype'
        · exact (congrArg List.length hlparams').trans Htarget.uvars.symm
        · intro resultSort resultLevel hofLevel Hheader Hambient
          have Htranslation : TrSourceConst Hc'.venv c'.lparams
              indTypes[0].name indTypes[0].type Hchecked.target := by
            simpa [hvenv', hlparams'] using Htarget
          let Hsemantic :=
            checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.first
              indTypes[0] Hchecked.target nindices' resultLevel
              Htranslation
              (by simpa [sourceSkeleton, Htarget.uvars, hlparams'] using Hheader)
          exact Hrec Hc' henv' hsafety' hlparams' hallowPrimitive' hfuel'
            hvenv'.symm hlevels' hnindices' hconsts' Hsemantic rfl hofLevel
            Hcache' Hsuffix'
            (by simpa [Hsynthesis'.indexCount] using Hambient))
      Hc rfl rfl rfl rfl rfl hempty rfl rfl rfl rfl Hcache Hsuffix
      Hsynthesis
      (by
        intro _
        exact ⟨List.eq_nil_of_length_eq_zero Hsynthesis.indexCount, rfl⟩)
      hnormalized'
  · cases hfuel : c.fuel.inductiveFuel with
    | zero => exact checkInductiveTypes.loopType.zero.WF
    | succ fuel =>
      by_cases hzero : 0 = nparams
      · subst nparams
        apply checkInductiveTypes.loopType.result.WF
          (Q := Q) hforall rfl
        rcases htype with ⟨current, htype', hcurrentEq⟩
        apply firstResult.WF
          (nparams := 0) (indTypes := indTypes) (dIdx := 0)
          (indName := indTypes[0].name) (nindices := 0)
          k Q Hc hempty htype'
        intro resultSort hsorted
        have hsortedRuntime := TrExpr.defeq Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf.toCtx hsorted hcurrentEq
        rcases CheckedSourceHeaderTranslation.checkedTerminal
            Hchecked hsortedRuntime with
          ⟨resultLevel, hofLevel, Htarget⟩
        rcases initialHeaderNormalization Hc hctx
            (target := sourceSkeleton) Hchecked.source Hchecked.typing
            ⟨current, htype', hcurrentEq⟩ with
          ⟨normalized', exprType, hnormalized', hheader⟩
        have hnormalizedEq := hnormalized'.uniq Hc.checking.tr.wf
          (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) htype'
        have hnormalizedEq' : Hc.venv.IsDefEqU c.lparams.length []
            normalized' current := by
          simpa [hctx, VLCtx.toCtx] using hnormalizedEq
        have htargetCurrentU := hheader.toU.trans Hc.checking.tr.wf
          (by trivial) hnormalizedEq'
        have htargetType : Hc.venv.IsType c.lparams.length []
            sourceSkeleton.type := by
          have hwf := Htarget.wf
          change Hc.venv.IsType Hchecked.target.uvars []
            Hchecked.target.type at hwf
          rw [Htarget.uvars] at hwf
          exact hwf
        rcases htargetType with ⟨exprType, htargetHasType⟩
        have htargetCurrent := htargetCurrentU.of_l Hc.checking.tr.wf
          (by trivial) htargetHasType
        have hcurrentType : Hc.venv.IsType c.lparams.length [] current := by
          rcases TrExpr.sort_result Hc.checking.tr.wf
              Hc.mlctx_wf.tr.wf.toCtx hsorted with
            ⟨_, _, hcurrent⟩
          simpa [hctx, VLCtx.toCtx] using (show Hc.venv.IsType c.lparams.length
            Hc.mlctx.vlctx.toCtx current from ⟨_, hcurrent.hasType.1⟩)
        have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
            [] Hc.mlctx.vlctx.toCtx := by
          simpa [hctx, VLCtx.toCtx] using (VEnv.IsDefEqCtx.refl
            (env := Hc.venv) (U := c.lparams.length)
            (by trivial : OnCtx ([] : List VExpr)
              (Hc.venv.IsType c.lparams.length)))
        let Hsynthesis :=
          checkInductiveTypes.loopType.HeaderSynthesisCertificate.empty
            hctxEq hcurrentType htargetCurrent
        have Hheader := Hsynthesis.synthesizedHeader
          (uvars := c.lparams.length) rfl hofLevel hsorted
        let Hsemantic :=
          checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.first
            indTypes[0] Hchecked.target 0 resultLevel Htarget
            (by simpa [sourceSkeleton] using Hheader)
        have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
            Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
          checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
        let Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
            Hc stats 0 :=
          checkInductiveTypes.loopType.ParameterContextSuffix.empty
            Hc hctx hparams
        exact Hrec Hc rfl rfl rfl rfl rfl rfl rfl rfl rfl Hsemantic rfl
          hofLevel Hcache Hsuffix
          (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
            Hsynthesis.context)
      · exact checkInductiveTypes.loopType.parameterMismatch.WF
          (Q := Q) hforall hzero

/-- A completed noninitial narrow telescope appends one declaration-independent
semantic header. -/
theorem laterResult.snocsSemanticNarrow
    {source : InductiveType} {target : VConstVal}
    {priorSources : List InductiveType}
    {narrowCurrent fullCurrent : VExpr} {scope : VLCtx}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {alpha : Type} (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (Htranslation : TrSourceConst Hc.venv c.lparams
      source.name source.type target)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel priorSources)
    (Hsynthesis : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      Hc.venv c.lparams
        (checkInductiveTypes.loopType.headerSkeleton target)
        scope narrowCurrent nparams nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullCurrent)
    (hparams : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      (HsemanticNext :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc.venv c.lparams nparams commonParams commonLevel
            (priorSources ++ [source])) →
      HsemanticNext.metadata =
        Hsemantic.metadata ++ [(nindices, resultLevel)] →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices source.name)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M alpha from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const source.name stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceEq⟩
  apply laterResult.WF k Q Hc hnonempty hsourceFull
  intro resultSort hguard hsorted
  have hsourceFull' : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type sourceFull :=
    hsourceFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hsortedNarrow := Hruntime.resultSort Hc.checking.tr.wf
    htypeNarrow hsourceFull' hsorted
  rcases TrExpr.sort_source hsortedNarrow with
    ⟨resultLevel, hofLevel, _hresult⟩
  rcases Hruntime.independentSourceScope with
    ⟨sourceScope, HsourceScope, hsourceScopeFVars⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams
    (uvars := c.lparams.length) (commonParams := commonParams)
    Hc.checking.tr.wf Hruntime HsourceScope hsourceScopeFVars
      rfl hparams hofLevel hsortedNarrow
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  let HsemanticNext := Hsemantic.snoc source target nindices resultLevel
    Htranslation hheader hlevel
  exact Hrec resultSort resultLevel hguard hofLevel HsemanticNext
    (checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.metadata_snoc Hsemantic
      source target nindices resultLevel Htranslation hheader hlevel)

/-- Fold one noninitial mutual header while preserving the exact ordered
semantic prefix. -/
theorem laterStep.extendsSemanticAccumulator
    {commonParams : List VExpr} {commonLevel : VLevel}
    {alpha : Type} (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c)
    (hidx : dIdx < indTypes.size)
    (_hnoninitial : 0 < dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel
          (indTypes.toList.take dIdx))
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      c'.lparams = c.lparams →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      Hc'.venv = Hc.venv →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        nparams (depth + nindices) →
      checkInductiveTypes.loopType.ParameterContextSuffix Hc'
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        (depth + nindices) →
      (Hsemantic' :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            (indTypes.toList.take (dIdx + 1))) →
      Hsemantic'.metadata =
        Hsemantic.metadata ++ [(nindices, resultLevel)] →
      checkInductiveTypes.loopType.AmbientParamContext Hc'
        commonParams (depth + nindices) →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes
      dIdx stats k c).WF Q := by
  apply stepPrefix.accumulatesRawHeaders
    (nparams := nparams) (stats := stats) (k := k) (Q := Q)
    Hc Hsemantic.headers.raw hidx
  intro checkedType Hchecked _Hraw normalized hbelow hnormalized
  have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized := by
    have hsourceNoFVars : FVarsIn (fun _ => False)
        indTypes[dIdx].type :=
      Hchecked.source.type.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False)
        Hc.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    exact hbelow _ hfalseUpSet hsourceNoFVars
  by_cases hforall : ∃ name dom body bi,
      normalized = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have Htarget := CheckedSourceHeaderTranslation.checkedLaterForall
      Hchecked hnormalized hnormalizedNoFVars
    let sourceSkeleton :=
      checkInductiveTypes.loopType.headerSkeleton Hchecked.target
    have HtargetSkeleton : TrSourceConst Hc.venv c.lparams
        indTypes[dIdx].name indTypes[dIdx].type
          sourceSkeleton.toVConstVal := by
      change TrSourceConst Hc.venv c.lparams indTypes[dIdx].name
        indTypes[dIdx].type Hchecked.target
      exact Htarget
    rcases initialLaterHeaderSynthesisState Hc HtargetSkeleton
        Hchecked.typing hnormalized hnormalizedNoFVars with
      ⟨narrowCurrent, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
    let Hscope : ∀ h : 0 < stats.params.size,
        checkInductiveTypes.loopType.LaterParameterScope Hsuffix 0
          (.forallE name dom body bi) := fun h =>
      initialLaterParameterScope Hc Hsuffix h HtargetSkeleton.raw hbelow
    apply checkInductiveTypes.loopType.laterParameterSynthesisWF Hc
      (target := sourceSkeleton)
      (k := fun type stats nindices => show AddInductive.M alpha from do
        let type ← TypeChecker.ensureSort type
        let mut stats := stats
        let resultLevel := type.sortLevel!
        if stats.indConsts.isEmpty then
          let lctx := (← read).lctx
          stats := { stats with
            lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
        else if !resultLevel.isEquiv stats.resultLevel then
          throw <| .other
            "mutually inductive types must live in the same universe"
        stats := { stats with
          nindices := stats.nindices.push nindices
          indConsts := stats.indConsts.push
            (.const indTypes[dIdx].name stats.levels) }
        AddInductive.checkInductiveTypes.loopInd nparams indTypes
          (dIdx + 1) stats k)
      (Q := Q) hnonempty Hsuffix
      (Hresult := by
        intro type' narrow' full' scope' i' fuel' hi' Hsynthesis'
          hscope' htypeNarrow' htypeFVars' htypeFull'
        cases hi'
        subst scope'
        let Hruntime :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        have hindices' : Hsynthesis'.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis'.indexCount
        have hparamScope : Hsuffix.parameterDecls.toCtx =
            Hsynthesis'.params.reverse := by
          simpa [hindices'] using Hsynthesis'.scopeCtx
        have hparamsBoundary := Hsuffix.paramsDefEq Hambient <|
          hcommonParams.trans hparams.symm
        rw [hparamScope] at hparamsBoundary
        apply checkInductiveTypes.loopType.laterIndexSynthesisWF
          (depth := depth) (commonParams := commonParams)
          (paramU := c.lparams.length)
          (R := fun env =>
            ∃ Hprior :
              checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
                env c.lparams nparams commonParams commonLevel
                  (indTypes.toList.take dIdx),
              Hprior.metadata = Hsemantic.metadata ∧
              TrSourceConst env c.lparams indTypes[dIdx].name
                indTypes[dIdx].type Hchecked.target ∧
              env = Hc.venv)
          (k := fun type stats nindices => show AddInductive.M alpha from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k)
          (Q := Q)
          (Hresult := by
            intro c' Hc' henv' hsafety' hlparams' hallowPrimitive' hfuel'
              type'' narrow'' full'' scope'' nindices'' fuel'' hforall''
              Hsynthesis'' Hruntime''
              htypeNarrow'' _htypeFVars'' htypeFull'' Hcache'' Hsuffix''
              Hambient'' HR'' hparams''
            rcases HR'' with
              ⟨Hsemantic'', hmetadataPrior, Htranslation'', hvenv'⟩
            apply checkInductiveTypes.loopType.result.WF
              (fuel := fuel'') (Q := Q) hforall'' rfl
            let HsemanticPrior := Hsemantic''.reindexUs hlparams'.symm
            apply laterResult.snocsSemanticNarrow
              (source := indTypes[dIdx]) (target := Hchecked.target)
              (priorSources := indTypes.toList.take dIdx)
              k Q Hc' hnonempty
              (by simpa [hlparams'] using Htranslation'')
              HsemanticPrior
              Hsynthesis'' Hruntime'' htypeNarrow'' htypeFull''
              (by simpa [hlparams'] using hparams'')
              (by simpa [hlparams'] using hcommon)
            intro resultSort resultLevel hguard hofLevel HsemanticNext
              hmetadataNext
            have hidxList : dIdx < indTypes.toList.length := by
              simpa using hidx
            let HsemanticNext' :
                checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
                  Hc'.venv c'.lparams nparams commonParams commonLevel
                    (indTypes.toList.take (dIdx + 1)) := by
              apply HsemanticNext.reindexSources
              exact (List.take_succ_eq_append_getElem hidxList).symm
            apply Hrec (resultLevel := resultLevel)
              (Hsemantic' := HsemanticNext') Hc' henv' hsafety' hlparams'
              hallowPrimitive' hfuel' hvenv'
            · exact Hcache''.reindex (by simp [updatedStats])
            · exact Hsuffix''.reindex (by simp [updatedStats])
            · calc
                HsemanticNext'.metadata = HsemanticNext.metadata := rfl
                _ = HsemanticPrior.metadata ++
                    [(nindices'', resultLevel)] := hmetadataNext
                _ = Hsemantic''.metadata ++
                    [(nindices'', resultLevel)] := by
                  rw [checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.metadata_reindexUs]
                _ = Hsemantic.metadata ++
                    [(nindices'', resultLevel)] := by rw [hmetadataPrior]
            · exact Hambient'')
          hconsume Hc rfl rfl rfl rfl (by simpa using Hcache)
          (by simpa using Hsuffix) (by simpa using Hambient)
          ⟨Hsemantic, rfl, Htarget, rfl⟩ Hsynthesis' hparamsBoundary Hruntime
          htypeNarrow' htypeFVars' htypeFull')
      hparams (by omega) Hscope
      (fun h => (Hscope h).older_eq_nil h |>.symm)
      (by
        intro hzero
        have hsize : stats.params.size = 0 := hparams.trans hzero.symm
        apply (List.eq_nil_of_length_eq_zero ?_).symm
        rw [Hsuffix.parameterDecls_length, hsize])
      Hsynthesis hnormalizedNarrow
      (by simpa [VLCtx.fvars] using hnormalizedNoFVars) hnormalized
  · cases hfuel : c.fuel.inductiveFuel with
    | zero => exact checkInductiveTypes.loopType.zero.WF
    | succ fuel =>
      by_cases hzero : 0 = nparams
      · apply checkInductiveTypes.loopType.result.WF
          (Q := Q) hforall hzero
        have hnormalizedFull := hnormalized
        rcases hnormalized with ⟨current, htype, hcurrentEq⟩
        apply laterResult.WF
          (nparams := nparams) (indTypes := indTypes) (dIdx := dIdx)
          (indName := indTypes[dIdx].name) (nindices := 0)
          k Q Hc hnonempty htype
        intro resultSort hguard hsorted
        have hsortedRuntime := TrExpr.defeq Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf.toCtx hsorted hcurrentEq
        rcases CheckedSourceHeaderTranslation.checkedTerminal
            Hchecked hsortedRuntime with
          ⟨resultLevel, hofLevel, Htarget⟩
        let sourceSkeleton :=
          checkInductiveTypes.loopType.headerSkeleton Hchecked.target
        have HtargetSkeleton : TrSourceConst Hc.venv c.lparams
            indTypes[dIdx].name indTypes[dIdx].type
              sourceSkeleton.toVConstVal := by
          change TrSourceConst Hc.venv c.lparams indTypes[dIdx].name
            indTypes[dIdx].type Hchecked.target
          exact Htarget
        rcases initialLaterHeaderSynthesisState Hc HtargetSkeleton
            Hchecked.typing hnormalizedFull hnormalizedNoFVars with
          ⟨narrowCurrent, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
        have hscopeEmpty : Hsuffix.parameterDecls = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [Hsuffix.parameterDecls_length, hparams, ← hzero]
        let HruntimeBase :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        have Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
            Hc.venv c.lparams [] Hc.mlctx.vlctx := by
          simpa [hscopeEmpty] using HruntimeBase
        have hfull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
            normalized current := htype.trExpr Hc.checking.tr.wf
              Hc.mlctx_wf.tr.wf
        have hsortedNarrow := Hruntime.resultSort Hc.checking.tr.wf
          hnormalizedNarrow hfull hsorted
        rcases Hruntime.independentSourceScope with
          ⟨sourceScope, HsourceScope, hsourceScopeFVars⟩
        have hcommonEmpty : commonParams = [] :=
          List.eq_nil_of_length_eq_zero (hcommonParams.trans hzero.symm)
        have hparamEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
            commonParams.reverse Hsynthesis.params.reverse := by
          rw [hcommonEmpty,
            List.eq_nil_of_length_eq_zero Hsynthesis.parameterCount]
          exact .refl (by trivial)
        have Hheader := Hsynthesis.synthesizedHeaderWithParams
          (uvars := c.lparams.length) (commonParams := commonParams)
          Hc.checking.tr.wf Hruntime HsourceScope hsourceScopeFVars
          rfl hparamEq hofLevel hsortedNarrow
        have Hheader' : checkInductiveTypes.loopType.SynthesizedHeader
            Hc.venv c.lparams c.lparams.length nparams commonParams
              sourceSkeleton 0 resultLevel := by
          simpa [hzero] using Hheader
        have hlevel : resultLevel ≈ commonLevel :=
          Level.isEquiv_wf hguard hofLevel hcommon
        let HsemanticNext := Hsemantic.snoc indTypes[dIdx]
          Hchecked.target 0 resultLevel Htarget Hheader' hlevel
        have hidxList : dIdx < indTypes.toList.length := by
          simpa using hidx
        let HsemanticNext' :
            checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
              Hc.venv c.lparams nparams commonParams commonLevel
                (indTypes.toList.take (dIdx + 1)) := by
          apply HsemanticNext.reindexSources
          exact (List.take_succ_eq_append_getElem hidxList).symm
        apply Hrec (resultLevel := resultLevel)
          (Hsemantic' := HsemanticNext') Hc rfl rfl rfl rfl rfl rfl
        · exact Hcache.reindexUpdatedStats stats.lctx resultSort false 0
            indTypes[dIdx].name
        · exact Hsuffix.reindexUpdatedStats stats.lctx resultSort false 0
            indTypes[dIdx].name
        · calc
            HsemanticNext'.metadata = HsemanticNext.metadata := rfl
            _ = Hsemantic.metadata ++ [(0, resultLevel)] := by
              simpa [HsemanticNext] using
                (checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator.metadata_snoc
                  Hsemantic indTypes[dIdx] Hchecked.target 0 resultLevel
                    Htarget Hheader' hlevel)
        · simpa using Hambient
      · exact checkInductiveTypes.loopType.parameterMismatch.WF
          (Q := Q) hforall hzero

/-- Complete the remaining mutual-header loop from a nonempty semantic
prefix. -/
theorem laterLoopIndSemantic
    {root c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams dIdx depth : Nat}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {rootVEnv : VEnv}
    {alpha : Type} (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat},
      (Hc' : ContextWF c') →
      c'.env = root.env →
      c'.safety = root.safety →
      c'.lparams = root.lparams →
      c'.allowPrimitive = root.allowPrimitive →
      c'.fuel = root.fuel →
      Hc'.venv = rootVEnv →
      (Hsemantic' :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            indTypes.toList) →
      stats'.levels.length = c'.lparams.length →
      stats'.levels = c'.lparams.map .param →
      stats'.nindices.size = indTypes.size →
      stats'.nindices.toList = Hsemantic'.metadata.map Prod.fst →
      stats'.indConsts.size = indTypes.size →
      stats'.indConsts =
        (indTypes.toList.map fun source =>
          .const source.name stats'.levels).toArray →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      commonParams.length = nparams →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
          nparams depth' →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth' →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' commonParams depth' →
      VLevel.ofLevel c'.lparams stats'.resultLevel = some commonLevel →
      (k stats' c').WF Q)
    (Hc : ContextWF c)
    (henvRoot : c.env = root.env)
    (hsafetyRoot : c.safety = root.safety)
    (hlparamsRoot : c.lparams = root.lparams)
    (hallowPrimitiveRoot : c.allowPrimitive = root.allowPrimitive)
    (hfuelRoot : c.fuel = root.fuel)
    (hvenvRoot : Hc.venv = rootVEnv)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel
          (indTypes.toList.take dIdx))
    (hdone : dIdx ≤ indTypes.size)
    (hnoninitial : 0 < dIdx)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.size = dIdx)
    (hindicesExact : stats.nindices.toList =
      Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts.size = dIdx)
    (hconstsExact : stats.indConsts =
      ((indTypes.toList.take dIdx).map fun source =>
        .const source.name stats.levels).toArray)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx
      stats k c).WF Q := by
  by_cases hidx : dIdx < indTypes.size
  · apply laterStep.extendsSemanticAccumulator k Q Hc hidx hnoninitial
      hnonempty hparams hcommonParams Hcache Hsuffix Hsemantic Hambient
      hcommon hconsume
    intro c' nindices resultSort resultLevel Hc' henv' hsafety'
      hlparams' hallowPrimitive' hfuel' hvenv' Hcache' Hsuffix' Hsemantic'
      hmetadata' Hambient'
    apply laterLoopIndSemantic k Q hconsume Hfinish Hc'
      (henv'.trans henvRoot) (hsafety'.trans hsafetyRoot)
      (hlparams'.trans hlparamsRoot)
      (hallowPrimitive'.trans hallowPrimitiveRoot)
      (hfuel'.trans hfuelRoot) (hvenv'.trans hvenvRoot) Hsemantic'
      (dIdx := dIdx + 1) (depth := depth + nindices)
      (stats := updatedStats stats stats.lctx resultSort false nindices
        indTypes[dIdx].name)
    · omega
    · omega
    · simpa [updatedStats, hlparams'] using hlevels
    · simpa [updatedStats, hlparams'] using hlevelParams
    · simp [updatedStats, hindices]
    · simp [updatedStats, hindicesExact, hmetadata']
    · simp [updatedStats, hconsts]
    · have hidxList : dIdx < indTypes.toList.length := by
        simpa using hidx
      rw [List.take_succ_eq_append_getElem hidxList]
      simp [updatedStats, hconstsExact]
    · simp [updatedStats]
    · simpa [updatedStats] using hparams
    · exact hcommonParams
    · exact Hcache'
    · exact Hsuffix'
    · exact Hambient'
    · simpa [updatedStats, hlparams'] using hcommon
  · have hcoverage : indTypes.size ≤ dIdx := Nat.le_of_not_gt hidx
    have htake : indTypes.toList.take dIdx = indTypes.toList :=
      List.take_of_length_le (by simpa using hcoverage)
    let HsemanticFull :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc.venv c.lparams nparams commonParams commonLevel
            indTypes.toList := Hsemantic.reindexSources htake
    apply result.WF (k := k) (Q := Q) hidx
    · exact hlevels
    · have : dIdx = indTypes.size := by omega
      simpa [this] using hindices
    · have : dIdx = indTypes.size := by omega
      simpa [this] using hconsts
    · exact hparams
    · exact Hfinish Hc henvRoot hsafetyRoot hlparamsRoot
        hallowPrimitiveRoot hfuelRoot hvenvRoot
        HsemanticFull
        hlevels hlevelParams
        (by
          have : dIdx = indTypes.size := by omega
          simpa [this] using hindices)
        (by simpa [HsemanticFull, htake] using hindicesExact)
        (by
          have : dIdx = indTypes.size := by omega
          simpa [this] using hconsts)
        (by simpa [htake] using hconstsExact)
        hnonempty hparams hcommonParams Hcache Hsuffix Hambient hcommon
termination_by indTypes.size - dIdx

/-- Initialize and complete semantic header accumulation from the first
family. -/
theorem firstLoopIndSemantic
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams : Nat}
    {alpha : Type} (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hc : ContextWF c)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth' : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      c'.lparams = c.lparams →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      Hc'.venv = Hc.venv →
      (Hsemantic' :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            indTypes.toList) →
      stats'.levels.length = c'.lparams.length →
      stats'.levels = c'.lparams.map .param →
      stats'.nindices.size = indTypes.size →
      stats'.nindices.toList = Hsemantic'.metadata.map Prod.fst →
      stats'.indConsts.size = indTypes.size →
      stats'.indConsts =
        (indTypes.toList.map fun source =>
          .const source.name stats'.levels).toArray →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      commonParams.length = nparams →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
          nparams depth' →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth' →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' commonParams depth' →
      VLevel.ofLevel c'.lparams stats'.resultLevel = some commonLevel →
      (k stats' c').WF Q)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hnindices : stats.nindices = #[])
    (hconsts : stats.indConsts = #[])
    (hparams : stats.params = #[]) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
      stats k c).WF Q := by
  apply firstStep.initializesSemanticAccumulator k Q Hc hctx hnonempty
    hempty hparams hconsume
  intro c' stats' nindices resultSort resultLevel params Hc' henv'
    hsafety' hlparams' hallowPrimitive' hfuel' hvenv' hlevels' hnindices'
    hconsts' Hsemantic hmetadata hofLevel Hcache Hsuffix Hambient
  have hparamSize : stats'.params.size = nparams := by
    have hlength :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hcache.params
    simpa using hlength
  have hcommonParams : params.length = nparams := by
    have hpayload : 0 < Hsemantic.payloads.length := by
      have hlength := congrArg List.length Hsemantic.sourceOrder
      have : Hsemantic.payloads.length = 1 := by simpa using hlength
      omega
    exact Hsemantic.payloads[0].2.synthesized.parameterCount
  have hidxList : 0 < indTypes.toList.length := by simpa using hnonempty
  let HsemanticTake :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc'.venv c'.lparams nparams params resultLevel
          (indTypes.toList.take 1) := by
    apply Hsemantic.reindexSources
    simpa using (List.take_succ_eq_append_getElem hidxList).symm
  apply laterLoopIndSemantic k Q hconsume Hfinish Hc' henv' hsafety'
    hlparams' hallowPrimitive' hfuel' hvenv' HsemanticTake
    (rootVEnv := Hc.venv)
    (dIdx := 1) (depth := nindices)
    (stats := updatedStats stats' c'.lctx resultSort true nindices
      indTypes[0].name)
  · omega
  · omega
  · simp [updatedStats, hlevels', hlevels, hlparams']
  · simp [updatedStats, hlevels', hlevelParams, hlparams']
  · simp [updatedStats, hnindices', hnindices]
  · simp [updatedStats, hnindices', hnindices, HsemanticTake, hmetadata]
  · simp [updatedStats, hconsts', hconsts]
  · rw [List.take_succ_eq_append_getElem hidxList]
    simp [updatedStats, hconsts', hconsts]
  · simp [updatedStats]
  · simpa [updatedStats] using hparamSize
  · exact hcommonParams
  · exact Hcache.reindexUpdatedStats c'.lctx resultSort true nindices
      indTypes[0].name
  · exact Hsuffix.reindexUpdatedStats c'.lctx resultSort true nindices
      indTypes[0].name
  · exact Hambient
  · simpa [updatedStats] using hofLevel

/-- Public skeleton-free verifier retaining exact source translations, the
full synthesized semantic certificate for every mutual family, and exact
alignment with the source verification environment. -/
theorem checkInductiveTypes.accumulatesSemanticHeadersSourceAligned
    {c : AddInductive.Context} {indTypes : Array InductiveType}
    {nparams : Nat} {alpha : Type}
    (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      c'.lparams = c.lparams →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      Hc'.venv = Hc.venv →
      (Hsemantic' :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            indTypes.toList) →
      stats'.levels.length = c'.lparams.length →
      stats'.levels = c'.lparams.map .param →
      stats'.nindices.size = indTypes.size →
      stats'.nindices.toList = Hsemantic'.metadata.map Prod.fst →
      stats'.indConsts.size = indTypes.size →
      stats'.indConsts =
        (indTypes.toList.map fun source =>
          .const source.name stats'.levels).toArray →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      commonParams.length = nparams →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
          nparams depth →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' commonParams depth →
      VLevel.ofLevel c'.lparams stats'.resultLevel = some commonLevel →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd nparams indTypes 0
    { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply firstLoopIndSemantic k Q hconsume Hc Hfinish hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl
  · rfl

/-- Compatibility adapter for consumers that do not need exact alignment
with the source verification environment. -/
theorem checkInductiveTypes.accumulatesSemanticHeaders
    {c : AddInductive.Context} {indTypes : Array InductiveType}
    {nparams : Nat} {alpha : Type}
    (k : AddInductive.InductiveStats → AddInductive.M alpha)
    (Q : alpha → Prop)
    (Hc : ContextWF c)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      c'.lparams = c.lparams →
      (Hsemantic' :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            indTypes.toList) →
      stats'.levels.length = c'.lparams.length →
      stats'.levels = c'.lparams.map .param →
      stats'.nindices.size = indTypes.size →
      stats'.nindices.toList = Hsemantic'.metadata.map Prod.fst →
      stats'.indConsts.size = indTypes.size →
      stats'.indConsts =
        (indTypes.toList.map fun source =>
          .const source.name stats'.levels).toArray →
      stats'.indConsts.isEmpty = false →
      stats'.params.size = nparams →
      commonParams.length = nparams →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
          nparams depth →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' depth →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' commonParams depth →
      VLevel.ofLevel c'.lparams stats'.resultLevel = some commonLevel →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  apply checkInductiveTypes.accumulatesSemanticHeadersSourceAligned
    k Q Hc hctx hnonempty hconsume
  intro c' stats' depth commonParams commonLevel Hc' henv hsafety
    hlparams _hallowPrimitive _hfuel _hvenv Hsemantic hlevels hlevelParams
    hindicesSize hindices hconstsSize hconsts hnonempty' hparams
    hcommonParams Hcache Hsuffix Hambient hcommon
  exact Hfinish Hc' henv hsafety hlparams Hsemantic hlevels hlevelParams
    hindicesSize hindices hconstsSize hconsts hnonempty' hparams
    hcommonParams Hcache Hsuffix Hambient hcommon

end checkInductiveTypes.loopInd
end VerifyInductive
end Lean4Lean
