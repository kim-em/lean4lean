import Lean4Lean.Verify.Inductive.Recursor.FirstPass

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace mkRecInfos.loopInd1

/-- The first mutual pass retains selectable motive, index, and major binders
for every appended `RecInfo`. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hprogress : recInfos.size = dIdx)
    (Harities : RecInfoArities stats recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hblueprints : RecInfoBlueprintCounts recInfos)
    (Hk : ∀ out c,
      out.size = recInfos.size + (indTypes.size - dIdx) →
      BindingContextWF c → (Hbindings : RecInfoBindings c out) →
      (Horigins : RecInfoTypeOrigins c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoArities stats out →
      RecInfoMinorsEmpty out →
      RecInfoBlueprintCounts out →
      BindingContextLE root c → (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context)
      hread fun ctx hctx => ?_
    subst ctx
    have hwhnf :
        ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
          AddInductive.M Expr) c).WF (fun _ => True) := by
      intro _ _
      trivial
    refine hwhnf.bind fun type _ => ?_
    apply mkRecInfos.loopArgs1.continueWithBindings
      (root := c) stats
    · intro indices originTypes cIndices HcIndices Hindices HindexOrigins hIndices
      by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
      · rw [if_pos harity]
        let majorTy :=
          (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
            indices).consumeTypeAnnotationsVerified
        apply withLocalDecl.continueRaw
        let cMajor : AddInductive.Context := { cIndices with
          ngen := cIndices.ngen.next
          lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
            majorTy .default }
        have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
            (fun lctx => lctx = cMajor.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        let major := Expr.fvar ⟨cIndices.ngen.curr⟩
        let motiveTy := cMajor.lctx.mkForall indices <|
          cMajor.lctx.mkForall #[major] <| .sort elimLevel
        let motiveName := if indTypes.size > 1 then
          (`motive).appendIndexAfter (dIdx + 1) else `motive
        apply withLocalDecl.continueRaw
        let cMotive : AddInductive.Context := { cMajor with
          ngen := cMajor.ngen.next
          lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
            motiveTy.consumeTypeAnnotationsVerified .default }
        refine mkRecInfos.loopInd1.resultBindings (root := root) (Q := Q)
          stats indTypes elimLevel
          (dIdx + 1) (recInfos.push {
            motive := .fvar ⟨cMajor.ngen.curr⟩
            minors := #[]
            indices
            major }) k cMotive ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · exact (HcIndices.withLocalDecl `t majorTy .default).withLocalDecl
            motiveName motiveTy.consumeTypeAnnotationsVerified .default
        · exact Hbindings.pushFrame hIndices HcIndices
            Hindices.toBoundFVarArray
            `t majorTy .default
            motiveName motiveTy.consumeTypeAnnotationsVerified .default
        · exact Horigins.pushFrame hIndices HcIndices HindexOrigins
            `t majorTy .default motiveName
              motiveTy.consumeTypeAnnotationsVerified .default
        · exact Hparams.mono <| hIndices.trans <|
            (BindingContextLE.withLocalDecl cIndices HcIndices
              `t majorTy .default).trans <|
              BindingContextLE.withLocalDecl cMajor
                (HcIndices.withLocalDecl `t majorTy .default) motiveName
                motiveTy.consumeTypeAnnotationsVerified .default
        · exact Hbindings.pushFrame_noAlias Hparams HnoAlias hIndices
            HcIndices Hindices `t majorTy .default motiveName
              motiveTy.consumeTypeAnnotationsVerified .default
        · exact Hroot.trans <| hIndices.trans <|
            (BindingContextLE.withLocalDecl cIndices HcIndices
              `t majorTy .default).trans <|
              BindingContextLE.withLocalDecl cMajor
                (HcIndices.withLocalDecl `t majorTy .default) motiveName
                motiveTy.consumeTypeAnnotationsVerified .default
        · simp [hprogress]
        · apply Harities.push
          have hnew : indices.size = stats.nindices[dIdx]! := by
            simpa using harity
          simpa [hprogress] using hnew
        · exact Hempty.push
        · exact Hblueprints.pushEmpty
        · intro out cOut houtSize HcOut HbindingsOut HoriginsOut HparamsOut
            HnoAliasOut HaritiesOut HemptyOut HblueprintsOut HrootOut
          have houtSize' : out.size = recInfos.size +
              (indTypes.size - dIdx) := by
            simp only [Array.size_push] at houtSize
            omega
          exact Hk out cOut houtSize' HcOut HbindingsOut HoriginsOut HparamsOut
            HnoAliasOut HaritiesOut HemptyOut HblueprintsOut HrootOut
      · rw [if_neg harity]
        exact Except.WF.throw
    · exact Hc
    · exact FreshBoundFVarArray.empty c
    · exact BoundFVarTypeOrigins.empty c
    · exact BindingContextLE.refl c
  · rw [dif_neg hidx]
    exact Hk recInfos c (by omega) Hc Hbindings Horigins Hparams HnoAlias
      Harities Hempty Hblueprints Hroot
termination_by indTypes.size - dIdx

/-- Semantic strengthening of the first mutual recursor pass.  In addition
to the operational binder certificates retained by `resultBindings`, every
family is replayed against its independently checked header under the common
recursor universe list, and the exact index/major/motive origin-type rows
remain translated and typed after all later mutual frames. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} (Hbase : ContextWF base)
    {decl : VInductDecl} {baseDepth runtimeDepth : Nat}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Hheaders : ∀ i (hi : i < indTypes.size),
      mkRecInfos.loopArgs1.CheckedRecursorHeaderAt Hbase stats decl
        baseDepth indTypes[i] i)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (HparamsCtx : ∀ i (hi : i < indTypes.size),
      VEnv.IsDefEqCtx R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length []
        ((Hheaders i hi).recursorParams Helim).reverse
        Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      R.mlctx.vlctx stats decl runtimeDepth)
    (Hbindings : RecInfoBindings current recInfos)
    (Horigins : RecInfoTypeOrigins current recInfos)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes current recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl
      Hsuffix.parameterDecls.toCtx recInfos elimLevel)
    (HindexTypeRows :
      RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray current stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE base current)
    (hprogress : recInfos.size = dIdx)
    (Harities : RecInfoArities stats recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hblueprints : RecInfoBlueprintCounts recInfos)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (henvOut : Rout.venv = Hbase.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rout.mlctx.vlctx stats decl outDepth)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoTypeOrigins outCtx out),
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl
        HsuffixOut.parameterDecls.toCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      RecInfoMinorsEmpty out →
      RecInfoBlueprintCounts out →
      BindingContextLE base outCtx →
      out.size = recInfos.size + (indTypes.size - dIdx) →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) current).WF
        (fun c' => c' = current) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context)
      hread fun ctx hctx => ?_
    subst ctx
    let Hheader := Hheaders dIdx hidx
    let loopK : Array Expr → AddInductive.M alpha := fun indices => do
      unless indices.size == stats.nindices[dIdx]! do
        throw <| .other
          "recursor index arity does not match checked inductive header"
      let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
      withLocalDecl `t .default tTy.consumeTypeAnnotationsVerified fun major => do
      let lctx ← getLCtx
      let motiveTy := lctx.mkForall indices <|
        lctx.mkForall #[major] <| .sort elimLevel
      let name := if indTypes.size > 1 then
        (`motive).appendIndexAfter (dIdx + 1) else `motive
      withLocalDecl name .default motiveTy.consumeTypeAnnotationsVerified fun motive =>
      AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel (dIdx + 1)
        (recInfos.push { motive, minors := #[], indices, major }) k
    change ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
        AddInductive.M Expr) current >>= fun normalized =>
      AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[]
        current.fuel.inductiveFuel loopK current).WF Q
    refine Hheader.startRecursorSemantics Helim R hconsume henv
      Hsuffix (HparamsCtx dIdx hidx) Hstats
      loopK ?_ current.fuel.inductiveFuel
    · intro cIndices nextDepth Rindices henvIndices HsuffixIndices
        hparameterDecls type
        fullTarget narrowTarget scope nindices indices indexOrigins
        indexTargets Hsynthesis hcanonicalParams hscopeBase HnarrowStats HstatsIndices Hruntime
        hfront htypeNarrow htypeFVars htypeFull htypeFullType Hindices
        HnarrowIndices hindexCount hcanonical HindexOrigins HindexTypes
        Hrecent
      by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
      · simp only [loopK]
        rw [if_pos harity]
        rcases Hheader.completedRecursorFrame Helim R Rindices Hsynthesis
            HnarrowStats Hruntime HnarrowIndices hindexCount hcanonical
            harity henvIndices hconsume Hrecent with ⟨Hframe⟩
        have hindicesSize : indices.size = nindices := by
          have hlength :=
            Lean4Lean.VerifyInductive.List.Forall₂.length_eq' HnarrowIndices
          simpa [hindexCount] using hlength
        rcases Hheader.completedRecursorMotiveTypeDefEq Helim Rindices
            Hsynthesis HnarrowStats Hruntime HnarrowIndices hcanonical
            HindexOrigins.bound henvIndices hindicesSize hfront Hframe with
          ⟨Hcanonical, HmotiveCanonical, HmotiveCanonicalClosed,
            hcanonicalMotiveReopen, hcanonicalMotiveBody⟩
        let majorTy :=
          (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
            indices).consumeTypeAnnotationsVerified
        refine withLocalDecl.recursorWF (name := `t) (bi := .default)
          Rindices Hframe.majorTr Hframe.majorType ?_
        let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
          Hframe.majorTr Hframe.majorType
        let HsuffixMajor := HsuffixIndices.withAmbient
          (name := `t) (bi := .default) Hframe.majorTr Hframe.majorType
        let HstatsMajor := HstatsIndices.withFVar Rmajor.checking.tr.wf
          Rmajor.mlctx_wf.tr.wf
        let cMajor : AddInductive.Context := { cIndices with
          ngen := cIndices.ngen.next
          lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
            majorTy .default }
        have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
            (fun lctx => lctx = cMajor.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        let major := Expr.fvar ⟨cIndices.ngen.curr⟩
        let motiveTy := cMajor.lctx.mkForall indices <|
          cMajor.lctx.mkForall #[major] <| .sort elimLevel
        let motiveName := if indTypes.size > 1 then
          (`motive).appendIndexAfter (dIdx + 1) else `motive
        refine withLocalDecl.recursorWF (name := motiveName) (bi := .default)
          Rmajor Hframe.motiveTr Hframe.motiveType ?_
        let Rmotive := Rmajor.withLocalDecl (name := motiveName)
          (bi := .default) Hframe.motiveTr Hframe.motiveType
        let HsuffixMotive := HsuffixMajor.withAmbient
          (name := motiveName) (bi := .default)
          Hframe.motiveTr Hframe.motiveType
        let HstatsMotive := HstatsMajor.withFVar Rmotive.checking.tr.wf
          Rmotive.mlctx_wf.tr.wf
        have HmajorAtIndices := HmajorTypes.weakenRecent Hrecent
        have HmotiveAtIndices := HmotiveTypes.weakenRecent Hrecent
        have HindexRowsAtIndices := HindexTypeRows.weakenRecent Hrecent
        let HmajorAtMotive :=
          (HmajorAtIndices.push (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HmotiveAtMotive :=
          (HmotiveAtIndices.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).push
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexRowsAtMotive :=
          (HindexRowsAtIndices.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexTypesAtMotive :=
          (HindexTypes.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexRows' := HindexRowsAtMotive.push HindexTypesAtMotive
        let cMotive : AddInductive.Context := { cMajor with
          ngen := cMajor.ngen.next
          lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
            motiveTy.consumeTypeAnnotationsVerified .default }
        let hIndices := Hrecent.contextLE
        let Hbindings' := Hbindings.pushFrame hIndices
          Rindices.toBindingContextWF
          Hrecent.toFreshBoundFVarArray.toBoundFVarArray
          `t majorTy .default motiveName
          motiveTy.consumeTypeAnnotationsVerified .default
        let Horigins' := Horigins.pushFrame hIndices
          Rindices.toBindingContextWF HindexOrigins
          `t majorTy .default motiveName
          motiveTy.consumeTypeAnnotationsVerified .default
        let Hparams' := Hparams.mono <| hIndices.trans <|
          (BindingContextLE.withLocalDecl cIndices
            Rindices.toBindingContextWF `t majorTy .default).trans <|
            BindingContextLE.withLocalDecl cMajor
              (Rindices.toBindingContextWF.withLocalDecl
                `t majorTy .default)
              motiveName motiveTy.consumeTypeAnnotationsVerified .default
        have HnoAlias' : Hbindings'.NoAlias Hparams' := by
          exact Hbindings.pushFrame_noAlias Hparams HnoAlias hIndices
            Rindices.toBindingContextWF
            Hrecent.toFreshBoundFVarArray
            `t majorTy .default motiveName
            motiveTy.consumeTypeAnnotationsVerified .default
        have holdMinors : Hbindings.flatMinors.fvars = [] :=
          Hempty.flatMinors_fvars Hbindings
        have hnewMinors : Hbindings'.flatMinors.fvars = [] :=
          Hempty.push.flatMinors_fvars Hbindings'
        have hparamsFVars : Hparams'.fvars = Hparams.fvars := rfl
        have hmotiveFVars : Hbindings'.motives.fvars =
            Hbindings.motives.fvars ++
              [(⟨cMajor.ngen.curr⟩ : FVarId)] := by
          rw [← Hbindings'.motives.exprArrayFVarIds,
            ← Hbindings.motives.exprArrayFVarIds]
          simp [Hbindings', ExprArrayFVarIds, cMajor, recursorFVarId]
        have hcontextFVars : Rmotive.mlctx.vlctx.fvars =
            (⟨cMajor.ngen.curr⟩ : FVarId) ::
              ((⟨cIndices.ngen.curr⟩ : FVarId) ::
                Hrecent.fvars.reverse) ++ R.mlctx.vlctx.fvars := by
          dsimp only [Rmotive, Rmajor, RecursorContextWF.withLocalDecl,
            TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]
          rw [Hrecent.contextFVars]
          rfl
        have Horder' : RecInfoOuterOrder Rmotive Hparams' Hbindings' :=
          RecInfoOuterOrder.pushMotive Horder holdMinors hparamsFVars
            hmotiveFVars hnewMinors hcontextFVars
        have hparameterDeclsMotive :
            HsuffixMotive.parameterDecls = Hsuffix.parameterDecls := by
          calc
            HsuffixMotive.parameterDecls =
                HsuffixIndices.parameterDecls := by rfl
            _ = Hsuffix.parameterDecls := hparameterDecls
        have HparamsCtx' : ∀ i (hi : i < indTypes.size),
            VEnv.IsDefEqCtx Rmotive.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length []
              ((Hheaders i hi).recursorParams Helim).reverse
              HsuffixMotive.parameterDecls.toCtx := by
          intro i hi
          have hvenvMotive : Rmotive.venv = R.venv := by
            change Rindices.venv = R.venv
            exact henvIndices.trans henv.symm
          rw [hvenvMotive, hparameterDeclsMotive]
          exact HparamsCtx i hi
        let hMajorFrame := BindingContextLE.withLocalDecl cIndices
          Rindices.toBindingContextWF `t majorTy .default
        let hMotiveFrame := BindingContextLE.withLocalDecl cMajor
          (Rindices.toBindingContextWF.withLocalDecl
            `t majorTy .default)
          motiveName motiveTy.consumeTypeAnnotationsVerified .default
        let hAllFrames : BindingContextLE current cMotive :=
          hIndices.trans (hMajorFrame.trans hMotiveFrame)
        let HindicesAtMajor : BoundFVarArray cMajor indices :=
          HindexOrigins.bound.mono hMajorFrame
        let HmajorAtMajor : BoundFVarArray cMajor #[major] := by
          simpa [cMajor, major] using
            (BoundFVarArray.empty cIndices).pushCurrent
              `t majorTy .default
        have hsourceShape : motiveTy.consumeTypeAnnotationsVerified =
            cMajor.lctx.mkForall indices
              (cMajor.lctx.mkForall #[major] (.sort elimLevel)) := by
          change motiveTy.consumeTypeAnnotationsVerified = motiveTy
          exact Hframe.motiveSourceEq
        have hnewMotiveShape : motiveTy.consumeTypeAnnotationsVerified =
            cMotive.lctx.mkForall indices
              (cMotive.lctx.mkForall #[major] (.sort elimLevel)) := by
          calc
            motiveTy.consumeTypeAnnotationsVerified =
                cMajor.lctx.mkForall indices
                  (cMajor.lctx.mkForall #[major] (.sort elimLevel)) :=
              hsourceShape
            _ = cMotive.lctx.mkForall indices
                  (cMajor.lctx.mkForall #[major] (.sort elimLevel)) :=
              (HindicesAtMajor.mkForall_mono hMotiveFrame _).symm
            _ = cMotive.lctx.mkForall indices
                  (cMotive.lctx.mkForall #[major] (.sort elimLevel)) :=
              congrArg (fun body => cMotive.lctx.mkForall indices body)
                (HmajorAtMajor.mkForall_mono hMotiveFrame _).symm
        let nextInfo : AddInductive.RecInfo := {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major }
        have hnewMotiveShape' : motiveTy.consumeTypeAnnotationsVerified =
            cMotive.lctx.mkForall nextInfo.indices
              (cMotive.lctx.mkForall #[nextInfo.major]
                (.sort elimLevel)) := by
          change motiveTy.consumeTypeAnnotationsVerified =
            cMotive.lctx.mkForall indices
              (cMotive.lctx.mkForall #[major] (.sort elimLevel))
          exact hnewMotiveShape
        let HmotiveShapes' := HmotiveShapes.push Hbindings hAllFrames
          nextInfo motiveTy.consumeTypeAnnotationsVerified hnewMotiveShape'
        have hnewMajorShape : majorTy =
            (mkAppN (mkAppN stats.indConsts[recInfos.size]! stats.params)
              nextInfo.indices).consumeTypeAnnotationsVerified := by
          simp only [majorTy, nextInfo]
          rw [hprogress]
        let HmajorShapes' := HmajorShapes.push nextInfo majorTy hnewMajorShape
        let HmajorExtension :=
          RecursorContextExtension.withLocalDecl (name := `t)
            (bi := .default) Rindices
            Hframe.majorTr Hframe.majorType
        let HmotiveExtension :=
          RecursorContextExtension.withLocalDecl (name := motiveName)
            (bi := .default) Rmajor
            Hframe.motiveTr Hframe.motiveType
        let HframeExtension : RecursorContextExtension Rindices Rmotive :=
          HmajorExtension.trans HmotiveExtension
        let HrootExtension : RecursorContextExtension R Rmotive :=
          Hrecent.contextExtension.trans HframeExtension
        have HfamilyTrMajor := HmajorExtension.weakTrExprS Hframe.familyTr
        have HfamilyTrMotive :=
          HmotiveExtension.weakTrExprS HfamilyTrMajor
        have HfamilyTypingMajor :=
          HmajorExtension.weakHasType Hcanonical.familyTyping
        have HfamilyTypingMotive :=
          HmotiveExtension.weakHasType HfamilyTypingMajor
        have HmotiveTypeTrMotive :=
          HmotiveExtension.weakTrExprS Hframe.motiveTr
        have HfamilyTrSeed : TrExprS Rmotive.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams)
            Rmotive.mlctx.vlctx
            (mkAppN stats.indConsts[dIdx]! stats.params)
            ((Hframe.familyTarget.lift' (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)) := by
          simpa only [Rmotive] using HfamilyTrMotive
        have HfamilyTypingSeed : Rmotive.venv.HasType
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            Rmotive.mlctx.vlctx.toCtx
            ((Hframe.familyTarget.lift' (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0))
            ((Hcanonical.familyType.lift'
                (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)) := by
          simpa only [Rmotive] using HfamilyTypingMotive
        have HfamilyTypeIsType := HfamilyTypingSeed.isType
          Rmotive.checking.tr.wf Rmotive.mlctx_wf.tr.wf.toCtx
        have HfamilyTypeDefEq : Rmotive.venv.IsDefEqU
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            Rmotive.mlctx.vlctx.toCtx
            ((Hcanonical.familyType.lift'
                (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0))
            ((Hcanonical.familyType.lift'
                (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)) :=
          ⟨_, Classical.choose_spec HfamilyTypeIsType⟩
        have HmotiveTypeTrSeed : TrExprS Rmotive.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams)
            Rmotive.mlctx.vlctx
            (cMotive.lctx.mkForall nextInfo.indices
              (cMotive.lctx.mkForall #[nextInfo.major]
                (.sort elimLevel)))
            (Hframe.motiveTarget.lift'
              (HmotiveExtension.shift.consN 0)) := by
          rw [← hnewMotiveShape']
          simpa only [Rmotive] using HmotiveTypeTrMotive
        have HmotiveTypeDefEqMajor :=
          HmajorExtension.weakDefEqU HmotiveCanonical
        have hmajorLift (expression : VExpr) :
            expression.liftN 1 0 =
              expression.lift' (HmajorExtension.shift.consN 0) := by
          change expression.liftN 1 0 =
            expression.lift' ((Lift.skip .refl).consN 0)
          rw [← Lift.skipN_one, VExpr.lift'_consN_skipN]
        have HmotiveTypeDefEqMajor' : Rmajor.venv.IsDefEqU
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            Rmajor.mlctx.vlctx.toCtx Hframe.motiveTarget
            (Hcanonical.motiveType.lift'
              (HmajorExtension.shift.consN 0)) := by
          rw [Hframe.motiveTarget_eq]
          rw [hmajorLift]
          exact HmotiveTypeDefEqMajor
        have HmotiveTypeDefEqWeak :=
          HmotiveExtension.weakDefEqU HmotiveTypeDefEqMajor'
        have HmotiveTypeDefEqSeed : Rmotive.venv.IsDefEqU
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            Rmotive.mlctx.vlctx.toCtx
            (Hframe.motiveTarget.lift'
              (HmotiveExtension.shift.consN 0))
            ((Hcanonical.motiveType.lift'
                (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)) := by
          simpa only [Rmotive] using HmotiveTypeDefEqWeak
        have htargetLt : dIdx < decl.types.length :=
          (List.getElem?_eq_some_iff.mp Hheader.targetAt).1
        have htargetEq : decl.types[dIdx] = Hheader.target := by
          have htargetAt := Hheader.targetAt
          rw [List.getElem?_eq_getElem htargetLt] at htargetAt
          exact Option.some.inj htargetAt
        have hseedIndexCount : indices.size =
            (decl.types[dIdx]'htargetLt).numIndices := by
          rw [htargetEq]
          have hguard : indices.size = stats.nindices[dIdx]! := by
            simpa using harity
          exact hguard.trans (by
            simp [Array.getElem!_eq_getD, Hheader.indexCount])
        let HindicesAtMotive : BoundFVarArray cMotive indices :=
          HindexOrigins.bound.mono (hMajorFrame.trans hMotiveFrame)
        let HmajorAtMotiveBound : BoundFVarArray cMotive #[major] :=
          HmajorAtMajor.mono hMotiveFrame
        rcases Hframe.motiveClosed with
          ⟨hclosedSize, motiveClosedTarget, HmotiveClosedTr,
            HmotiveClosedType, hmotiveClosedTarget⟩
        let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
        have HnarrowFamily :=
          (Hheader.recursorNarrowFamilyPrefixTranslation Helim Rindices
            Hsynthesis HnarrowStats henvIndices).1
        have HnarrowIndexFVars : ∀ arg ∈ indices.toList,
            arg.FVarsIn (· ∈ scope.fvars) := by
          have go : ∀ {sources targets : List _},
              List.Forall₂ (TrExprS Rindices.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                scope) sources targets →
              ∀ arg ∈ sources, arg.FVarsIn (· ∈ scope.fvars) := by
            intro sources targets Htranslated arg harg
            induction Htranslated with
            | nil => simp at harg
            | cons Hhead Htail ih =>
              simp only [List.mem_cons] at harg
              rcases harg with rfl | harg
              · exact Hhead.fvarsIn
              · exact ih harg
          exact go HnarrowIndices
        have HmajorRawFVars :
            (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
              indices).FVarsIn (· ∈ scope.fvars) := by
          rw [Expr.mkAppN_eq_mkAppList]
          apply FVarsIn.mkAppList.mpr
          refine ⟨HnarrowFamily.fvarsIn, ?_⟩
          exact HnarrowIndexFVars
        have HmajorTyFVars : majorTy.FVarsIn (· ∈ scope.fvars) := by
          exact Expr.consumeTypeAnnotationsVerified_fvarsIn HmajorRawFVars
        rcases Helim.sortType (env := Rindices.venv) (Δ := scope) with
          ⟨narrowSortLevel, HsortNarrow, _HsortNarrowType⟩
        have hone : 1 ≤ Rmajor.mlctx.length := by
          dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
          simp
        have hmajorRecent : #[major].toList.reverse =
            (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
          dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl]
          simp
        have hmajorConcrete : majorBody =
            Rmajor.mlctx.mkForall 1 hone (.sort elimLevel) := by
          dsimp only [majorBody]
          rw [← Rmajor.lctx_eq]
          exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent
        have HmajorBodyFVars : majorBody.FVarsIn
            (· ∈ scope.fvars) := by
          rw [hmajorConcrete]
          have HsortAbstract :
              (Expr.abstract1 ⟨cIndices.ngen.curr⟩
                (.sort elimLevel)).FVarsIn (· ∈ scope.fvars) := by
            apply FVarsIn.abstract1_of
            exact HsortNarrow.fvarsIn.mono fun _ h => Or.inr h
          simpa only [Rmajor, RecursorContextWF.withLocalDecl,
            TypeChecker.MLCtx.mkForall] using
            (show (Expr.forallE `t majorTy
                (Expr.abstract1 ⟨cIndices.ngen.curr⟩ (.sort elimLevel))
                .default).FVarsIn
                (· ∈ scope.fvars) from
              ⟨HmajorTyFVars, HsortAbstract⟩)
        let hmajorLE := BindingContextLE.withLocalDecl cIndices
          Rindices.toBindingContextWF `t majorTy .default
        have hmotiveConcrete : motiveTy =
            cIndices.lctx.mkForall indices majorBody := by
          dsimp [motiveTy, majorBody]
          exact Hrecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
            hmajorLE _
        have hmotiveMkForall : motiveTy =
            Rindices.mlctx.mkForall indices.size Hrecent.size_le
              majorBody := by
          rw [hmotiveConcrete, ← Rindices.lctx_eq]
          exact Rindices.mlctx_wf.mkForall_eq indices.size Hrecent.size_le
            Hrecent.reverse_eq
        have hfrontLength : Hruntime.frontSourceDomains.length =
            indices.size := by
          rw [hfront, Hsynthesis.indexCount, ← hindicesSize]
        have hfrontLE : Hruntime.frontSourceDomains.length ≤
            Rindices.mlctx.length := by
          rw [hfrontLength]
          exact Hrecent.size_le
        have HmotiveSourceFVarsAtBase : motiveTy.FVarsIn
            (· ∈ VLCtx.fvars
              (scope.drop Hruntime.frontSourceDomains.length)) := by
          rw [hmotiveMkForall]
          simpa only [hfrontLength] using
            Hruntime.front.mkForall_fvarsIn_sourceBase
              Rindices.onlyLams Rindices.mlctx_wf Hruntime.context
              hfrontLE majorBody HmajorBodyFVars
        have HmotiveClosedTrSeed : TrExprS Rmotive.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams)
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
            (cMotive.lctx.mkForall nextInfo.indices
              (cMotive.lctx.mkForall #[nextInfo.major]
                (.sort elimLevel))) motiveClosedTarget := by
          rw [← hnewMotiveShape']
          change TrExprS Rindices.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams)
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
            motiveTy.consumeTypeAnnotationsVerified motiveClosedTarget
          simpa only [motiveTy, cMajor] using HmotiveClosedTr
        have HmotiveClosedTypeSeed : Rmotive.venv.IsType
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx.toCtx
            motiveClosedTarget := by
          change Rindices.venv.IsType
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx.toCtx
            motiveClosedTarget
          exact HmotiveClosedType
        have hcanonicalLevelTranslation : stats.levels.mapM
            (VLevel.ofLevel
              (AddInductive.getRecLevelParams elimLevel base.lparams)) =
            some (Hheader.recursorAbstractLevels Helim) := by
          cases elimLevel with
          | zero =>
            simpa [mkRecInfos.loopArgs1.CheckedRecursorHeaderAt.recursorAbstractLevels,
              mkRecInfos.loopArgs1.CheckedRecursorHeaderAt.abstractLevels,
              AddInductive.getRecLevelParams] using
              Hheader.materialized.levelTranslation
          | param fresh =>
            have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim
              Hheader.materialized.levelTranslation
            simpa [mkRecInfos.loopArgs1.CheckedRecursorHeaderAt.recursorAbstractLevels,
              mkRecInfos.loopArgs1.CheckedRecursorHeaderAt.abstractLevels,
              AddInductive.getRecLevelParams] using hshifted
          | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
            simp [AddInductive.AdmissibleElimLevel] at Helim
        rcases Hruntime.front.base with
          ⟨motiveSourceScope, motiveSourceExpanded, motiveSourceShift,
            hmotiveSourceScope, hmotiveSourceExpanded, hmotiveSourceShift,
            HmotiveSourceLift⟩
        have hfrontSourceLength : Hruntime.frontSourceDomains.length =
            indices.size := by
          rw [hfront, Hsynthesis.indexCount, ← hindicesSize]
        have hfrontExpandedLength : Hruntime.frontExpandedDomains.length =
            indices.size := by
          rw [← Hruntime.front.length_eq, hfrontSourceLength]
        have hmotiveSourceScope' :
            scope.drop Hsynthesis.indices.length = motiveSourceScope := by
          simpa [hfront] using hmotiveSourceScope
        have hmotiveSourceParameterScope :
          motiveSourceScope = Hsuffix.parameterDecls := by
          rw [← hmotiveSourceScope', Hsynthesis.indexCount]
          exact hscopeBase
        have HmotiveSourceFVarsNarrow : motiveTy.FVarsIn
            (· ∈ VLCtx.fvars motiveSourceScope) := by
          rw [← hmotiveSourceScope']
          simpa [hfront] using HmotiveSourceFVarsAtBase
        have HmotiveSourceNoBV : VLCtx.NoBV motiveSourceScope := by
          change VLCtx.bvars motiveSourceScope = 0
          rw [← hmotiveSourceScope', ← hfront]
          rw [Hruntime.front.sourceBaseBVars]
          exact Hruntime.noBV
        have hmotiveSourceScopeCtx : VLCtx.toCtx motiveSourceScope =
            Hsynthesis.params.reverse := by
          have hdecomposition := Hruntime.front.sourceContext
          rw [hfront, Hsynthesis.scopeCtx, hmotiveSourceScope'] at hdecomposition
          exact List.append_inj_right hdecomposition.symm rfl
        have HmotiveSourceContext : VLCtx.IsDefEq Rindices.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            motiveSourceExpanded
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx := by
          have Hdrop := Hruntime.context.drop indices.size
          rw [← Rindices.onlyLams.vlctx_dropN indices.size hclosedSize]
            at Hdrop
          have hexpandedDrop : Hruntime.expanded.drop indices.size =
              motiveSourceExpanded := by
            simpa [hfrontExpandedLength] using hmotiveSourceExpanded
          change VLCtx.IsDefEq Rindices.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams).length
            (Hruntime.expanded.drop indices.size)
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx at Hdrop
          rw [hexpandedDrop] at Hdrop
          exact Hdrop
        let Hseed : RecursorMotiveTelescopeSeed Rmotive stats decl dIdx
            nextInfo elimLevel := {
          canonical := {
            target_lt := htargetLt
            params := Hsynthesis.params
            indices := Hsynthesis.indices
            levels := Hheader.recursorAbstractLevels Helim
            family := VExpr.mkApps
              ((VExpr.const Hheader.target.name
                (Hheader.recursorAbstractLevels Helim)).liftN
                  Hsynthesis.params.length 0)
              (recursorCanonicalVars Hsynthesis.params.length)
            familyResult := narrowTarget
            motiveType := VExpr.wrapForalls Hsynthesis.indices
              (.forallE
                (VExpr.mkApps
                  ((VExpr.mkApps
                    ((VExpr.const Hheader.target.name
                      (Hheader.recursorAbstractLevels Helim)).liftN
                        Hsynthesis.params.length 0)
                    (recursorCanonicalVars Hsynthesis.params.length)).liftN
                      Hsynthesis.indices.length 0)
                  (recursorCanonicalVars Hsynthesis.indices.length))
                (.sort Hframe.resultLevel))
            resultLevel := Hframe.resultLevel
            params_length := Hsynthesis.parameterCount
            indices_length := by
              simpa [nextInfo] using Hsynthesis.indexCount.trans
                hindicesSize.symm
            levels_length := by
              rw [htargetEq]
              exact Hheader.recursorAbstractLevels_length Helim
            levels_wf := Hheader.recursorAbstractLevels_wf Helim
            levels_translation := hcanonicalLevelTranslation
            family_eq := by rw [htargetEq]
            motiveType_eq := rfl
            family_typing := by
              simpa [Rmotive, Rmajor] using
                Hheader.recursorCanonicalFamilyPrefix Helim Rindices
                  Hsynthesis henvIndices
            familyApplicationType := by
              let canonicalFamily := VExpr.mkApps
                ((VExpr.const Hheader.target.name
                  (Hheader.recursorAbstractLevels Helim)).liftN
                    Hsynthesis.params.length 0)
                (recursorCanonicalVars Hsynthesis.params.length)
              let canonicalMajor := VExpr.mkApps
                (canonicalFamily.liftN Hsynthesis.indices.length 0)
                (recursorCanonicalVars Hsynthesis.indices.length)
              let canonicalBody := VExpr.forallE canonicalMajor
                (.sort Hframe.resultLevel)
              have hcanonicalMajor :
                  canonicalMajor.lift' Hruntime.shift =
                    Hframe.majorSourceTarget := by
                simpa [canonicalBody, canonicalMajor, canonicalFamily,
                  VExpr.liftN] using
                  hcanonicalMotiveBody
              have HmajorSource : Rindices.venv.IsType
                  (AddInductive.getRecLevelParams elimLevel
                    base.lparams).length
                  Rindices.mlctx.vlctx.toCtx Hframe.majorSourceTarget :=
                Hframe.majorType.defeqU_l Rindices.checking.tr.wf
                  Rindices.mlctx_wf.tr.wf.toCtx
                  Hframe.majorSourceDefEq.symm
              have HmajorExpanded := HmajorSource.defeqDFC
                Rindices.checking.tr.wf.ordered
                (Hruntime.context.defeqCtx.symm
                  Rindices.checking.tr.wf.ordered)
              have HcanonicalExpanded : Rindices.venv.IsType
                  (AddInductive.getRecLevelParams elimLevel
                    base.lparams).length
                  Hruntime.expanded.toCtx
                  (canonicalMajor.lift' Hruntime.shift) := by
                simpa [hcanonicalMajor] using HmajorExpanded
              have HcanonicalNarrow :=
                (VEnv.IsType.weak'_iff Rindices.checking.tr.wf
                  Hruntime.context.wf.toCtx Hruntime.lift.toCtx).1
                    HcanonicalExpanded
              simpa [Rmotive, Rmajor, Hsynthesis.scopeCtx,
                canonicalMajor, canonicalFamily] using HcanonicalNarrow
            telescope := by
              exact RecursorMotiveTelescope.wrapForalls Hsynthesis.indices
                (VExpr.mkApps
                  ((VExpr.const Hheader.target.name
                    (Hheader.recursorAbstractLevels Helim)).liftN
                      Hsynthesis.params.length 0)
                  (recursorCanonicalVars Hsynthesis.params.length))
                narrowTarget Hframe.resultLevel }
          target_lt := htargetLt
          indexCount := hseedIndexCount
          family := (Hframe.familyTarget.lift'
            (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)
          familyActualType :=
            (Hcanonical.familyType.lift'
              (HmajorExtension.shift.consN 0)).lift'
                (HmotiveExtension.shift.consN 0)
          familyType :=
            (Hcanonical.familyType.lift'
              (HmajorExtension.shift.consN 0)).lift'
                (HmotiveExtension.shift.consN 0)
          motiveActualType :=
            Hframe.motiveTarget.lift' (HmotiveExtension.shift.consN 0)
          motiveType :=
            (Hcanonical.motiveType.lift'
              (HmajorExtension.shift.consN 0)).lift'
                (HmotiveExtension.shift.consN 0)
          resultLevel := Hframe.resultLevel
          motiveClosedScope :=
            (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
          motiveClosedAmbient := Hsuffix.ambientDecls
          motiveParameterScope := Hsuffix.parameterDecls
          motiveClosedContext := by
            change (Rindices.mlctx.dropN indices.size hclosedSize).vlctx =
              Hsuffix.ambientDecls ++ Hsuffix.parameterDecls
            rw [show hclosedSize = Hrecent.size_le from rfl,
              Hrecent.drop_eq]
            exact Hsuffix.context
          motiveParameterAlignment := by
            change VEnv.IsDefEqCtx Rindices.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              [] Hsynthesis.params.reverse Hsuffix.parameterDecls.toCtx
            rw [← hcanonicalParams]
            exact VEnv.IsDefEqCtx.refl (OnCtx.append_right (by
              rw [← Hsynthesis.scopeCtx]
              exact Hsynthesis.scopeWF.toCtx))
          motiveParameterDecls := Hsuffix.cached
          motiveSourceScope := motiveSourceScope
          motiveSourceExpanded := motiveSourceExpanded
          motiveSourceShift := motiveSourceShift
          motiveSourceAlignment := by
            change VEnv.IsDefEqCtx Rindices.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              [] Hsynthesis.params.reverse (VLCtx.toCtx motiveSourceScope)
            rw [hmotiveSourceScopeCtx]
            exact VEnv.IsDefEqCtx.refl (OnCtx.append_right (by
              rw [← Hsynthesis.scopeCtx]
              exact Hsynthesis.scopeWF.toCtx))
          motiveSourceParameterScope := hmotiveSourceParameterScope
          motiveSourceLift := HmotiveSourceLift
          motiveSourceContext := HmotiveSourceContext
          motiveSourceNoBV := HmotiveSourceNoBV
          motiveSourceFVars := by
            rw [← hnewMotiveShape', Hframe.motiveSourceEq]
            exact HmotiveSourceFVarsNarrow
          motiveClosedTarget := motiveClosedTarget
          motiveClosedTr := HmotiveClosedTrSeed
          motiveClosedType := HmotiveClosedTypeSeed
          motiveClosedCanonicalTarget :=
            VExpr.wrapForalls Hruntime.frontExpandedDomains
              (.forallE Hframe.majorSourceTarget
                (.sort Hframe.resultLevel))
          motiveClosedCanonicalEq := by
            let canonicalBody := VExpr.forallE
              (VExpr.mkApps
                ((VExpr.mkApps
                  (.const Hheader.target.name
                    (Hheader.recursorAbstractLevels Helim))
                  (recursorCanonicalVars Hsynthesis.params.length)).liftN
                    Hsynthesis.indices.length 0)
                (recursorCanonicalVars Hsynthesis.indices.length))
              (.sort Hframe.resultLevel)
            have Hclose := Hruntime.front.closeAtBase motiveSourceShift
              hmotiveSourceShift canonicalBody
            have hbody := hcanonicalMotiveBody
            dsimp only at hbody
            rw [hfront, hbody] at Hclose
            simpa [canonicalBody, VExpr.liftN] using Hclose
          motiveClosedCanonicalDefEq := by
            change Rindices.venv.IsDefEqU
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              (Rindices.mlctx.dropN indices.size hclosedSize).vlctx.toCtx
              motiveClosedTarget
              (VExpr.wrapForalls Hruntime.frontExpandedDomains
                (.forallE Hframe.majorSourceTarget
                  (.sort Hframe.resultLevel)))
            rw [Rindices.onlyLams.toCtx_dropN indices.size hclosedSize]
            rw [hmotiveClosedTarget]
            exact HmotiveCanonicalClosed
          motiveReopenedCanonicalTarget :=
            (((VExpr.wrapForalls Hruntime.frontExpandedDomains
              (.forallE Hframe.majorSourceTarget
                (.sort Hframe.resultLevel))).liftN indices.size 0).lift'
                  (HmajorExtension.shift.consN 0)).lift'
                    (HmotiveExtension.shift.consN 0)
          motiveTypeCanonicalEq := by
            rw [hcanonicalMotiveReopen]
          familyUnique := HnarrowStats.familyPrefixUnique dIdx htargetLt
          familyTr := HfamilyTrSeed
          familyTyping := HfamilyTypingSeed
          familyTypeDefEq := HfamilyTypeDefEq
          indicesBound := HindicesAtMotive
          majorBound := HmajorAtMotiveBound
          motiveTypeTr := HmotiveTypeTrSeed
          motiveTypeDefEq := HmotiveTypeDefEqSeed
          telescope := (Hcanonical.telescope.lift'
            (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0) }
        have HseedParams0 :
            VEnv.IsDefEqCtx Rmotive.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              [] Hseed.canonical.params.reverse
                Hsuffix.parameterDecls.toCtx := by
          change VEnv.IsDefEqCtx Rindices.venv
            (AddInductive.getRecLevelParams elimLevel base.lparams).length []
            Hsynthesis.params.reverse Hsuffix.parameterDecls.toCtx
          rw [← hcanonicalParams]
          exact VEnv.IsDefEqCtx.refl (OnCtx.append_right (by
            rw [← Hsynthesis.scopeCtx]
            exact Hsynthesis.scopeWF.toCtx))
        have HseedPair :
            ∃ S : RecursorMotiveTelescopeSeed Rmotive stats decl
                recInfos.size nextInfo elimLevel,
              VEnv.IsDefEqCtx Rmotive.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                [] S.canonical.params.reverse
                  Hsuffix.parameterDecls.toCtx := by
          rw [hprogress]
          exact ⟨Hseed, HseedParams0⟩
        rcases HseedPair with ⟨Hseed', HseedParams⟩
        have HseedAt : RecursorMotiveTelescopeAt Rmotive stats decl
            recInfos.size nextInfo elimLevel := Hseed'.toTelescopeAt
        let Htelescopes' :=
          (Htelescopes.mono HrootExtension).push nextInfo
            HseedAt Hseed' HseedParams
        refine resultSemantics Hbase stats indTypes elimLevel Helim Hheaders
          hconsume (dIdx + 1)
          (recInfos.push {
            motive := .fvar ⟨cMajor.ngen.curr⟩
            minors := #[]
            indices
            major }) k Rmotive (by simpa [Rmotive, Rmajor] using henvIndices)
          HsuffixMotive HparamsCtx' HstatsMotive Hbindings' Horigins'
          ?_ ?_ ?_ ?_ (by
            simpa [hparameterDeclsMotive] using Htelescopes') ?_ Hparams'
          HnoAlias' Horder'
          (Hroot.trans <| hIndices.trans <|
            (BindingContextLE.withLocalDecl cIndices
              Rindices.toBindingContextWF `t majorTy .default).trans <|
              BindingContextLE.withLocalDecl cMajor
                (Rindices.toBindingContextWF.withLocalDecl
                  `t majorTy .default)
                motiveName motiveTy.consumeTypeAnnotationsVerified .default)
          (by simp [hprogress])
          (by
            apply Harities.push
            have hnew : indices.size = stats.nindices[dIdx]! := by
              simpa using harity
            simpa [hprogress] using hnew)
          Hempty.push Hblueprints.pushEmpty ?_
        · change RecursorTranslatedOriginTypes Rmotive
            (Horigins.majorTypes.push majorTy)
          exact HmajorAtMotive
        · change RecInfoMajorTypeShapes stats
            (recInfos.push {
              motive := .fvar ⟨cMajor.ngen.curr⟩
              minors := #[]
              indices
              major })
            (Horigins.majorTypes.push majorTy)
          exact HmajorShapes'
        · change RecursorTranslatedOriginTypes Rmotive
            (Horigins.motiveTypes.push motiveTy.consumeTypeAnnotationsVerified)
          exact HmotiveAtMotive
        · change RecInfoMotiveTypeShapes cMotive
            (recInfos.push {
              motive := .fvar ⟨cMajor.ngen.curr⟩
              minors := #[]
              indices
              major })
            (Horigins.motiveTypes.push motiveTy.consumeTypeAnnotationsVerified)
            elimLevel
          exact HmotiveShapes'
        · change RecursorTranslatedOriginTypeRows Rmotive
            (Horigins.indexTypes.push indexOrigins)
          exact HindexRows'
        · intro cOut outDepth out Rout henvOut HsuffixOut
            hparameterDeclsOut HstatsOut HbindingsOut
            HoriginsOut HmajorOut HmajorShapesOut HmotiveOut HmotiveShapesOut
            HtelescopesOut HindexRowsOut
            HparamsOut HnoAliasOut HorderOut HaritiesOut HemptyOut
            HblueprintsOut HrootOut houtSize
          apply Hk out Rout henvOut HsuffixOut
            (hparameterDeclsOut.trans hparameterDeclsMotive)
            HstatsOut HbindingsOut
            HoriginsOut HmajorOut HmajorShapesOut HmotiveOut HmotiveShapesOut
            HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
            HaritiesOut HemptyOut HblueprintsOut HrootOut
          simp only [Array.size_push] at houtSize
          omega
      · simp only [loopK]
        rw [if_neg harity]
        exact Except.WF.throw
  · rw [dif_neg hidx]
    exact Hk recInfos R henv Hsuffix rfl Hstats Hbindings Horigins HmajorTypes
      HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexTypeRows Hparams HnoAlias
      Horder Harities Hempty Hblueprints Hroot (by omega)
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopUArgs.loop

/-- Every higher-order argument opened while exposing a recursive field is a
fresh ordinary local declaration, retained in the exact array later passed to
`LocalContext.mkLambda`. -/
theorem resultBindings {alpha : Type}
    (k : Expr → Array Expr → AddInductive.M alpha)
    {uiTy : Expr} {xs : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hxs : FreshBoundFVarArray root c xs)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ uiTy xs c, BindingContextWF c →
      FreshBoundFVarArray root c xs → BindingContextLE root c →
      (k uiTy xs c).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs.loop k uiTy xs fuel c).WF Q := by
  induction fuel generalizing c uiTy xs with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopUArgs.loop] at h
  | succ fuel ih =>
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotationsVerified bi }
      unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
        AddInductive.instMonadLocalNameGeneratorM
        AddInductive.instMonadWithReaderOfLocalContextM
      change ((monadLift (TypeChecker.whnf
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
          AddInductive.M Expr) c' >>= fun normalized =>
        AddInductive.mkRecInfos.loopUArgs.loop k normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) fuel c').WF Q
      have hwhnf :
          ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c').WF (fun _ => True) := by
        intro _ _
        trivial
      exact hwhnf.bind fun normalized _ =>
        ih (Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi)
          (Hxs.pushCurrent Hc Hroot name dom.consumeTypeAnnotationsVerified bi)
          (Hroot.trans <| BindingContextLE.withLocalDecl c Hc name
            dom.consumeTypeAnnotationsVerified bi)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change (k _ xs c).WF Q
      exact Hk _ _ _ Hc Hxs Hroot

/-- Semantic refinement of the higher-order recursive-argument telescope.
Every executable binder opened by `loopUArgs.loop` is checked under the
recursor universe list, and the exact consecutive suffix is retained for the
`LocalContext.mkForall` which constructs the induction-hypothesis type. -/
theorem resultSemantics {alpha : Type}
    (head : Expr) (k : Expr → Array Expr → AddInductive.M alpha)
    {recLparams : List Name}
    {root : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {uiTy : Expr} {xs : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (R : RecursorContextWF c recLparams)
    {typeTarget : VExpr}
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx uiTy typeTarget)
    (htypeType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx typeTarget)
    (Hxs : RecursorRecentBoundFVarArray Rroot R xs)
    {appliedTarget : VExpr}
    (happlied : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN head xs) appliedTarget)
    (happliedType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx appliedTarget typeTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {exposedTarget appliedTarget : VExpr}
      {args : Array Expr},
      TrExpr Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType exposedTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx exposedTarget →
      RecursorRecentBoundFVarArray Rroot Rcurrent args →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN head args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget exposedTarget →
      (k exposedType args current).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs.loop k uiTy xs fuel c).WF Q := by
  induction fuel generalizing c uiTy xs typeTarget appliedTarget with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopUArgs.loop] at h
  | succ fuel ih =>
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      rcases TrExpr.forallE_source htype with
        ⟨sourceDom, sourceBody, hdom, hbody, hdomType,
          hbodyType, hforallEq⟩
      rcases hconsume c recLparams R hdom hdomType with
        ⟨consumedDom, Hdom⟩
      rcases Hdom.body R hbody with
        ⟨consumedBody, hbodyConsumed, hbodyEq⟩
      refine withLocalDecl.recursorWF (name := name) (bi := bi) (Q := Q)
        R Hdom.consumed Hdom.isType ?_
      let R' := R.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have happliedFn := happlied.weakFV R.checking.tr.wf.ordered W
        R'.mlctx_wf.tr.wf
      have happliedFnType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (appliedTarget.liftN 1 0)
          ((VExpr.forallE sourceDom sourceBody).liftN 1 0) := by
        exact (happliedType.defeqU_r R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx hforallEq.symm).weakN
            R.checking.tr.wf.ordered W.toCtx
      have harg : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        apply TrExprS.fvar
        change VLCtx.find?
          ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
          (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0)
        simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
          VLocalDecl.value, VLocalDecl.type, VExpr.lift]
      have hargType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (.bvar 0) (sourceDom.liftN 1 0) := by
        have hlookup : R'.mlctx.vlctx.find? (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0) := by
          change VLCtx.find?
            ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx)
            (.inr ⟨c.ngen.curr⟩) =
              some ((.bvar 0), consumedDom.liftN 1 0)
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type, VExpr.lift]
        have hconsumed := R'.mlctx_wf.tr.wf.find?_wf
          R'.checking.tr.wf.ordered hlookup
        have hdomainEq := Hdom.source_defeq.choose_spec.weakN
          R.checking.tr.wf.ordered W.toCtx
        exact hconsumed.defeqU_r R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx hdomainEq.symm.toU
      have happlied' : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (mkAppN head (xs.push (.fvar ⟨c.ngen.curr⟩)))
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) := by
        simpa [mkAppN] using
          TrExprS.app happliedFnType hargType happliedFn harg
      have happliedType' : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) consumedBody := by
        have happ := VEnv.HasType.app happliedFnType hargType
        have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
        apply happ.defeqU_r R'.checking.tr.wf R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VExpr.instN_bvar0] using
            hbodyEq'
      have hopened := R.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbodyConsumed
      have hctx : VLCtx.IsDefEq R.venv recLparams.length
          ((none, .vlam sourceDom) :: R.mlctx.vlctx)
          ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
        VLCtx.IsDefEq.cons
          (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
          (.vlam Hdom.source_defeq.choose_spec)
      have hsourceBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx sourceBody := by
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
          hbodyType.defeqDFC R.checking.tr.wf.ordered hctx.defeqCtx
      have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
      have hconsumedBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx consumedBody := by
        apply hsourceBodyType.defeqU_l R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
      have hnormalize := whnfInRecursorContext.scopeWF R' hopened
      exact hnormalize.bind fun normalized hnormalized =>
        ih R' hnormalized.2 hconsumedBodyType
          (Hxs.pushCurrent name dom.consumeTypeAnnotationsVerified consumedDom bi
            Hdom.consumed Hdom.isType) happlied' happliedType'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change (k _ xs c).WF Q
      exact Hk R htype htypeType Hxs happlied happliedType

/-- Semantic refinement of `loopUArgs.loop` which reconstructs the complete
higher-order recursive-domain judgment on the way back out of the forall
telescope.  The terminal executable check supplies the direct family
application; each traversed binder contributes one `RecursiveArgAtTarget`
`forallE` constructor. -/
theorem resultRecursiveDomain {alpha : Type}
    (head : Expr)
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Nat → AddInductive.M alpha)
    {decl : VInductDecl} {recLparams : List Name}
    {root : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Rroot.venv stats.indConsts)
    {initialType uiTy : Expr} {xs : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : Nat → alpha → Prop}
    (R : RecursorContextWF c recLparams)
    {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {typeTarget : VExpr}
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx uiTy typeTarget)
    (htypeType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx typeTarget)
    (Hxs : RecursorRecentBoundFVarArray Rroot R xs)
    (Htrace : RecursorLoopUArgsPrefix root initialType c uiTy xs)
    {P : FVarId → Prop}
    (htypeScope : uiTy.FVarsIn
      (fun fv => fv ∈ Hxs.fvars ∨ P fv))
    (hcurrentUp : IsFVarUpSet
      (fun fv => fv ∈ Hxs.fvars ∨ P fv) R.mlctx.vlctx)
    {appliedTarget : VExpr}
    (happlied : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN head xs) appliedTarget)
    (happliedType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx appliedTarget typeTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      RecursorLoopUArgsPrefix root initialType current exposedType args →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hrecent : RecursorRecentBoundFVarArray Rroot Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN head args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      AddInductive.isValidIndApp? stats exposedType = some target →
      exposedType.FVarsIn
        (fun fv => fv ∈ Hrecent.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hrecent.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      (k exposedType args target current).WF (Q target)) :
    (AddInductive.mkRecInfos.loopUArgs.loop
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        k exposedType args target)
      uiTy xs fuel c).WF fun out =>
        ∃ target, ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth typeTarget ∧ Q target out := by
  induction fuel generalizing c uiTy xs typeTarget appliedTarget depth with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopUArgs.loop] at h
  | succ fuel ih =>
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      rcases TrExpr.forallE_source htype with
        ⟨sourceDom, sourceBody, hdom, hbody, hdomType,
          hbodyType, hforallEq⟩
      rcases hconsume c recLparams R hdom hdomType with
        ⟨consumedDom, Hdom⟩
      rcases Hdom.body R hbody with
        ⟨consumedBody, hbodyConsumed, hbodyEq⟩
      refine withLocalDecl.recursorWF (name := name) (bi := bi)
        (Q := fun out =>
          ∃ target, ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth typeTarget ∧ Q target out)
        R Hdom.consumed Hdom.isType ?_
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotationsVerified bi }
      let R' : RecursorContextWF c' recLparams :=
        R.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have happliedFn := happlied.weakFV R.checking.tr.wf.ordered W
        R'.mlctx_wf.tr.wf
      have happliedFnType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (appliedTarget.liftN 1 0)
          ((VExpr.forallE sourceDom sourceBody).liftN 1 0) := by
        exact (happliedType.defeqU_r R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx hforallEq.symm).weakN
            R.checking.tr.wf.ordered W.toCtx
      have harg : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        apply TrExprS.fvar
        change VLCtx.find?
          ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
          (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0)
        simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
          VLocalDecl.value, VLocalDecl.type, VExpr.lift]
      have hargType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (.bvar 0) (sourceDom.liftN 1 0) := by
        have hlookup : R'.mlctx.vlctx.find? (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0) := by
          change VLCtx.find?
            ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx)
            (.inr ⟨c.ngen.curr⟩) =
              some ((.bvar 0), consumedDom.liftN 1 0)
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type, VExpr.lift]
        have hconsumed := R'.mlctx_wf.tr.wf.find?_wf
          R'.checking.tr.wf.ordered hlookup
        have hdomainEq := Hdom.source_defeq.choose_spec.weakN
          R.checking.tr.wf.ordered W.toCtx
        exact hconsumed.defeqU_r R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx hdomainEq.symm.toU
      have happlied' : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (mkAppN head (xs.push (.fvar ⟨c.ngen.curr⟩)))
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) := by
        simpa [mkAppN] using
          TrExprS.app happliedFnType hargType happliedFn harg
      have happliedType' : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) consumedBody := by
        have happ := VEnv.HasType.app happliedFnType hargType
        have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
        apply happ.defeqU_r R'.checking.tr.wf R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VExpr.instN_bvar0] using
            hbodyEq'
      have hopened := R.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbodyConsumed
      let Hxs' := Hxs.pushCurrent name dom.consumeTypeAnnotationsVerified
        consumedDom bi Hdom.consumed Hdom.isType
      have hbodyScope : (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)).FVarsIn
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) := by
        have hbodyScopeBase : body.FVarsIn
            (fun fv => fv ∈ Hxs'.fvars ∨ P fv) := by
          apply htypeScope.2.mono
          intro fv h
          rcases h with hlocal | hroot
          · exact Or.inl (by
              change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
              exact List.mem_append_left _ hlocal)
          · exact Or.inr hroot
        simpa only [Expr.instantiate1_eq] using
          hbodyScopeBase.instantiate1 (by
            simp only [FVarsIn]
            exact Or.inl (by
              change (⟨c.ngen.curr⟩ : FVarId) ∈
                Hxs.fvars ++ [⟨c.ngen.curr⟩]
              simp))
      have hnewNotCurrent : (⟨c.ngen.curr⟩ : FVarId) ∉
          R.mlctx.vlctx.fvars := by
        intro hmem
        rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq] at hmem
        exact R.toBindingContextWF.current_not_mem hmem
      have hcurrentUp' : IsFVarUpSet
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) R.mlctx.vlctx := by
        apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hcurrentUp
        intro fv hfv
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl (by
              change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
              exact List.mem_append_left _ h)
          · exact Or.inr h
        · intro h
          rcases h with h | h
          · change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩] at h
            rcases List.mem_append.mp h with h | h
            · exact Or.inl h
            · simp only [List.mem_singleton] at h
              subst fv
              exact False.elim (hnewNotCurrent hfv)
          · exact Or.inr h
      have hnextUp : IsFVarUpSet
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) R'.mlctx.vlctx := by
        change IsFVarUpSet _
          ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotationsVerified.fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
        refine ⟨hcurrentUp', fun _ dep hdep => ?_⟩
        have hselected := (fvarsIn_iff.mp
          (Expr.consumeTypeAnnotationsVerified_fvarsIn htypeScope.1)).1 dep hdep
        rcases hselected with hlocal | hroot
        · exact Or.inl (by
            change dep ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
            exact List.mem_append_left _ hlocal)
        · exact Or.inr hroot
      have hsourceBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx sourceBody := by
        let hctxEq : VLCtx.IsDefEq R.venv recLparams.length
            ((none, .vlam sourceDom) :: R.mlctx.vlctx)
            ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
          VLCtx.IsDefEq.cons
            (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
            (.vlam Hdom.source_defeq.choose_spec)
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
          hbodyType.defeqDFC R.checking.tr.wf.ordered hctxEq.defeqCtx
      have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
      have hconsumedBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx consumedBody := by
        apply hsourceBodyType.defeqU_l R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv,
          RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
      let normalizeRun :=
        (monadLift (TypeChecker.whnf
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
            AddInductive.M Expr) c'
      have hnormalizeSemantic :=
        whnfInRecursorContext.scopeWF R' hopened
      have hnormalize : normalizeRun.WF fun normalized =>
          normalizeRun = .ok normalized ∧
          FVarsBelow R'.mlctx.vlctx
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized ∧
          TrExpr R'.venv recLparams R'.mlctx.vlctx normalized consumedBody := by
        intro normalized hrun
        exact ⟨hrun, hnormalizeSemantic normalized hrun⟩
      refine hnormalize.bind fun normalized hnormalized => ?_
      rcases hnormalized with ⟨hnormalizeRun, hnormalized⟩
      have Hstats' := Hstats.withFVar R'.checking.tr.wf R'.mlctx_wf.tr.wf
      have hctx' : VLCtx.NoIndConsts
          (decl.types.map (·.name)) R'.mlctx.vlctx := by
        apply VLCtx.NoIndConsts.cons hctx
        rfl
      have hnormalizedScope := hnormalized.1 _ hnextUp hbodyScope
      let Htrace' : RecursorLoopUArgsPrefix root initialType c' normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) :=
        .push Htrace rfl hnormalizeRun
      have Hrec := ih R' Hstats' hctx' hnormalized.2
        hconsumedBodyType
        Hxs' Htrace' hnormalizedScope hnextUp
        happlied' happliedType'
      exact Hrec.mono fun out Hout => by
        rcases Hout with ⟨target, htarget, hrecursive, hout⟩
        rcases hforallEq.symm with ⟨forallType, hforall⟩
        rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
        rcases hbodyEq with ⟨bodyType, hbodyEq⟩
        exact ⟨target, htarget, .forallE hforall hdomEq hbodyEq
          hrecursive, hout⟩
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change ((do
        let some target := AddInductive.isValidIndApp? stats _
          | throw (Lean.Kernel.Exception.other
            "recursive constructor field lost its inductive result type")
        k _ xs target) c).WF _
      rcases htype with ⟨syntaxTarget, hsyntax, hdefeq⟩
      cases hvalid : AddInductive.isValidIndApp? stats _ with
      | none =>
        simp only [hvalid, bind, Except.bind]
        exact Except.WF.throw
      | some target =>
        simp only [hvalid, bind, Except.bind]
        have htargetStats : target < stats.indConsts.size :=
          (checkPositivityStep.isValidIndApp?_some hvalid).1
        have htarget : target < decl.types.length := by
          rw [← Hstats.types_size]
          exact htargetStats
        let Hvalid := Hstats.validatedIndAppAt hsyntax hvalid htarget
          (by simpa only [Hxs.venv_eq] using hlit) hctx
        have Hterminal := Hk (target := target) R Htrace hsyntax hdefeq
          htypeType Hxs happlied happliedType hvalid htypeScope hcurrentUp
        exact Hterminal.mono fun out hout => by
          rcases hdefeq.symm with ⟨exprType, hterminal⟩
          exact ⟨target, htarget,
            VInductDecl.RecursiveArgAtTarget.direct hterminal
              Hvalid.application,
            hout⟩

end mkRecInfos.loopUArgs.loop

/-- Public binder-aware interface for `loopUArgs`, starting from its empty
local-argument accumulator. -/
theorem mkRecInfos.loopUArgs.resultBindings {alpha : Type}
    (ui : Expr) (k : Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hk : ∀ uiTy xs c', BindingContextWF c' →
      FreshBoundFVarArray c c' xs → BindingContextLE c c' →
      (k uiTy xs c').WF Q) :
    (AddInductive.mkRecInfos.loopUArgs ui k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopUArgs
  have hinfer :
      ((monadLift (TypeChecker.inferType ui) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hinfer.bind fun inferred _ => ?_
  have hwhnf :
      ((monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hwhnf.bind fun normalized _ => ?_
  change (AddInductive.mkRecInfos.loopUArgs.loop k normalized #[]
    c.fuel.inductiveFuel c).WF Q
  exact mkRecInfos.loopUArgs.loop.resultBindings k Hc
    (FreshBoundFVarArray.empty c) (BindingContextLE.refl c) Hk

/-- Public semantic interface for `loopUArgs` on the retained recursive-field
free variables supplied by `loopCtorArgs`.  Type inference is verified by the
free-variable computation lemma, then normalization and every higher-order
binder remain wholly inside the recursor universe interpretation. -/
theorem mkRecInfos.loopUArgs.resultSemantics {alpha : Type}
    (fv : FVarId) (k : Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    {Q : alpha → Prop}
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {exposedTarget appliedTarget : VExpr}
      {args : Array Expr},
      TrExpr Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType exposedTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx exposedTarget →
      (Hrecent : RecursorRecentBoundFVarArray R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget exposedTarget →
      (k exposedType args current).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv) k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopUArgs
  have hinfer := inferTypeFVarInRecursorContext.WF R hfield
  refine hinfer.bind fun inferred hinferred => ?_
  rcases hinferred with
    ⟨inferredTarget, _hbelow, hfieldAgain, hinferredTr, hfieldTyping⟩
  have hinferredType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
  have hnormalize := whnfInRecursorContext.scopeWF R hinferredTr
  refine hnormalize.bind fun normalized hnormalized => ?_
  change (AddInductive.mkRecInfos.loopUArgs.loop k normalized #[]
    c.fuel.inductiveFuel c).WF Q
  exact mkRecInfos.loopUArgs.loop.resultSemantics (.fvar fv) k R
    hconsume R hnormalized.2 hinferredType
    (RecursorRecentBoundFVarArray.empty R) (by
      change TrExprS R.venv recLparams R.mlctx.vlctx
        (.fvar fv) fieldTarget
      exact hfieldAgain)
    hfieldTyping Hk

/-- The public recursive-field interface retains the complete source domain,
not merely the validated family application exposed after traversing its
higher-order binders.  This is the semantic certificate needed to align the
implementation's selected recursive calls with `VInductDecl.RecursiveField`.
-/
theorem mkRecInfos.loopUArgs.resultRecursiveDomain {alpha : Type}
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Nat → AddInductive.M alpha)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (hfieldScope : P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {Q : Nat → alpha → Prop}
    (Hk : ∀ (Hinput : RecursorLoopUArgsInput c (.fvar fv))
      {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      RecursorLoopUArgsPrefix c Hinput.normalizedType current exposedType args →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hrecent : RecursorRecentBoundFVarArray R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      AddInductive.isValidIndApp? stats exposedType = some target →
      exposedType.FVarsIn
        (fun fv => fv ∈ Hrecent.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hrecent.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      (k exposedType args target current).WF (Q target)) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        k exposedType args target) c).WF fun out =>
          ∃ domain,
            R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
              fieldTarget domain ∧
            ∃ target, ∃ htarget : target < decl.types.length,
              decl.RecursiveArgAtTarget R.venv recLparams.length
                (decl.types[target]'htarget).name
                R.mlctx.vlctx.toCtx depth domain ∧ Q target out := by
  unfold AddInductive.mkRecInfos.loopUArgs
  let inferRun :=
    (monadLift (TypeChecker.inferType (.fvar fv)) : AddInductive.M Expr) c
  have hinferSemantic := inferTypeFVarInRecursorContext.WF R hfield
  have hinfer : inferRun.WF fun inferred =>
      inferRun = .ok inferred ∧
      ∃ inferredTarget, TrTyping R.venv recLparams R.mlctx.vlctx
        (.fvar fv) inferred fieldTarget inferredTarget := by
    intro inferred hr
    exact ⟨hr, hinferSemantic inferred hr⟩
  refine hinfer.bind fun inferred hinferred => ?_
  rcases hinferred with
    ⟨hinferRun, inferredTarget, _hbelow, hfieldAgain, hinferredTr,
      hfieldTyping⟩
  have hfieldSourceScope : (Expr.fvar fv).FVarsIn P := by
    simpa only [FVarsIn] using hfieldScope
  have hinferredScope : inferred.FVarsIn P :=
    _hbelow P hrootUp hfieldSourceScope
  have hinferredType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
  let normalizeRun :=
    (monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr) c
  have hnormalizeSemantic :=
    whnfInRecursorContext.scopeWF R hinferredTr
  have hnormalize : normalizeRun.WF fun normalized =>
      normalizeRun = .ok normalized ∧
      FVarsBelow R.mlctx.vlctx inferred normalized ∧
      TrExpr R.venv recLparams R.mlctx.vlctx normalized inferredTarget := by
    intro normalized hr
    exact ⟨hr, hnormalizeSemantic normalized hr⟩
  refine hnormalize.bind fun normalized hnormalized => ?_
  rcases hnormalized with ⟨hnormalizeRun, hnormalizedScope,
    hnormalizedTr⟩
  let Hinput : RecursorLoopUArgsInput c (.fvar fv) := {
    inferredType := inferred
    normalizedType := normalized
    inference := hinferRun
    normalization := hnormalizeRun }
  have hnormalizedScope : normalized.FVarsIn P :=
    hnormalizedScope P hrootUp hinferredScope
  change (AddInductive.mkRecInfos.loopUArgs.loop
    (fun exposedType args => do
      let some target := AddInductive.isValidIndApp? stats exposedType
        | throw (.other
          "recursive constructor field lost its inductive result type")
      k exposedType args target)
    normalized #[] c.fuel.inductiveFuel c).WF _
  have Hloop := mkRecInfos.loopUArgs.loop.resultRecursiveDomain
    (fuel := c.fuel.inductiveFuel) (.fvar fv) stats k R
    hconsume hlit R Hstats hctx hnormalizedTr hinferredType
    (RecursorRecentBoundFVarArray.empty R)
    (RecursorLoopUArgsPrefix.root (root := c) (source := normalized))
    (hnormalizedScope.mono fun _ h => Or.inr h)
    (by
      apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hrootUp
      intro fv _
      change P fv ↔ fv ∈ ([] : List FVarId) ∨ P fv
      simp)
    (by
      change TrExprS R.venv recLparams R.mlctx.vlctx
        (.fvar fv) fieldTarget
      exact hfieldAgain)
    hfieldTyping (Hk Hinput)
  exact Hloop.mono fun out hout => ⟨inferredTarget, hfieldTyping, hout⟩

/-- Source-level construction retained for one induction-hypothesis type.
It records the terminal family application and exact higher-order telescope
selected by `loopUArgs`, before the resulting type is installed as a local
declaration by `loopU`. -/
structure RecInfoHypothesisTypeOrigin
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (root : AddInductive.Context) (field type : Expr) where
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  exposedType : Expr
  args : Array Expr
  arguments_bound : FreshBoundFVarArray root current args
  loopInput : RecursorLoopUArgsInput root field
  loopTrace : RecursorLoopUArgsPrefix root loopInput.normalizedType current
    exposedType args
  field_fvar : ∃ fv, field = .fvar fv ∧ fv ∈ root.lctx.fvars
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  motive_is_fvar : ∃ fv,
    recInfos[ownerIdx]!.motive = .fvar fv ∧ fv ∈ root.lctx.fvars
  type_eq :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive itIndices)
      (mkAppN field args)
    type = current.lctx.mkForall args motiveApp

/-- Forget that an origin was retained by the in-progress hypothesis loop;
the completed minor certificate has the same transparent payload. -/
def RecInfoHypothesisTypeOrigin.toMinor
    (O : RecInfoHypothesisTypeOrigin stats recInfos root field type) :
    RecInfoMinorHypothesisTypeOrigin stats recInfos root field type := {
  current := O.current
  current_wf := O.current_wf
  current_extends := O.current_extends
  exposedType := O.exposedType
  args := O.args
  arguments_bound := O.arguments_bound
  loopInput := O.loopInput
  loopTrace := O.loopTrace
  field_fvar := O.field_fvar
  ownerIdx := O.ownerIdx
  owner_valid := O.owner_valid
  motive_is_fvar := O.motive_is_fvar
  type_eq := O.type_eq }

/-- Pointwise source origins for the prefix of recursive fields already
processed by `loopU`.  Each installed declaration is tied to the unconsumed
type returned by the corresponding `loopUArgs` run. -/
structure RecInfoHypothesisTypeOrigins
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (fieldRoot c : AddInductive.Context)
    (fields hypotheses : Array Expr) where
  size_le : hypotheses.size ≤ fields.size
  entry : ∀ j (hj : j < hypotheses.size),
    ∃ root sourceType,
      BindingContextLE fieldRoot root ∧
      Nonempty (RecInfoHypothesisTypeOrigin
        stats recInfos root fields[j]! sourceType) ∧
      ∃ D : BoundFVarDeclarationAt c hypotheses j,
        D.type = sourceType.consumeTypeAnnotationsVerified

def RecInfoHypothesisTypeOrigins.empty
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) (fields : Array Expr) :
    RecInfoHypothesisTypeOrigins stats recInfos c c fields #[] where
  size_le := by simp
  entry := by intro j hj; simp at hj

def RecInfoHypothesisTypeOrigins.pushCurrent
    (H : RecInfoHypothesisTypeOrigins stats recInfos fieldRoot c
      fields hypotheses)
    (Hc : BindingContextWF c)
    (name : Name) (sourceType : Expr) (bi : BinderInfo)
    (hnext : hypotheses.size < fields.size)
    (Hroot : BindingContextLE fieldRoot root)
    (Horigin : Nonempty (RecInfoHypothesisTypeOrigin stats recInfos root
      fields[hypotheses.size]! sourceType)) :
    RecInfoHypothesisTypeOrigins stats recInfos fieldRoot
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          sourceType.consumeTypeAnnotationsVerified bi }
      fields (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) := by
  let ty := sourceType.consumeTypeAnnotationsVerified
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  refine {
    size_le := by simpa using Nat.succ_le_of_lt hnext
    entry := ?_ }
  intro j hj
  by_cases hilast : j = hypotheses.size
  · subst j
    let D : BoundFVarDeclarationAt c'
        (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) hypotheses.size := {
      inBounds := by simp
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    exact ⟨root, sourceType, Hroot, Horigin, D, rfl⟩
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases H.entry j hjOld with
      ⟨oldRoot, oldType, HoldRoot, Hold, D, htype⟩
    exact ⟨oldRoot, oldType, HoldRoot, Hold,
      (D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep, htype⟩

/-- The call-blueprint row produced beside a hypothesis prefix, indexed by
the same producer witnesses as `RecInfoHypothesisTypeOrigins`. -/
structure RecInfoHypothesisCallBlueprintOrigins
    (H : RecInfoHypothesisTypeOrigins stats recInfos fieldRoot c
      fields hypotheses)
    (calls : Array AddInductive.RecCallBlueprint) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (hj : j < hypotheses.size),
    ∃ root sourceType,
      ∃ (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root
        fields[j]! sourceType),
        ∃ (D : BoundFVarDeclarationAt c hypotheses j),
          BindingContextLE fieldRoot root ∧
          D.type = sourceType.consumeTypeAnnotationsVerified ∧
          calls[j]! = {
            major := fields[j]!
            args := O.args
            lctx := O.current.lctx
            targetTypeIdx := O.ownerIdx
            targetIndices := O.exposedType.getAppArgs[stats.params.size:]
            template := O.current.lctx.mkLambda O.args <|
              (mkAppN (.bvar 0)
                O.exposedType.getAppArgs[stats.params.size:]).app
                  (mkAppN fields[j]! O.args) }

theorem RecInfoHypothesisCallBlueprintOrigins.empty
    (H : RecInfoHypothesisTypeOrigins stats recInfos c c fields #[]) :
    RecInfoHypothesisCallBlueprintOrigins H #[] where
  size_eq := rfl
  entry j hj := by simp at hj

theorem RecInfoHypothesisCallBlueprintOrigins.pushCurrent
    {H : RecInfoHypothesisTypeOrigins stats recInfos fieldRoot c
      fields hypotheses}
    {calls : Array AddInductive.RecCallBlueprint}
    (Hcalls : RecInfoHypothesisCallBlueprintOrigins H calls)
    (Hc : BindingContextWF c)
    (name : Name) (sourceType : Expr) (bi : BinderInfo)
    (hnext : hypotheses.size < fields.size)
    (Hroot : BindingContextLE fieldRoot root)
    (O : RecInfoHypothesisTypeOrigin stats recInfos root
      fields[hypotheses.size]! sourceType)
    (call : AddInductive.RecCallBlueprint)
    (hcall : call = {
      major := fields[hypotheses.size]!
      args := O.args
      lctx := O.current.lctx
      targetTypeIdx := O.ownerIdx
      targetIndices := O.exposedType.getAppArgs[stats.params.size:]
      template := O.current.lctx.mkLambda O.args <|
        (mkAppN (.bvar 0)
          O.exposedType.getAppArgs[stats.params.size:]).app
            (mkAppN fields[hypotheses.size]! O.args) }) :
    RecInfoHypothesisCallBlueprintOrigins
      (H.pushCurrent Hc name sourceType bi hnext Hroot ⟨O⟩)
      (calls.push call) := by
  let ty := sourceType.consumeTypeAnnotationsVerified
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  refine {
    size_eq := by simpa using congrArg Nat.succ Hcalls.size_eq
    entry := ?_ }
  intro j hj
  by_cases hilast : j = hypotheses.size
  · subst j
    let D : BoundFVarDeclarationAt c'
        (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) hypotheses.size := {
      inBounds := by simp
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    refine ⟨root, sourceType, O.toMinor, D, Hroot, rfl, ?_⟩
    have hlast : (calls.push call)[hypotheses.size]! = call := by
      rw [show hypotheses.size = calls.size from Hcalls.size_eq.symm]
      simp
    rw [hlast, hcall]
    rfl
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases Hcalls.entry j hjOld with
      ⟨oldRoot, oldType, Oold, D, HoldRoot, htype, hcallOld⟩
    refine ⟨oldRoot, oldType, Oold,
      (D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep,
      HoldRoot, htype, ?_⟩
    have hjCalls : j < calls.size := by rw [Hcalls.size_eq]; exact hjOld
    have hpush : (calls.push call)[j]! = calls[j]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos (by simp; omega), dif_pos hjCalls]
      exact Array.getElem_push_lt hjCalls
    rw [hpush]
    exact hcallOld

/-- Close a semantically typed motive application over the exact
higher-order suffix traversed by `loopUArgs`.  This is the pointwise bridge
needed by the second `mkRecInfos` pass: the caller supplies only the typing of
the terminal motive application, while this theorem reconstructs and checks
the complete induction-hypothesis declaration domain returned by production,
while retaining its exact source construction.
-/
theorem mkRecInfos.loopUArgs.inductionHypothesisTypeOrigin
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    (Hmotives : BoundFVarArray c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorRecentBoundFVarArray R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv) (fun uiTy xs => do
      let some itIdx := AddInductive.isValidIndApp? stats uiTy
        | throw (.other
          "recursive constructor field lost its inductive result type")
      let itIndices := uiTy.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN (.fvar fv) xs)
      return (← getLCtx).mkForall xs motiveApp) c).WF fun viTy =>
        ∃ viTarget,
          TrExprS R.venv recLparams R.mlctx.vlctx
            viTy.consumeTypeAnnotationsVerified viTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
          Nonempty (RecInfoHypothesisTypeOrigin
            stats recInfos c (.fvar fv) viTy) := by
  let build : Expr → Array Expr → Nat → AddInductive.M Expr :=
    fun exposedType args target => do
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      return (← getLCtx).mkForall args motiveApp
  have hfvScope : fv ∈ R.mlctx.vlctx.fvars := by
    simpa only [FVarsIn] using hfield.fvarsIn
  have hfvRoot : fv ∈ c.lctx.fvars := by
    rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq]
    exact hfvScope
  have Hrun := mkRecInfos.loopUArgs.resultRecursiveDomain fv stats build c R
    Hstats hconsume hlit hctx hfield hfvScope
      (IsFVarUpSet.fvars (R.mlctx_wf.tr.wf).fvwf)
    (Q := fun _ viTy => ∃ viTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        viTy.consumeTypeAnnotationsVerified viTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
      Nonempty (RecInfoHypothesisTypeOrigin
        stats recInfos c (.fvar fv) viTy)) ?_
  · simpa only [build] using Hrun.mono (fun viTy Hout => by
      rcases Hout with ⟨_domain, _hfieldType, _target, _htarget,
        _hrecursive, Hvi⟩
      exact Hvi)
  · intro Hinput current Rcurrent exposedType syntaxTarget terminalTarget
      appliedTarget args target Htrace Hexposed Hdefeq Hterminal Hargs Happlied
      HappliedType hvalid _hexposedScope _hup
    rcases Happ Rcurrent Hexposed Hdefeq Hterminal Hargs Happlied
        HappliedType hvalid with ⟨motiveTarget, Hmotive, HmotiveType⟩
    have htargetStats : target < stats.indConsts.size :=
      (checkPositivityStep.isValidIndApp?_some hvalid).1
    have htarget : target < recInfos.size := by
      rw [hrecords]
      exact htargetStats
    rcases Hmotives.get_eq_fvar target
        (by simpa using htarget) with
      ⟨motiveFVar, hmotiveFVar, hmotiveMember⟩
    rcases Hargs.mkForall Hmotive HmotiveType with
      ⟨viTarget, Hvi, HviType⟩
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive itIndices)
      (mkAppN (.fvar fv) args)
    rcases hconsume c recLparams R Hvi HviType with
      ⟨consumedTarget, Hconsumed⟩
    change (Except.ok (current.lctx.mkForall args motiveApp)).WF _
    exact Except.WF.pure
      ⟨consumedTarget, Hconsumed.consumed, Hconsumed.isType, ⟨{
        current := current
        current_wf := Rcurrent.toBindingContextWF
        current_extends := Hargs.contextLE
        exposedType := exposedType
        args := args
        arguments_bound := Hargs.toFreshBoundFVarArray
        loopInput := Hinput
        loopTrace := Htrace
        field_fvar := ⟨fv, rfl, hfvRoot⟩
        ownerIdx := target
        owner_valid := hvalid
        motive_is_fvar := ⟨motiveFVar, by
          rw [getElem!_pos recInfos target htarget]
          simpa only [Array.getElem_map] using hmotiveFVar,
          hmotiveMember⟩
        type_eq := rfl }⟩⟩

/-- Semantic interface for the strengthened recursive-field terminal check.
The executable callback now validates the exposed result before projecting a
mutual-family index; this theorem turns that branch into the corresponding
targeted abstract application and retains the exact higher-order suffix. -/
theorem mkRecInfos.loopUArgs.resultValidatedIndApp {alpha : Type}
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Nat → AddInductive.M alpha)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    {Q : alpha → Prop}
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget typeTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget typeTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx typeTarget →
      (Hrecent : RecursorRecentBoundFVarArray R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget typeTarget →
      RecursorValidatedIndAppAt Rcurrent.venv recLparams
        Rcurrent.mlctx.vlctx stats decl (depth + args.size)
        exposedType syntaxTarget target →
      (k exposedType args target current).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv) (fun exposedType args => do
      let some target := AddInductive.isValidIndApp? stats exposedType
        | throw (.other
          "recursive constructor field lost its inductive result type")
      k exposedType args target) c).WF Q := by
  refine mkRecInfos.loopUArgs.resultSemantics fv
    (fun exposedType args => do
      let some target := AddInductive.isValidIndApp? stats exposedType
        | throw (.other
          "recursive constructor field lost its inductive result type")
      k exposedType args target)
    c R hconsume hfield ?_
  intro current Rcurrent exposedType typeTarget appliedTarget args htype
    htypeType Hrecent happlied happliedType
  rcases htype with ⟨syntaxTarget, hsyntax, hdefeq⟩
  cases hvalid : AddInductive.isValidIndApp? stats exposedType with
  | none =>
      simp only [hvalid, bind, Except.bind]
      exact Except.WF.throw
  | some target =>
      simp only [hvalid, bind, Except.bind]
      let HstatsCurrent := Hstats.weakenRecent Hrecent
      have htargetStats : target < stats.indConsts.size :=
        (checkPositivityStep.isValidIndApp?_some hvalid).1
      have htarget : target < decl.types.length := by
        rw [← HstatsCurrent.types_size]
        exact htargetStats
      have hctxCurrent : VLCtx.NoIndConsts
          (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
        Hrecent.noIndConsts hctx
      exact Hk Rcurrent hsyntax hdefeq htypeType Hrecent happlied happliedType
        (HstatsCurrent.validatedIndAppAt hsyntax hvalid htarget
          (by simpa only [Hrecent.venv_eq] using hlit) hctxCurrent)

/-- Exact recursive-call syntax together with the inner binding context used
to close its higher-order arguments. -/
structure BoundGeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (field value : Expr) where
  exposedType : Expr
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  localArgs : Array Expr
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  arguments_bound : FreshBoundFVarArray root current localArgs
  value_eq :
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
      minors
    value = (current.lctx.mkLambda localArgs <|
      (mkAppN (.bvar 0) indices).app
        (mkAppN field localArgs)).instantiate1 recursor

/-- Pre-installation semantics of one generated recursive call.  The
blueprint-producing pass installs hypotheses for earlier recursive fields,
so the higher-order argument telescope is recent relative to its exact
producer root.  The common constructor-field root remains separate. -/
structure SemanticBoundGeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (field value : Expr) where
  generated : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
    root field value
  current_context : RecursorContextWF generated.current recLparams
  recent : RecursorRecentBoundFVarArray R current_context
    generated.localArgs
  rootScope : FVarId → Prop
  /-- Exact source scope established by the successful recursive-field
  producer.  This is trace evidence, not a replay or caller premise. -/
  exposed_scope : generated.exposedType.FVarsIn
    (fun fv => fv ∈ recent.fvars ∨ rootScope fv)
  current_scope_up : IsFVarUpSet
    (fun fv => fv ∈ recent.fvars ∨ rootScope fv)
    current_context.mlctx.vlctx
  exposedTarget : VExpr
  exposed_translation : TrExprS current_context.venv recLparams
    current_context.mlctx.vlctx generated.exposedType exposedTarget
  terminalTarget : VExpr
  exposed_defeq : current_context.venv.IsDefEqU recLparams.length
    current_context.mlctx.vlctx.toCtx exposedTarget terminalTarget
  terminal_type : current_context.venv.IsType recLparams.length
    current_context.mlctx.vlctx.toCtx terminalTarget
  appliedFieldTarget : VExpr
  applied_field_translation : TrExprS current_context.venv recLparams
    current_context.mlctx.vlctx
    (mkAppN field generated.localArgs) appliedFieldTarget
  applied_field_typing : current_context.venv.HasType recLparams.length
    current_context.mlctx.vlctx.toCtx appliedFieldTarget terminalTarget
  /-- The exact validated inductive application produced at this call site. -/
  validated : RecursorValidatedIndAppAt current_context.venv recLparams
    current_context.mlctx.vlctx stats decl
    (depth + generated.localArgs.size) generated.exposedType exposedTarget
    generated.ownerIdx
  /-- The call-local telescope closed and restricted to the common
  constructor-field context.  In the blueprint-producing pass this removes
  the irrelevant hypotheses installed for earlier recursive fields. -/
  commonDomains : List VExpr
  commonDomains_length : commonDomains.length = generated.localArgs.size
  common_exposed_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (generated.current.lctx.mkForall generated.localArgs
      generated.exposedType)
    (VExpr.wrapForalls commonDomains exposedTarget)
  common_exposed_type : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapForalls commonDomains exposedTarget)
  common_applied_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (generated.current.lctx.mkLambda generated.localArgs
      (mkAppN field generated.localArgs))
    (VExpr.wrapLams commonDomains appliedFieldTarget)
  common_applied_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapLams commonDomains appliedFieldTarget)
    (VExpr.wrapForalls commonDomains exposedTarget)
  /-- Exact recursive-domain judgment retained from positivity.  These facts
  are produced by the successful field check and discharge source closedness
  obligations without replaying the checker. -/
  fieldTarget : VExpr
  domain : VExpr
  field_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    field fieldTarget
  field_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    fieldTarget domain
  owner_lt : generated.ownerIdx < decl.types.length
  recursive : decl.RecursiveArgAtTarget R.venv recLparams.length
    (decl.types[generated.ownerIdx]'owner_lt).name
    R.mlctx.vlctx.toCtx depth domain

/-- The exact higher-order argument suffix of a recursive constructor field,
closed back to the rule's field context.  The exposed result type and the
eta-expanded field use one shared domain list; this is the typed major premise
later supplied to the recursively selected generated recursor. -/
structure SemanticBoundGeneratedRecursiveCall.AppliedFieldTelescope
    {R : RecursorContextWF root recLparams}
    (S : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) where
  domains : List VExpr
  domains_length : domains.length = S.generated.localArgs.size
  exposed_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (S.generated.current.lctx.mkForall S.generated.localArgs
      S.generated.exposedType)
    (VExpr.wrapForalls domains S.exposedTarget)
  exposed_type : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapForalls domains S.exposedTarget)
  applied_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (S.generated.current.lctx.mkLambda S.generated.localArgs
      (mkAppN field S.generated.localArgs))
    (VExpr.wrapLams domains S.appliedFieldTarget)
  applied_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapLams domains S.appliedFieldTarget)
    (VExpr.wrapForalls domains S.exposedTarget)

/-- The recursive field syntax retained by the successful producer has no
ambient loose variables. -/
theorem SemanticBoundGeneratedRecursiveCall.fieldClosed
    {R : RecursorContextWF root recLparams}
    (S : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    field.looseBVarRange' = 0 := by
  have hclosed := S.field_translation.closed
  rw [R.mlctx.noBV] at hclosed
  exact hclosed.looseBVarRange_zero

/-- Recover the shared higher-order field telescope from the semantic facts
already established by `loopUArgs`.  The executable normalizer may expose a
definitionally equal terminal type, so it is transported back to the exact
syntax translation before the suffix is closed. -/
def SemanticBoundGeneratedRecursiveCall.appliedFieldTelescope
    {R : RecursorContextWF root recLparams}
    (S : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    S.AppliedFieldTelescope where
  domains := S.commonDomains
  domains_length := S.commonDomains_length
  exposed_translation := S.common_exposed_translation
  exposed_type := S.common_exposed_type
  applied_translation := S.common_applied_translation
  applied_typing := S.common_applied_typing

/-- The recursive-call callback shared by the executable rule loop and its
pointwise semantic interface.  Naming it prevents the match compiler from
leaking module-local matcher constants into the refinement theorem's public
type. -/
def mkRecRules.buildRecursiveCall
    (indTypes : Array InductiveType)
    (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) (field : Expr) :
    Expr → Array Expr → AddInductive.M Expr :=
  fun exposedType args => do
    let some target := AddInductive.isValidIndApp? stats exposedType
      | throw (.other
        "recursive constructor field lost its inductive result type")
    let indices := exposedType.getAppArgs[stats.params.size:]
    let recursor :=
      Expr.const (Lean.mkRecName indTypes[target]!.name) lvls
    let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
      minors
    let lctx ← getLCtx
    return (lctx.mkLambda args <|
      (mkAppN (.bvar 0) indices).app
        (mkAppN field args)).instantiate1 recursor

/-- Pointwise semantic refinement of the exact recursive-call builder used
by `mkRecRules.loopU`.  It couples the implementation's validated owner with
the complete higher-order recursive domain reconstructed by `loopUArgs`. -/
theorem mkRecRules.boundGeneratedCallSemantic
    (indTypes : Array InductiveType)
    (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (fv : FVarId) {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (hfieldScope : P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv)
      (mkRecRules.buildRecursiveCall indTypes stats motives minors lvls
        (.fvar fv)) root).WF fun value =>
        ∃ S : SemanticBoundGeneratedRecursiveCall indTypes stats motives
            minors lvls R decl depth (.fvar fv) value,
          S.rootScope = P := by
  unfold mkRecRules.buildRecursiveCall
  let buildCallAt : Expr → Array Expr → Nat → AddInductive.M Expr :=
    fun exposedType args target => do
      let indices := exposedType.getAppArgs[stats.params.size:]
      let recursor := Expr.const
        (Lean.mkRecName indTypes[target]!.name) lvls
      let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
        minors
      let lctx ← getLCtx
      return (lctx.mkLambda args <|
        (mkAppN (.bvar 0) indices).app
          (mkAppN (.fvar fv) args)).instantiate1 recursor
  have Hloop := mkRecInfos.loopUArgs.resultRecursiveDomain fv stats
    buildCallAt root R Hstats hconsume hlit hctx hfield
    hfieldScope hrootUp
    (Q := fun target value =>
      ∃ Hinput : RecursorLoopUArgsInput root (.fvar fv),
      ∃ H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
          root (.fvar fv) value,
        ∃ Htrace : RecursorLoopUArgsPrefix root Hinput.normalizedType
          H.current H.exposedType H.localArgs,
        H.ownerIdx = target ∧
        ∃ Rcurrent : RecursorContextWF H.current recLparams,
          ∃ Hrecent : RecursorRecentBoundFVarArray R Rcurrent H.localArgs,
            ∃ syntaxTarget terminalTarget appliedTarget,
              TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
                  H.exposedType syntaxTarget ∧
                Rcurrent.venv.IsDefEqU recLparams.length
                  Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget ∧
                Rcurrent.venv.IsType recLparams.length
                  Rcurrent.mlctx.vlctx.toCtx terminalTarget ∧
                TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
                  (mkAppN (.fvar fv) H.localArgs) appliedTarget ∧
                Rcurrent.venv.HasType recLparams.length
                  Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget ∧
                H.exposedType.FVarsIn
                  (fun fv => fv ∈ Hrecent.fvars ∨ P fv) ∧
                IsFVarUpSet (fun fv => fv ∈ Hrecent.fvars ∨ P fv)
                  Rcurrent.mlctx.vlctx ∧
                RecursorValidatedIndAppAt Rcurrent.venv recLparams
                  Rcurrent.mlctx.vlctx stats decl
                  (depth + H.localArgs.size) H.exposedType syntaxTarget
                  H.ownerIdx)
    (by
      intro Hinput current Rcurrent exposedType syntaxTarget terminalTarget
        appliedTarget args target Htrace hsyntax hdefeq htype Hrecent happlied
        happliedType hvalid hexposedScope hcurrentUp
      change (Except.ok
        ((current.lctx.mkLambda args <|
          (mkAppN (.bvar 0)
            exposedType.getAppArgs[stats.params.size:]).app
              (mkAppN (.fvar fv) args)).instantiate1
                (mkAppN (mkAppN (mkAppN
                  (Expr.const (Lean.mkRecName indTypes[target]!.name) lvls)
                  stats.params) motives) minors))).WF _
      let Hgenerated : BoundGeneratedRecursiveCall indTypes stats motives
          minors lvls root (.fvar fv)
          ((current.lctx.mkLambda args <|
            (mkAppN (.bvar 0)
              exposedType.getAppArgs[stats.params.size:]).app
                (mkAppN (.fvar fv) args)).instantiate1
                  (mkAppN (mkAppN (mkAppN
                    (Expr.const (Lean.mkRecName indTypes[target]!.name) lvls)
                    stats.params) motives) minors)) := {
        exposedType := exposedType
        ownerIdx := target
        owner_valid := hvalid
        localArgs := args
        current := current
        current_wf := Rcurrent.toBindingContextWF
        current_extends := Hrecent.contextLE
        arguments_bound := Hrecent.toFreshBoundFVarArray
        value_eq := by simp [AddInductive.getIIndices, hvalid] }
      let HstatsCurrent := Hstats.weakenRecent Hrecent
      have htargetStats : target < stats.indConsts.size :=
        (checkPositivityStep.isValidIndApp?_some hvalid).1
      have htargetDecl : target < decl.types.length := by
        rw [← HstatsCurrent.types_size]
        exact htargetStats
      have hctxCurrent : VLCtx.NoIndConsts
          (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
        Hrecent.noIndConsts (names := decl.types.map (·.name)) hctx
      let Hvalidated := HstatsCurrent.validatedIndAppAt hsyntax hvalid
        htargetDecl (by simpa only [Hrecent.venv_eq] using hlit)
        hctxCurrent
      exact Except.WF.pure
        ⟨Hinput, Hgenerated, Htrace, rfl, Rcurrent, Hrecent, syntaxTarget,
          terminalTarget,
          appliedTarget, hsyntax, hdefeq, htype, happlied, happliedType,
          hexposedScope, hcurrentUp, Hvalidated⟩)
  exact Hloop.mono fun value Hout => by
    rcases Hout with
      ⟨domain, hfieldTyping, target, htarget, hrecursive,
        Hinput, Hgenerated, Htrace, howner, Rcurrent, Hrecent, syntaxTarget,
        terminalTarget,
        appliedTarget, hsyntax, hdefeq, htype, happlied, happliedType,
        hexposedScope, hcurrentUp, Hvalidated⟩
    subst target
    have HexposedType : Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget :=
      VEnv.IsType.defeqU_l Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx hdefeq.symm htype
    have HappliedType : Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget syntaxTarget :=
      happliedType.defeqU_r Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx hdefeq.symm
    let commonDomains := MLCtxForallDomains Rcurrent.mlctx
      Hgenerated.localArgs.size Hrecent.size_le
    have HexposedClosed := Hrecent.mkForallExact hsyntax HexposedType
    have HappliedClosed := Hrecent.mkLambda happlied HappliedType
    exact ⟨{
      generated := Hgenerated
      current_context := Rcurrent
      recent := Hrecent
      rootScope := P
      exposed_scope := hexposedScope
      current_scope_up := hcurrentUp
      exposedTarget := syntaxTarget
      exposed_translation := hsyntax
      terminalTarget := terminalTarget
      exposed_defeq := hdefeq
      terminal_type := htype
      appliedFieldTarget := appliedTarget
      applied_field_translation := happlied
      applied_field_typing := happliedType
      validated := Hvalidated
      commonDomains := commonDomains
      commonDomains_length :=
        Rcurrent.onlyLams.forallDomains_length
          Hgenerated.localArgs.size Hrecent.size_le
      common_exposed_translation := by
        simpa [commonDomains] using HexposedClosed.1
      common_exposed_type := by
        simpa [commonDomains] using HexposedClosed.2
      common_applied_translation := by
        simpa [commonDomains] using HappliedClosed.1
      common_applied_typing := by
        simpa [commonDomains] using HappliedClosed.2
      fieldTarget := fieldTarget
      domain := domain
      field_translation := hfield
      field_typing := hfieldTyping
      owner_lt := htarget
      recursive := hrecursive
      }, rfl⟩

theorem BoundGeneratedRecursiveCall.generated
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    checkPositivityStep.GeneratedRecursiveCall
      indTypes stats motives minors lvls field value := by
  exact ⟨H.exposedType, H.localArgs, H.current.lctx, H.value_eq⟩

def BoundGeneratedRecursiveCall.body
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let (typeIdx, indices) := AddInductive.getIIndices stats H.exposedType
  let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
  let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
    minors
  let templateBody := (mkAppN (.bvar 0) indices).app
    (mkAppN field H.localArgs)
  (templateBody.abstractList H.arguments_bound.fvars).instantiate1'
    recursor H.localArgs.size

theorem BoundGeneratedRecursiveCall.value_eq_body
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    value = (H.current.lctx.mkLambda H.localArgs <|
      let indices := (AddInductive.getIIndices stats H.exposedType).2
      (mkAppN (.bvar 0) indices).app
        (mkAppN field H.localArgs)).instantiate1
          (mkAppN (mkAppN (mkAppN
            (.const (Lean.mkRecName
              indTypes[(AddInductive.getIIndices stats H.exposedType).1]!.name)
              lvls) stats.params) motives) minors) := by
  simpa using H.value_eq

/-- The exact lambda telescope closed by one generated recursive call. -/
theorem BoundGeneratedRecursiveCall.lambdaTelescope
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    Expr.LambdaTelescope value H.localArgs.size
      H.body := by
  rcases H with
    ⟨exposedType, ownerIdx, howner, localArgs, current, Hwf, Hle, Hargs,
      Hvalue⟩
  let templateBody : Expr :=
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    (mkAppN (.bvar 0) indices).app (mkAppN field localArgs)
  let recursor : Expr :=
    let (typeIdx, _) := AddInductive.getIIndices stats exposedType
    mkAppN (mkAppN (mkAppN
      (.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls) stats.params)
      motives) minors
  have Hvalue' : value =
      (current.lctx.mkLambda localArgs templateBody).instantiate1 recursor := by
    simpa [templateBody, recursor] using Hvalue
  change Expr.LambdaTelescope value localArgs.size
    ((templateBody.abstractList Hargs.fvars).instantiate1'
      recursor localArgs.size)
  rw [Hvalue']
  let Hselection :=
    Hargs.toBoundFVarArray.toLocalForallSelection Hwf
  have Hfvars : Hselection.fvars = Hargs.fvars := rfl
  rcases Hselection with ⟨fvars, rfl, Hdecl⟩
  rw [← Hfvars]
  have Htemplate := LocalContext.mkLambda_fvars_lambdaTelescope
    (body := templateBody) Hdecl
  simpa using Htemplate.instantiate1 recursor

/-- The successful semantic producer proves that the eta-expanded field is
closed with respect to loose variables.  Instantiating the retained outer
recursor placeholder therefore changes only the call template, while
preserving its concrete higher-order lambda prefix. -/
theorem SemanticBoundGeneratedRecursiveCall.sameAppliedFieldLambdaPrefix
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    Expr.SameLambdaPrefix H.generated.localArgs.size value
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)) := by
  let Hselection :=
    H.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      H.generated.current_wf
  let templateBody : Expr :=
    let indices :=
      (AddInductive.getIIndices stats H.generated.exposedType).2
    (mkAppN (.bvar 0) indices).app
      (mkAppN field H.generated.localArgs)
  let applied := H.generated.current.lctx.mkLambda H.generated.localArgs
    (mkAppN field H.generated.localArgs)
  have Hsame : Expr.SameLambdaPrefix H.generated.localArgs.size
      (H.generated.current.lctx.mkLambda H.generated.localArgs templateBody)
      applied :=
    Hselection.sameLambdaPrefix H.generated.arguments_bound.nodup
      templateBody (mkAppN field H.generated.localArgs)
  let recursor := mkAppN (mkAppN (mkAppN
    (.const (Lean.mkRecName
      indTypes[(AddInductive.getIIndices stats H.generated.exposedType).1]!.name)
      lvls) stats.params) motives) minors
  have Hsame' := Hsame.instantiate1 recursor
  have happliedClosed : Closed applied := by
    have hclosed := H.appliedFieldTelescope.applied_translation.closed
    simpa [applied, R.mlctx.noBV] using hclosed
  have happliedInst : applied.instantiate1 recursor = applied :=
    by simpa [Expr.instantiate1_eq] using
      (Expr.instantiate1_eq_self
        (a := recursor) happliedClosed.looseBVarRange_zero)
  rw [happliedInst] at Hsame'
  have Hsame'' : Expr.SameLambdaPrefix H.generated.localArgs.size
      ((H.generated.current.lctx.mkLambda H.generated.localArgs <|
        let indices :=
          (AddInductive.getIIndices stats H.generated.exposedType).2
        (mkAppN (.bvar 0) indices).app
          (mkAppN field H.generated.localArgs)).instantiate1 recursor)
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)) := by
    simpa [templateBody, recursor, applied] using Hsame'
  exact Eq.mp (congrArg
    (fun source => Expr.SameLambdaPrefix H.generated.localArgs.size source
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)))
    H.generated.value_eq_body).symm Hsame''

/-- The higher-order lambda domains of a semantically retained generated
call predate the generated recursors.  Closing the surrounding rule binders
therefore yields a source telescope whose domains avoid every fresh recursor
name, while imposing no such condition on the call body. -/
theorem SemanticBoundGeneratedRecursiveCall.outerAvoidingLambdaTelescope
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value)
    (hfresh : ∀ name ∈ names, R.venv.constants name = none)
    (binders : List FVarId) :
    Expr.AvoidingLambdaTelescope names
      (value.abstractList binders) H.generated.localArgs.size
      (H.generated.body.abstractList binders H.generated.localArgs.size) := by
  have hcurrentFresh : ∀ name ∈ names,
      H.current_context.venv.constants name = none := by
    intro name hname
    rw [H.recent.venv_eq]
    exact hfresh name hname
  let Hselection :=
    H.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      H.generated.current_wf
  have hdecl : ∀ fv ∈ H.generated.arguments_bound.fvars,
      ∃ index name type bi kind,
        H.generated.current.lctx.find? fv =
          some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    exact Hselection.declarations fv hfv
  have Htel : Expr.AvoidingLambdaTelescope names
      (H.generated.current.lctx.mkLambda
        (H.generated.arguments_bound.fvars.map Expr.fvar).toArray
        (mkAppN field
          (H.generated.arguments_bound.fvars.map Expr.fvar).toArray))
      H.generated.arguments_bound.fvars.length
      ((mkAppN field
        (H.generated.arguments_bound.fvars.map Expr.fvar).toArray).abstractList
          H.generated.arguments_bound.fvars) :=
    LocalContext.mkLambda_fvars_avoidingLambdaTelescope hdecl
      (fun fv index userName type bi kind hfv hfind =>
        checkPositivityStep.RecursorContextWF.cdeclTypeAvoids
          H.current_context hcurrentFresh hfind)
  have hlocalSize : H.generated.localArgs.size =
      H.generated.arguments_bound.fvars.length := by
    have := congrArg Array.size H.generated.arguments_bound.expressions
    simpa using this
  have Htel' : Expr.AvoidingLambdaTelescope names value
      H.generated.localArgs.size H.generated.body := by
    have HtelEta : Expr.AvoidingLambdaTelescope names
        (H.generated.current.lctx.mkLambda H.generated.localArgs
          (mkAppN field H.generated.localArgs))
        H.generated.localArgs.size
        ((mkAppN field H.generated.localArgs).abstractList
          H.generated.arguments_bound.fvars) := by
      simpa [H.generated.arguments_bound.expressions, hlocalSize] using Htel
    exact H.sameAppliedFieldLambdaPrefix.symm.avoidingLambdaTelescope
      HtelEta H.generated.lambdaTelescope
  simpa using Htel'.abstractList binders

/-- Translating a bound generated call exposes the exact abstract lambda
domains and the translation of its simultaneously abstracted call body. -/
theorem BoundGeneratedRecursiveCall.translatedLambdaShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        H.body residual := by
  exact TrExprS.lambdaTelescope_shape_with_context H.lambdaTelescope Htr

/-- Closing a generated call over an additional rule-level binder list
preserves its higher-order lambda arity. The residual records the necessary
binder-depth shift explicitly, avoiding any assumption that translation and
simultaneous abstraction commute definitionally. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedLambdaTelescope
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) :
    Expr.LambdaTelescope (value.abstractList binders)
      H.localArgs.size
      (H.body.abstractList binders H.localArgs.size) := by
  simpa using H.lambdaTelescope.abstractList binders

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedLambdaShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.body.abstractList binders H.localArgs.size) residual := by
  exact TrExprS.lambdaTelescope_shape_with_context
    (H.outerAbstractedLambdaTelescope binders) Htr

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedLambdaShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.body.abstractList binders H.localArgs.size) residual ∧
      ∀ dom ∈ domains, dom.SourceConstFree recursors := by
  exact TrExprS.lambdaTelescope_shape_with_context_noFresh
    hfresh hctx (H.outerAbstractedLambdaTelescope binders) Htr

/-- Simultaneous abstraction preserves the generated recursor spine and
turns the freshly opened local arguments into the canonical de Bruijn spine
on the recursive field. -/
theorem BoundGeneratedRecursiveCall.abstractedBody_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    let (typeIdx, indices) :=
      AddInductive.getIIndices stats H.exposedType
    let recursor := mkAppN (mkAppN (mkAppN
      (.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls)
      stats.params) motives) minors
    let abstractedFn :=
      mkAppN ((Expr.bvar 0).abstractList H.arguments_bound.fvars)
        (indices.map fun e => e.abstractList H.arguments_bound.fvars)
    let abstractedMajor :=
      mkAppN (field.abstractList H.arguments_bound.fvars)
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
    H.body =
      (abstractedFn.instantiate1' recursor H.localArgs.size).app
        (abstractedMajor.instantiate1' recursor H.localArgs.size) := by
  rcases hindices : AddInductive.getIIndices stats H.exposedType with
    ⟨typeIdx, indices⟩
  have hlocal :
      H.localArgs.map (fun e =>
        e.abstractList H.arguments_bound.fvars) =
      (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      H.localArgs.map (fun e =>
          e.abstractList H.arguments_bound.fvars) =
          ((H.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList H.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList H.arguments_bound.fvars)
            H.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          H.arguments_bound.fvars 0 H.arguments_bound.nodup
  simp only [BoundGeneratedRecursiveCall.body, hindices,
    Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]
  rfl

def BoundGeneratedRecursiveCall.recursorName
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Name :=
  Lean.mkRecName indTypes[(AddInductive.getIIndices stats H.exposedType).1]!.name

/-- The owner retained at the successful validation branch is exactly the
family index consumed by the partial production helper. -/
theorem BoundGeneratedRecursiveCall.recursorName_eq_owner
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.recursorName = Lean.mkRecName indTypes[H.ownerIdx]!.name := by
  simp only [BoundGeneratedRecursiveCall.recursorName,
    checkPositivityStep.getIIndices.fst_eq_of_valid H.owner_valid]

def BoundGeneratedRecursiveCall.abstractedRecursor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let indices := (AddInductive.getIIndices stats H.exposedType).2
  let recursor := mkAppN (mkAppN (mkAppN
    (.const H.recursorName lvls) stats.params) motives) minors
  (mkAppN ((Expr.bvar 0).abstractList H.arguments_bound.fvars)
    (indices.map fun e => e.abstractList H.arguments_bound.fvars)).instantiate1'
      recursor H.localArgs.size

def BoundGeneratedRecursiveCall.abstractedMajor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let recursor := mkAppN (mkAppN (mkAppN
    (.const H.recursorName lvls) stats.params) motives) minors
  (mkAppN (field.abstractList H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray).instantiate1'
        recursor H.localArgs.size

def BoundGeneratedRecursiveCall.outerAbstractedRecursor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedRecursor.abstractList binders H.localArgs.size

def BoundGeneratedRecursiveCall.outerAbstractedMajor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedMajor.abstractList binders H.localArgs.size

/-- The eta-expanded recursive field used as the generated recursor's major
premise closes over the same exact fresh higher-order arguments as the call
itself.  Its residual is `abstractedMajor`, rather than the complete call
body retained by `lambdaTelescope`. -/
theorem BoundGeneratedRecursiveCall.appliedFieldLambdaTelescope
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldClosed : field.looseBVarRange' = 0) :
    Expr.LambdaTelescope
      (H.current.lctx.mkLambda H.localArgs (mkAppN field H.localArgs))
      H.localArgs.size H.abstractedMajor := by
  let Hselection :=
    H.arguments_bound.toBoundFVarArray.toLocalForallSelection H.current_wf
  have Hdecl := Hselection.declarations
  have HselectionFvars : Hselection.fvars =
      H.arguments_bound.fvars := rfl
  rw [HselectionFvars] at Hdecl
  have Hexpressions := H.arguments_bound.expressions
  rw [Hexpressions]
  have Htel := LocalContext.mkLambda_fvars_lambdaTelescope
    (body := mkAppN field
      (H.arguments_bound.fvars.map Expr.fvar).toArray) Hdecl
  have hlocal :
      (H.arguments_bound.fvars.map Expr.fvar).toArray.map (fun e =>
        e.abstractList H.arguments_bound.fvars) =
      (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar
          (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    simpa using Expr.abstractList_fvarArray
      H.arguments_bound.fvars 0 H.arguments_bound.nodup
  have hsize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  let major := mkAppN (field.abstractList H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
  have hfieldRange :
      (field.abstractList H.arguments_bound.fvars).looseBVarRange' ≤
        H.arguments_bound.fvars.length := by
    have Hrange := Expr.abstractList_looseBVarRange_le
      (e := field) (fvs := H.arguments_bound.fvars) (k := 0)
    simpa [hfieldClosed] using Hrange
  have hmajorRange : major.looseBVarRange' ≤
      H.arguments_bound.fvars.length := by
    apply Expr.mkAppN_looseBVarRange_le hfieldRange
    intro arg harg
    rcases Array.mem_iff_getElem.mp harg with ⟨i, hi, rfl⟩
    have hi' : i < H.arguments_bound.fvars.length := by simpa using hi
    simp only [List.getElem_toArray, List.getElem_ofFn,
      Lean.Expr.looseBVarRange']
    omega
  have hmajorInst : major.instantiate1'
      (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
        stats.params) motives) minors) H.localArgs.size = major := by
    apply Expr.instantiate1'_eq_self
    rw [hsize]
    exact hmajorRange
  have habstractedMajor : H.abstractedMajor = major := by
    change major.instantiate1'
      (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
        stats.params) motives) minors) H.localArgs.size = major
    exact hmajorInst
  rw [habstractedMajor]
  simpa [Expr.abstractList_mkAppN, hlocal, major] using Htel

/-- When the producer field expression is closed, the exact instantiated
template major reduces to the ordinary eta-expanded field residual. -/
theorem BoundGeneratedRecursiveCall.abstractedMajor_eq_of_closed
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldClosed : field.looseBVarRange' = 0) :
    H.abstractedMajor =
      mkAppN (field.abstractList H.arguments_bound.fvars)
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray := by
  let major := mkAppN (field.abstractList H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
  change major.instantiate1'
    (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
      stats.params) motives) minors) H.localArgs.size = major
  apply Expr.instantiate1'_eq_self
  have hsize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  rw [hsize]
  apply Expr.mkAppN_looseBVarRange_le
  · have Hrange := Expr.abstractList_looseBVarRange_le
      (e := field) (fvs := H.arguments_bound.fvars) (k := 0)
    simpa [hfieldClosed] using Hrange
  · intro arg harg
    rcases Array.mem_iff_getElem.mp harg with ⟨i, hi, rfl⟩
    have hi' : i < H.arguments_bound.fvars.length := by simpa using hi
    simp only [List.getElem_toArray, List.getElem_ofFn,
      Lean.Expr.looseBVarRange']
    omega

/-- Closing the shared higher-order prefix over the surrounding rule binders
preserves its literal equality. -/
theorem SemanticBoundGeneratedRecursiveCall.sameOuterAppliedFieldLambdaPrefix
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) (binders : List FVarId) :
    Expr.SameLambdaPrefix H.generated.localArgs.size
      (value.abstractList binders)
      ((H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)).abstractList binders) := by
  exact H.sameAppliedFieldLambdaPrefix.abstractList binders

/-- A root free variable is untouched by the fresh call-local binders.
Abstracting it over the surrounding rule telescope below those locals is
therefore exactly weakening its ordinary rule abstraction. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedFVar_eq_lift_of_fresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfresh : fv ∉ H.arguments_bound.fvars)
    (hbinders : binders.Nodup) (hfv : fv ∈ binders) :
    ((Expr.fvar fv).abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      ((Expr.fvar fv).abstractList binders).liftLooseBVars'
        0 H.localArgs.size := by
  rw [Expr.abstractList_fvar_of_not_mem hfresh]
  simpa using Expr.abstractList_add_eq_liftLooseBVars
    (e := .fvar fv) (fvars := binders) (depth := 0)
    (extra := H.localArgs.size) (by trivial) hbinders

theorem BoundGeneratedRecursiveCall.outerAbstractedRootFVar_eq_lift
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hroot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hfv : fv ∈ binders) :
    ((Expr.fvar fv).abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      ((Expr.fvar fv).abstractList binders).liftLooseBVars'
        0 H.localArgs.size := by
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hroot
  exact H.outerAbstractedFVar_eq_lift_of_fresh hfresh hbinders hfv

/-- Array form for binders retained in a context other than the call root.
The producer supplies exact disjointness from temporary call-local arguments. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedBoundArray_eq_lift_of_fresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (B : BoundFVarArray c xs)
    (hfresh : ∀ fv ∈ B.fvars, fv ∉ H.arguments_bound.fvars)
    (hbinders : binders.Nodup)
    (hselected : ∀ fv ∈ B.fvars, fv ∈ binders) :
    xs.map (fun arg =>
        (arg.abstractList H.arguments_bound.fvars).abstractList
          binders H.localArgs.size) =
      xs.map (fun arg =>
        (arg.abstractList binders).liftLooseBVars' 0 H.localArgs.size) := by
  apply Array.ext
  · simp
  · intro j hleft hright
    have hj : j < xs.size := by simpa using hleft
    rcases B.getElem_eq_fvar j hj with ⟨hjFvars, harg⟩
    simp only [Array.getElem_map]
    rw [harg]
    exact H.outerAbstractedFVar_eq_lift_of_fresh
      (hfresh B.fvars[j] (List.getElem_mem hjFvars)) hbinders
      (hselected B.fvars[j] (List.getElem_mem hjFvars))

/-- Pointwise array form of `outerAbstractedRootFVar_eq_lift`.  It applies
to the retained parameter, motive, and minor arrays used by generated
recursive calls. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedBoundArray_eq_lift
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (B : BoundFVarArray root xs)
    (hbinders : binders.Nodup)
    (hselected : ∀ fv ∈ B.fvars, fv ∈ binders) :
    xs.map (fun arg =>
        (arg.abstractList H.arguments_bound.fvars).abstractList
          binders H.localArgs.size) =
      xs.map (fun arg =>
        (arg.abstractList binders).liftLooseBVars' 0 H.localArgs.size) := by
  apply Array.ext
  · simp
  · intro j hleft hright
    have hj : j < xs.size := by simpa using hleft
    rcases B.getElem_eq_fvar j hj with ⟨hjFvars, harg⟩
    simp only [Array.getElem_map]
    rw [harg]
    exact H.outerAbstractedRootFVar_eq_lift
      (B.members B.fvars[j] (List.getElem_mem hjFvars)) hbinders
      (hselected B.fvars[j] (List.getElem_mem hjFvars))

def BoundGeneratedRecursiveCall.localIndices
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : List Nat :=
  List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
    H.arguments_bound.fvars.length - 1 - i

/-- Alpha-normalized payload of the recursive-result `loopUArgs` run.  It is
the second-pass counterpart of
`RecInfoMinorHypothesisTypeOrigin.replayTrace`. -/
def BoundGeneratedRecursiveCall.replayTrace
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId) : RecursorLoopUArgsTrace where
  ownerIdx := H.ownerIdx
  localArity := H.localArgs.size
  localTelescope :=
    (H.current.lctx.mkForall H.localArgs (.sort .zero)).abstractList
      fieldBinders
  motive :=
    (motives[H.ownerIdx]!.abstractList
      H.arguments_bound.fvars).abstractList fieldBinders H.localArgs.size
  indices :=
    ((H.exposedType.getAppArgs[stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList H.arguments_bound.fvars).abstractList
          fieldBinders H.localArgs.size)

/-- The second-pass counterpart of
`RecInfoMinorHypothesisTypeOrigin.outerAbstractedMotiveApp`. -/
def BoundGeneratedRecursiveCall.outerAbstractedMotiveApp
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId) : Expr :=
  Expr.app
    (mkAppN (H.replayTrace fieldBinders).motive
      (H.replayTrace fieldBinders).indices)
    (H.outerAbstractedMajor fieldBinders)

theorem BoundGeneratedRecursiveCall.outerAbstractedMotiveApp_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId)
    (hfieldClosed : field.looseBVarRange' = 0) :
    let indices : Array Expr :=
      H.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN motives[H.ownerIdx]! indices)
      (mkAppN field H.localArgs)
    (motiveApp.abstractList H.arguments_bound.fvars).abstractList
        fieldBinders H.localArgs.size =
      H.outerAbstractedMotiveApp fieldBinders := by
  dsimp only
  have hlocal :
      H.localArgs.map (fun e =>
        e.abstractList H.arguments_bound.fvars) =
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar
            (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      H.localArgs.map (fun e =>
          e.abstractList H.arguments_bound.fvars) =
          ((H.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList H.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList H.arguments_bound.fvars)
            H.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          H.arguments_bound.fvars 0 H.arguments_bound.nodup
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]
  unfold BoundGeneratedRecursiveCall.outerAbstractedMotiveApp
  unfold BoundGeneratedRecursiveCall.outerAbstractedMajor
  rw [H.abstractedMajor_eq_of_closed hfieldClosed]
  rw [Expr.abstractList_mkAppN]
  simp [BoundGeneratedRecursiveCall.outerAbstractedMotiveApp,
    BoundGeneratedRecursiveCall.replayTrace,
    BoundGeneratedRecursiveCall.outerAbstractedMajor,
    Array.map_map, Function.comp_def]


end VerifyInductive
end Lean4Lean
