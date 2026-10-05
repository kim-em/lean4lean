import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldChoice
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem TrExprS.dropFVarPrefix_typed
    (henv : env.WF) (hscope : (added ++ suffix).WF env Us.length)
    (hnoBV : (added ++ suffix).NoBV)
    (H : TrExprS env Us (added ++ suffix) source target)
    (Htype : env.IsType Us.length (added ++ suffix).toCtx target)
    (hfvars : FVarsIn (· ∈ suffix.fvars) source) :
    ∃ target', TrExprS env Us suffix source target' ∧ env.IsType Us.length suffix.toCtx target' := by
  obtain ⟨target', Hnew⟩ := TrExprS.dropFVarPrefix henv hscope hnoBV H hfvars
  let W := (VLCtx.FVLift.to_append suffix (VLCtx.NoBV.leftOfAppend added suffix hnoBV)).toFVLift'
  have Hweak := Hnew.weakFV' henv.ordered W hscope
  have Heq := Hweak.uniq henv (.refl henv hscope) H
  obtain ⟨level, HweakType⟩ := Htype.defeqU_l henv hscope.toCtx Heq.symm
  exact ⟨target', Hnew, level,
    (VEnv.HasType.weak'_iff henv hscope.toCtx W.toCtx).1 HweakType⟩

theorem RecInfoMinorSemanticSource.constructorSourceFVars
    {root : AddInductive.Context} {Rroot : RecursorContextWF root recLparams}
    {S : RecInfoMinorTypeShape} (HS : RecInfoMinorSemanticSource Rroot S) :
    (HS.traversal.terminalContext.lctx.mkForall S.fields HS.traversal.terminal).FVarsIn
      (· ∈ HS.parameterSuffix.parameterDecls.fvars) := by
  rw [← HS.terminalWF.lctx_eq,
    HS.terminalWF.mlctx_wf.mkForall_eq S.fields.size HS.fieldsRecent.size_le HS.fieldsRecent.reverse_eq
      (by simpa [TypeChecker.MLCtx.noBV] using HS.terminalTranslation.closed)]
  have Hup : IsFVarUpSet
      (fun fv => fv ∈ HS.terminalWF.mlctx.fvarRevList S.fields.size HS.fieldsRecent.size_le ∨
        fv ∈ ExprArrayFVarIds HS.traversal.stats.params) HS.terminalWF.mlctx.vlctx := by
    simpa [HS.fieldsRecent.fvarRevList_eq] using HS.fieldParameterUp
  have Hbody := HS.fieldOpening.currentFVarsIn HS.parameterScope
  have hfields := HS.fieldOpening.fvars_eq_bound HS.fieldsRecent.toBoundFVarArray
  rw [hfields, HS.parameterSuffix.parameterDecls_fvars] at Hbody
  have Hfv := HS.terminalWF.onlyLams.mkForall_fvarsIn_upset HS.terminalWF.mlctx_wf
    S.fields.size HS.fieldsRecent.size_le HS.traversal.terminal Hup (by
      simpa [HS.fieldsRecent.fvarRevList_eq] using Hbody)
  simpa [HS.parameterSuffix.parameterDecls_fvars] using Hfv

theorem RecInfoMinorSemanticSource.constructorTranslationAtSuffix
    {root : AddInductive.Context} {Rroot : RecursorContextWF root recLparams}
    {S : RecInfoMinorTypeShape} (HS : RecInfoMinorSemanticSource Rroot S) :
    ∃ target, TrExprS HS.rootWF.venv recLparams HS.parameterSuffix.parameterDecls
      (HS.traversal.terminalContext.lctx.mkForall S.fields HS.traversal.terminal) target ∧
      HS.rootWF.venv.IsType recLparams.length HS.parameterSuffix.parameterDecls.toCtx target := by
  obtain ⟨Htr, Htype⟩ := HS.fieldsRecent.mkForallExact HS.terminalTranslation HS.terminalType
  rw [HS.parameterSuffix.context] at Htr Htype
  have Hwf : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).WF
      HS.rootWF.venv recLparams.length := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx_wf.tr.wf
  have HnoBV : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).NoBV := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx.noBV
  exact TrExprS.dropFVarPrefix_typed HS.rootWF.checking.tr.wf Hwf HnoBV Htr Htype HS.constructorSourceFVars

/-- Retarget a complete source telescope to a separately selected strict
translation of the same domain prefix, transporting the residual by typed
context equality. The new residual is chosen only after the domains are fixed. -/
theorem TrExprS.retargetForallPrefix
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (Htel : Expr.ForallTelescope source n residual)
    (hdomains : domains.length = n)
    (Hfull : TrExprS env Us Δ source target)
    (Htype : env.IsType Us.length Δ.toCtx target)
    (Htemplate : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls domains (.sort .zero))) :
    ∃ result,
      TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) ∧
      TrExprS env Us (abstractForallContext domains Δ) residual result ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx result ∧
      env.IsDefEqU Us.length Δ.toCtx target (VExpr.wrapForalls domains result) := by
  obtain ⟨oldDomains, oldResult, hlen, heq, _⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Hfull
  subst target
  have Hprefix := (TrExprS.forallDomainsOnly Htel hlen Hfull).1
  have Hcontexts := TrExprS.forallPrefixContextEq henv Htel.domainsOnly hlen hdomains
    Hprefix Htemplate (.refl henv hΔ)
  obtain ⟨Hres, HresType⟩ := TrExprS.forallTelescope_residual_typed henv Htel hlen Hfull Htype
  obtain ⟨result, HnewRes⟩ := Hres.defeqDFC henv Hcontexts
  have HresEq := Hres.uniq henv Hcontexts HnewRes
  have HnewType := (HresType.defeqU_l henv Hcontexts.wf.toCtx HresEq).defeqDFC
    henv.ordered Hcontexts.defeqCtx
  obtain ⟨Hnew, HnewFullType⟩ := TrExprS.rebuildForallPrefix Htel hdomains Htemplate HnewRes HnewType
  exact ⟨result, Hnew, HnewFullType, HnewRes, HnewType,
    Hfull.uniq henv (.refl henv hΔ) Hnew⟩

theorem CompletedRecursorConstruction.constructorSourceUniverses
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars).levelParamsIn
      c.lparams = true := by
  obtain ⟨traversal, htraversal, _, _, _, Htr⟩ :=
    H.minorSourceReplay owner howner (by rwa [← H.sourceFamilyCount]) localIndex hlocal
      (H.sourceMinorOffsetBound owner howner localIndex hlocal)
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at Htr
  have Hsupport := HS.semantic.traversal.decisions.levelParamsIn
    HS.semantic.rootWF.toBindingContextWF Htr.levelParamsIn
  have Hfields : FieldUniverseSupport c.lparams HS.semantic.traversal.terminalContext
      (H.origins.minorShapes owner howner localIndex hlocal).fields := by
    simpa [HS.semantic.traversal_fields] using Hsupport.2
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have Hfull := Hfields.mono HS.semantic.fieldsRecent.toBoundFVarArray Hext
  let Hbound := HS.semantic.fieldsRecent.toBoundFVarArray.mono Hext
  simpa using Hfull.mkForall Hbound Hsupport.1

theorem CompletedRecursorConstruction.consumedConstructorAtParameters
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ∃ target,
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars) target ∧
      H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx target := by
  obtain ⟨target, Htr, Htype⟩ := HS.semantic.constructorTranslationAtSuffix
  have hrootEnv : H.recursorWF.venv = HS.semantic.rootWF.venv :=
    HS.semantic.extension.venv_eq.trans
      (HS.semantic.hypothesesRecent.venv_eq.trans HS.semantic.fieldsRecent.venv_eq)
  rw [← hrootEnv, HS.parameterDecls_eq] at Htr Htype
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have hsource := HS.semantic.fieldsRecent.toBoundFVarArray.mkForall_mono Hext HS.semantic.traversal.terminal
  rw [← hsource] at Htr
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have Habstract := H.parameterSuffix.abstractParameters H.params hparams (domains := []) (by
    simpa [abstractForallContext] using Htr)
  exact ⟨target, by simpa using Habstract, Htype⟩

private theorem recursorLevels_zero
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .zero) :
    recursorDeclarationAbstractLevels Us ha = VLevel.params Us.length := by
  subst elim
  rfl

private theorem recursorLevels_param
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .param fresh) :
    recursorDeclarationAbstractLevels Us ha = VLevel.prependShift Us.length := by
  subst elim
  simp only [recursorDeclarationAbstractLevels]
  exact VLevel.inst_map_id VLevel.prependShift_length

theorem CompletedRecursorConstruction.chooseOriginalSupportedType
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (hsource : source.levelParamsIn c.lparams = true)
    (Htr : TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source target)
    (Htype : H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      H.parameterSuffix.parameterDecls.toCtx target) :
    ∃ sourceTarget,
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse []) source sourceTarget ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx sourceTarget := by
  have Htype' : H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []).toCtx target := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Htype
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have Hctx := H.parameterAnonymousContext
    rw [recursorLevels_zero H.elimLevelAdmissible helim, R.sourceAnonymousParameterWF.instL_id] at Hctx
    refine ⟨target, ?_, ?_⟩
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htr
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams,
        abstractForallContext_toCtx, VLCtx.toCtx] using Htype'
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hctx := H.parameterAnonymousContext
    rw [recursorLevels_param H.elimLevelAdmissible helim] at Hctx
    have Htr' : TrExprS R.context.venv (fresh :: c.lparams)
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length))
        source target := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htr
    have hshift : ∀ level ∈ VLevel.prependShift c.lparams.length, level.WF (fresh :: c.lparams).length := by
      simpa using VLevel.prependShift_wf (n := c.lparams.length)
    have Hwf := (show VLCtx.WF R.context.venv (VLevel.prependShift c.lparams.length).length
        (abstractForallContext R.parameterScope.toCtx.reverse []) from by
          simpa using R.sourceAnonymousParameterWF).instL hshift
    have Hsource := Htr'.dropFreshLevelParam Hwf
    rw [levelParamsIn_fixed_dropFresh hsource hfresh, R.sourceAnonymousParameterWF.prepend_drop_levels] at Hsource
    have Htype'' : R.context.venv.IsType (fresh :: c.lparams).length
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length)).toCtx
        target := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htype'
    have HsourceType := Htype''.instL (recursorDropLevels_wf (n := c.lparams.length))
    have hcontext := congrArg VLCtx.toCtx R.sourceAnonymousParameterWF.prepend_drop_levels
    rw [VLCtx.instL_toCtx] at hcontext
    rw [hcontext] at HsourceType
    exact ⟨_, Hsource, by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HsourceType⟩

/-- The actual terminal family application is translated only after the
consumed source-field domains have been fixed. This preserves one constructor
context while allowing projection representations to change by typed conversion. -/
theorem CompletedRecursorConstruction.sourceConstructorTail
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let domains := H.sourceFields owner howner localIndex hlocal
    ∃ result,
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars)
        (VExpr.wrapForalls domains result) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx (VExpr.wrapForalls domains result) ∧
      TrExprS R.headerVEnv c.lparams
        (abstractForallContext domains (abstractForallContext R.parameterScope.toCtx.reverse []))
        ((HS.semantic.traversal.terminal.abstractList HS.semantic.fieldsRecent.fvars).abstractList
          H.params.fvars S.fields.size) result ∧
      R.headerVEnv.IsType c.lparams.length (domains.reverse ++ R.parameterScope.toCtx) result := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨sourceTarget, Hsource, HsourceType, _⟩ :=
    H.constructorConsumedHeaderReplay owner howner localIndex hlocal HS
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  let Hbound := HS.semantic.fieldsRecent.toBoundFVarArray.mono Hext
  have Htel := (Hbound.mkForall_forallTelescope H.localWF HS.semantic.traversal.terminal).abstractList H.params.fvars
  simp only [Nat.zero_add] at Htel
  have Htemplate : TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
      (Expr.forallDomainsOnly S.fields.size
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars))
      (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal) (.sort .zero)) := by
    rw [Expr.forallDomainsOnly_abstractList,
      Hbound.forallDomainsOnly H.localWF HS.semantic.fieldsRecent.nodup]
    exact (H.sourceFields_headerReplay owner howner localIndex hlocal).1
  have HsourceType' : R.headerVEnv.IsType c.lparams.length
      (abstractForallContext R.parameterScope.toCtx.reverse []).toCtx sourceTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HsourceType
  obtain ⟨result, Hnew, HnewType, Hres, HresType, _⟩ :=
    TrExprS.retargetForallPrefix R.headerCheckingAnnotations.1.wf R.headerAnonymousParameterWF Htel
      (H.sourceFields_length owner howner localIndex hlocal) Hsource HsourceType' Htemplate
  have hterminalClosed : Closed HS.semantic.traversal.terminal := by
    have h := HS.semantic.terminalTranslation.closed
    simpa [TypeChecker.MLCtx.noBV] using h
  have hboundNodup : Hbound.fvars.Nodup := HS.semantic.fieldsRecent.nodup
  rw [Expr.abstractN_eq_abstractList_of_closed (xs := Hbound.fvars) hboundNodup
    hterminalClosed] at Hres
  refine ⟨result, Hnew, ?_, Hres, ?_⟩
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HnewType
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HresType

end Lean4Lean.VerifyInductive
