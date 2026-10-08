import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldChoice
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel


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
