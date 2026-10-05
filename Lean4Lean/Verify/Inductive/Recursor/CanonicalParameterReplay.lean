import Lean4Lean.Verify.Inductive.CompletedRecursorConstruction

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Close an arbitrary generated body over the actual cached parameter
binders. These are the annotation-consumed domains used by production. -/
theorem RecursorParameterContextSuffix.closeParameters
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (Hbody : TrExprS R.venv recLparams H.parameterDecls source target)
    (HbodyType : R.venv.IsType recLparams.length H.parameterDecls.toCtx target) :
    let parameterMLCtx := R.mlctx.dropN depth H.depth_le
    TrExprS R.venv recLparams []
        (R.mlctx.lctx.mkForall stats.params
          source)
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          target) ∧
      R.venv.IsType recLparams.length []
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          target) := by
  let parameterMLCtx := R.mlctx.dropN depth H.depth_le
  have hparameterWF : parameterMLCtx.WF R.venv recLparams := by
    simpa [parameterMLCtx] using R.mlctx_wf.dropN depth H.depth_le
  have hparameterOnly : MLCtxOnlyLams parameterMLCtx := by
    simpa [parameterMLCtx] using R.onlyLams.dropN depth H.depth_le
  have hparameterCtx : parameterMLCtx.vlctx = H.parameterDecls := by
    simpa [parameterMLCtx] using H.dropAmbient_vlctx
  have hparams : stats.params.toList.reverse =
      (parameterMLCtx.fvarRevList parameterMLCtx.length
        (Nat.le_refl _)).map Expr.fvar := by
    rcases cachedParameterDecls_fvars H.cached with
      ⟨fvars, hsource, hscope⟩
    rw [TypeChecker.MLCtx.fvarRevList_all, hparameterCtx, hscope]
    exact hsource
  have hparamsArray : stats.params =
      (parameterMLCtx.vlctx.fvars.reverse.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    rw [TypeChecker.MLCtx.fvarRevList_all] at hparams
    have hforward := congrArg List.reverse hparams
    simpa [List.map_reverse] using hforward
  have hlocalSource : R.mlctx.lctx.mkForall stats.params
        source =
      parameterMLCtx.lctx.mkForall stats.params
        source := by
    rw [hparamsArray, LocalContext.mkForall, LocalContext.mkForall,
      LocalContext.mkBinding_eq, LocalContext.mkBinding_eq]
    apply LocalContext.mkBindingList_congr
    intro fv hfv
    apply R.onlyLams.dropN_find?_eq R.mlctx_wf depth H.depth_le
    exact List.mem_reverse.mp hfv
  have hbody : TrExprS R.venv recLparams parameterMLCtx.vlctx source target := by
    simpa only [hparameterCtx] using Hbody
  have hsource : parameterMLCtx.lctx.mkForall stats.params
        source =
      parameterMLCtx.mkForall parameterMLCtx.length (Nat.le_refl _)
        source :=
    hparameterWF.mkForall_eq parameterMLCtx.length (Nat.le_refl _) hparams
      (by simpa [TypeChecker.MLCtx.noBV] using hbody.closed)
  have hbodyType : R.venv.IsType recLparams.length parameterMLCtx.vlctx.toCtx target := by
    simpa only [hparameterCtx] using HbodyType
  have hclosed := hparameterWF.mkForall_trS R.checking.tr.wf
    hbody hbodyType parameterMLCtx.length (Nat.le_refl _)
  have hdomains := hparameterOnly.forallDomains_eq_take_reverse
    parameterMLCtx.length (Nat.le_refl _)
  have hparameterLength : parameterMLCtx.length =
      H.parameterDecls.length := by
    rw [← TypeChecker.MLCtx.vlctx_length, hparameterCtx]
  have htake : H.parameterDecls.toCtx.take parameterMLCtx.length =
      H.parameterDecls.toCtx := by
    have htoCtxLength : H.parameterDecls.toCtx.length =
        H.parameterDecls.length :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        H.cached
    apply List.take_of_length_le
    rw [htoCtxLength, ← hparameterLength]
    exact Nat.le_refl _
  rw [TypeChecker.MLCtx.dropN_all, ← hsource] at hclosed
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, hdomains] at hclosed
  rw [hparameterCtx, htake] at hclosed
  rw [hlocalSource]
  exact hclosed


private theorem ctx_levelWF {env : VEnv} {Γ : List VExpr} (H : OnCtx Γ (env.IsType U)) :
    OnCtx Γ (fun _ A => A.LevelWF U) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih => exact ⟨ih H.1, (Classical.choose_spec H.2).levelWF (ih H.1) |>.1⟩

private theorem ctx_instL_id {env : VEnv} {Γ : List VExpr} (H : OnCtx Γ (env.IsType U)) :
    Γ.map (VExpr.instL (VLevel.params U)) = Γ := by
  have Hw := ctx_levelWF H
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.map_cons, Hw.2.instL_id]
    exact congrArg (List.cons A) (ih H.1 Hw.1)

theorem checkInductiveTypes.loopType.ParameterContextSuffix.recursorDomains
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (H.toRecursorContext Helim).parameterDecls.toCtx =
      H.parameterDecls.toCtx.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams Helim)) := by
  have Hwf := (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix Hc H).scopeWF Hc.checking.tr.wf
  have hid := ctx_instL_id Hwf.toCtx
  cases elimLevel with
  | zero => exact hid.symm
  | param fresh =>
    change (H.parameterDecls.instL (VLevel.prependShift c.lparams.length)).toCtx = _
    rw [VLCtx.instL_toCtx]
    rw [recursorDeclarationAbstractLevels]
    conv => lhs; rw [← hid]
    rw [List.map_map]
    apply congrArg (fun f => List.map f H.parameterDecls.toCtx)
    funext e
    exact VExpr.instL_instL
  | succ level | max left right | imax left right | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The generated parameter domains descend from the actual cached source
scope, with exactly the executable recursor universe substitution. -/
theorem CompletedRecursorConstruction.parameterDomains
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) :
    H.parameterSuffix.parameterDecls.toCtx.reverse =
      R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
  rw [H.parameterDecls,
    checkInductiveTypes.loopType.ParameterContextSuffix.recursorDomains,
    List.map_reverse]
  have hscope : R.materializedFinal.parameterSuffix.parameterDecls = R.parameterScope :=
    R.materializedFinal_parameterScope
  rw [hscope]

/-- Translate the concrete closed parameter telescope to that source-boundary
choice, without deriving a literal target from translation uniqueness. -/
theorem CompletedRecursorConstruction.sourceParameterTranslation
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params (.sort .zero))
      (VExpr.wrapForalls (R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
        (.sort .zero)) := by
  have Htr := H.parameterSuffix.closedSortTranslation
  rw [H.recursorEnv, H.recursorWF.lctx_eq, H.parameterDomains] at Htr
  exact Htr


theorem CompletedConstructorPhases.sourceParameterContext
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    sourceEnv.IsDefEqCtx decl.uvars [] R.params.reverse R.parameterScope.toCtx := by
  have Hctx := R.sourceMaterialized.paramsContext
  rw [R.sourceHeaderParams, R.sourceParameterScope,
    R.sourceContextVEnv, R.sourceMaterialized.uvars] at Hctx
  exact Hctx

theorem CompletedRecursorConstruction.closeSourceParameters
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (Hbody : TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls source target)
    (HbodyType : R.context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      H.parameterSuffix.parameterDecls.toCtx target) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params source)
      (VExpr.wrapForalls (R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))) target) ∧
    R.context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (VExpr.wrapForalls (R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))) target) := by
  have Htr := H.parameterSuffix.closeParameters
    (by simpa only [H.recursorEnv] using Hbody)
    (by simpa only [H.recursorEnv] using HbodyType)
  rw [H.recursorEnv, H.recursorWF.lctx_eq, H.parameterDomains] at Htr
  exact Htr

end Lean4Lean.VerifyInductive
