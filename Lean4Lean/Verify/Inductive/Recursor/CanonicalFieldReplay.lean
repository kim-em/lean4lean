import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldUniverses
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldConsumption
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMotiveGroup
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem MLCtxOnlyLams.mkForall_fvarsIn_upset
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us)
    (n : Nat) (hn : n ≤ m.length) (body : Expr)
    (Hup : IsFVarUpSet (fun fv => fv ∈ m.fvarRevList n hn ∨ P fv) m.vlctx)
    (Hbody : body.FVarsIn (fun fv => fv ∈ m.fvarRevList n hn ∨ P fv)) :
    (m.mkForall n hn body).FVarsIn P := by
  induction n generalizing m body with
  | zero => simpa using Hbody
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlet fv name type value type' value' tail => exact H.vlet_false.elim
    | vlam fv name type type' bi tail =>
      have htail := Nat.le_of_succ_le_succ hn
      have hnot := Hwf.1.tr.find?_eq_none.mp Hwf.2.1
      let Q := fun other => other ∈ tail.fvarRevList n htail ∨ P other
      have HupTail : IsFVarUpSet Q tail.vlctx := by
        apply (IsFVarUpSet.congr Hwf.1.tr.wf.fvwf (P := fun other => other = fv ∨ Q other) (Q := Q) ?_).mp
          (by simpa [TypeChecker.MLCtx.fvarRevList, Q, List.mem_cons, or_assoc] using Hup.1)
        intro other hother
        have hne : other ≠ fv := by intro heq; subst other; exact hnot hother
        simp [hne]
      have Htype : type.FVarsIn Q := by
        apply fvarsIn_iff.mpr
        refine ⟨?_, Hwf.2.2.1.fvarsIn.mono (fun _ _ => trivial)⟩
        intro other hother
        have hP := Hup.2 (by simp) other hother
        have hmem := (fvarsIn_iff.mp Hwf.2.2.1.fvarsIn).1 other hother
        have hne : other ≠ fv := by intro heq; subst other; exact hnot hmem
        simpa [Q, TypeChecker.MLCtx.fvarRevList, hne] using hP
      apply ih H.tail_vlam Hwf.1 htail _ HupTail
      constructor
      · exact Htype
      · apply FVarsIn.abstract1_of
        simpa [TypeChecker.MLCtx.fvarRevList, Q, List.mem_cons, or_assoc] using Hbody

theorem RecInfoMinorSemanticSource.fieldSourceFVars
    {root : AddInductive.Context} {Rroot : RecursorContextWF root recLparams}
    {S : RecInfoMinorTypeShape} (HS : RecInfoMinorSemanticSource Rroot S) :
    (HS.traversal.terminalContext.lctx.mkForall S.fields (.sort .zero)).FVarsIn
      (· ∈ HS.parameterSuffix.parameterDecls.fvars) := by
  rw [← HS.terminalWF.lctx_eq,
    HS.terminalWF.mlctx_wf.mkForall_eq (e := .sort .zero) S.fields.size HS.fieldsRecent.size_le
      HS.fieldsRecent.reverse_eq trivial]
  have Hup : IsFVarUpSet
      (fun fv => fv ∈ HS.terminalWF.mlctx.fvarRevList S.fields.size HS.fieldsRecent.size_le ∨
        fv ∈ ExprArrayFVarIds HS.traversal.stats.params) HS.terminalWF.mlctx.vlctx := by
    simpa [HS.fieldsRecent.fvarRevList_eq] using HS.fieldParameterUp
  have Hfv := HS.terminalWF.onlyLams.mkForall_fvarsIn_upset HS.terminalWF.mlctx_wf
    S.fields.size HS.fieldsRecent.size_le (.sort .zero) Hup (by trivial)
  simpa [HS.parameterSuffix.parameterDecls_fvars] using Hfv

theorem RecInfoMinorSemanticSource.fieldTranslationAtSuffix
    {root : AddInductive.Context} {Rroot : RecursorContextWF root recLparams}
    {S : RecInfoMinorTypeShape} (HS : RecInfoMinorSemanticSource Rroot S) :
    ∃ target, TrExprS HS.rootWF.venv recLparams HS.parameterSuffix.parameterDecls
      (HS.traversal.terminalContext.lctx.mkForall S.fields (.sort .zero)) target := by
  have Htr := (HS.fieldsRecent.mkForallExact (body := .sort .zero) (bodyTarget := .sort .zero) (.sort rfl) ⟨_, .sort trivial⟩).1
  rw [HS.parameterSuffix.context] at Htr
  have Hwf : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).WF
      HS.rootWF.venv recLparams.length := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx_wf.tr.wf
  have HnoBV : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).NoBV := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx.noBV
  exact TrExprS.dropFVarPrefix HS.rootWF.checking.tr.wf Hwf HnoBV Htr HS.fieldSourceFVars

theorem TrExprS.isType_forallSort
    (Htel : Expr.ForallTelescope source n (.sort level))
    (Htr : TrExprS env Us Δ source target) : env.IsType Us.length Δ.toCtx target := by
  cases Htel with
  | nil => cases Htr with | sort hu => exact ⟨_, .sort (VLevel.WF.of_ofLevel hu)⟩
  | cons Htel => cases Htr with | forallE Hdom Hbody _ _ => exact .forallE Hdom Hbody

theorem CompletedRecursorConstruction.consumedFieldDomains
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ∃ domains, domains.length = S.fields.size ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars)
        (VExpr.wrapForalls domains (.sort .zero)) ∧
      H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx (VExpr.wrapForalls domains (.sort .zero)) := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨HS⟩ := H.minorSemantics owner howner localIndex hlocal
  obtain ⟨target, Htr⟩ := HS.semantic.fieldTranslationAtSuffix
  have hrootEnv : H.recursorWF.venv = HS.semantic.rootWF.venv :=
    HS.semantic.extension.venv_eq.trans
      (HS.semantic.hypothesesRecent.venv_eq.trans HS.semantic.fieldsRecent.venv_eq)
  rw [← hrootEnv, HS.parameterDecls_eq] at Htr
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have hsource := HS.semantic.fieldsRecent.toBoundFVarArray.mkForall_mono Hext (.sort .zero)
  rw [← hsource] at Htr
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have Habstract := H.parameterSuffix.abstractParameters H.params hparams (domains := []) (by
    simpa [abstractForallContext] using Htr)
  simp only [List.append_nil, List.length_nil] at Habstract
  have Hbound := S.fields_bound.mono HS.semantic.extension.contextLE
  have Htel := (Hbound.mkForall_forallTelescope H.localWF (.sort .zero)).abstractList H.params.fvars
  have hsort (fvars : List FVarId) (k : Nat) :
      (Expr.sort .zero).abstractList fvars k = .sort .zero :=
    Expr.abstractList_eq_self_of_abstract1 _ (by intro fv depth; simp [Expr.abstract1]) fvars k
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort .zero).abstractN fvars k = .sort .zero := rfl
  simp only [hsort, hsortN] at Htel
  obtain ⟨domains, result, hdomains, heq, Hresult⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Habstract
  cases Hresult with
  | sort hu =>
    cases hu
    rw [heq] at Habstract
    exact ⟨domains, hdomains, Habstract, by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
        TrExprS.isType_forallSort Htel Habstract⟩

theorem Expr.ForallTelescope.forallDomainsOnly_eq
    (H : Expr.ForallTelescope source n (.sort .zero)) :
    Expr.forallDomainsOnly n source = source := by
  induction n generalizing source with
  | zero => cases H; rfl
  | succ n ih =>
    cases H with
    | cons Htail => simp [Expr.forallDomainsOnly, ih Htail]

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

/-- A supported consumed telescope can be chosen at source universes and
replayed exactly in the recursor universe context. -/
theorem CompletedRecursorConstruction.chooseOriginalSupportedDomains
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (Htel : Expr.ForallTelescope source n (.sort .zero))
    (hsource : source.levelParamsIn c.lparams = true)
    (hdomains : domains.length = n)
    (Htr : TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
      (VExpr.wrapForalls domains (.sort .zero))) :
    ∃ sourceDomains, sourceDomains.length = n ∧
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          (sourceDomains.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have Hctx := H.parameterAnonymousContext
    rw [recursorLevels_zero H.elimLevelAdmissible helim, R.sourceAnonymousParameterWF.instL_id] at Hctx
    have Hsource : TrExprS R.context.venv c.lparams
        (abstractForallContext R.parameterScope.toCtx.reverse []) source
        (VExpr.wrapForalls domains (.sort .zero)) := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htr
    refine ⟨domains, hdomains, Hsource, ?_, ?_⟩
    · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using TrExprS.isType_forallSort Htel Hsource
    · have Hidentity := Hsource.substLevelParamsCore
        (Us := c.lparams) (F := Level.param) (ls := VLevel.params c.lparams.length)
        R.sourceAnonymousParameterWF
        (fun level hlevel => VLevel.params_wf hlevel)
        (fun u u' hu => by
          simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu)
      rw [Expr.instantiateLevelParamsCore_id, R.sourceAnonymousParameterWF.instL_id] at Hidentity
      rw [Hctx, H.recursorEnv, recursorLevels_zero H.elimLevelAdmissible helim]
      simpa [helim, AddInductive.getRecLevelParams, VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst]
        using Hidentity
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hctx := H.parameterAnonymousContext
    rw [recursorLevels_param H.elimLevelAdmissible helim] at Hctx
    have Htr' : TrExprS R.context.venv (fresh :: c.lparams)
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length))
        source (VExpr.wrapForalls domains (.sort .zero)) := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htr
    obtain ⟨sourceDomains, hlength, Hsource, Htype, Hrec⟩ :=
      TrExprS.chooseOriginalForallDomains R.context.checking.tr.wf R.sourceAnonymousParameterWF
        hfresh Htel hdomains Htr' (by
          rw [Htel.forallDomainsOnly_eq]
          exact levelParamsIn_fixed_dropFresh hsource hfresh)
    rw [Htel.forallDomainsOnly_eq] at Hsource Hrec
    refine ⟨sourceDomains, hlength, Hsource, ?_, ?_⟩
    · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Htype
    · rw [Hctx, H.recursorEnv, recursorLevels_param H.elimLevelAdmissible helim]
      simpa [helim, AddInductive.getRecLevelParams] using Hrec

/-- Lift a previously selected original-universe translation into the actual
recursor context without making another target choice. -/
theorem CompletedRecursorConstruction.liftOriginalType
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (Hsource : TrExprS R.context.venv c.lparams
      (abstractForallContext R.parameterScope.toCtx.reverse []) source target) :
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
      (target.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have Hidentity := Hsource.substLevelParamsCore
      (Us := c.lparams) (F := Level.param) (ls := VLevel.params c.lparams.length)
      R.sourceAnonymousParameterWF (fun level hlevel => VLevel.params_wf hlevel)
      (fun u u' hu => by
        simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu)
    rw [Expr.instantiateLevelParamsCore_id] at Hidentity
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorLevels_zero H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hidentity
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hrec := Hsource.prependLevelParam R.context.checking.tr.wf R.sourceAnonymousParameterWF hfresh
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorLevels_param H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hrec

/-- Select the field telescope in the header environment, before any current
constructor can enter a projection witness. Retain its exact lifted replay. -/
theorem CompletedRecursorConstruction.sourceFieldDomains
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (_hsourceOwner : owner < indTypes.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (_hindex : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    ∃ sourceDomains, sourceDomains.length = S.fields.size ∧
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          (sourceDomains.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  obtain ⟨HS⟩ := H.minorSemantics owner howner localIndex hlocal
  obtain ⟨target, Htr, _⟩ := H.constructorConsumedHeaderReplay owner howner localIndex hlocal HS
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  let Hbound := HS.semantic.fieldsRecent.toBoundFVarArray.mono Hext
  have Htel := (Hbound.mkForall_forallTelescope H.localWF HS.semantic.traversal.terminal).abstractList H.params.fvars
  obtain ⟨domains, result, hlen, heq, _⟩ := TrExprS.forallTelescope_shape_with_context Htel Htr
  rw [heq] at Htr
  obtain ⟨Hprefix, HprefixType⟩ := TrExprS.forallDomainsOnly Htel hlen Htr
  rw [Expr.forallDomainsOnly_abstractList,
    Hbound.forallDomainsOnly H.localWF HS.semantic.fieldsRecent.nodup] at Hprefix
  refine ⟨domains, hlen, Hprefix, ?_, ?_⟩
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HprefixType
  · simpa [VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst] using
      H.liftOriginalType (Hprefix.mono (R.installation.constructorLE.trans R.ctorLE))

end Lean4Lean.VerifyInductive
