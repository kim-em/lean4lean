import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorReplay

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

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

/-- Choose both original-universe translations with the same substitution.
This retains the conversion between raw and consumed constructor telescopes;
independent choices of their projection witnesses need not be literally equal. -/
theorem CompletedRecursorConstruction.chooseOriginalSupportedTypesDefEq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (hleft : left.levelParamsIn c.lparams = true)
    (hright : right.levelParamsIn c.lparams = true)
    (Hleft : TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) left leftTarget)
    (Hright : TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) right rightTarget)
    (Htype : H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      H.parameterSuffix.parameterDecls.toCtx leftTarget)
    (Heq : H.recursorWF.venv.IsDefEqU (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      H.parameterSuffix.parameterDecls.toCtx leftTarget rightTarget) :
    ∃ originalLeft originalRight,
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        left originalLeft ∧
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        right originalRight ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx originalLeft ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx originalRight ∧
      R.context.venv.IsDefEqU c.lparams.length R.parameterScope.toCtx originalLeft originalRight := by
  have Htype' : H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []).toCtx leftTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Htype
  have Heq' : H.recursorWF.venv.IsDefEqU (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []).toCtx leftTarget rightTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Heq
  suffices ∃ originalLeft originalRight,
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        left originalLeft ∧
      TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        right originalRight ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx originalLeft ∧
      R.context.venv.IsDefEqU c.lparams.length R.parameterScope.toCtx originalLeft originalRight by
    obtain ⟨originalLeft, originalRight, Hleft, Hright, Htype, Heq⟩ := this
    exact ⟨originalLeft, originalRight, Hleft, Hright, Htype,
      Htype.defeqU_l R.context.checking.tr.wf (by
        simpa [abstractForallContext_toCtx, VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx) Heq, Heq⟩
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have Hctx := H.parameterAnonymousContext
    have hlevels := recursorLevels_zero H.elimLevelAdmissible helim
    rw [hlevels, R.sourceAnonymousParameterWF.instL_id] at Hctx
    refine ⟨leftTarget, rightTarget, ?_, ?_, ?_, ?_⟩
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Hleft
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Hright
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams,
        abstractForallContext_toCtx, VLCtx.toCtx] using Htype'
    · simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams,
        abstractForallContext_toCtx, VLCtx.toCtx] using Heq'
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hctx := H.parameterAnonymousContext
    have hlevels := recursorLevels_param H.elimLevelAdmissible helim
    rw [hlevels] at Hctx
    have Hleft' : TrExprS R.context.venv (fresh :: c.lparams)
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length))
        left leftTarget := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Hleft
    have Hright' : TrExprS R.context.venv (fresh :: c.lparams)
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length))
        right rightTarget := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Hright
    have hshift : ∀ level ∈ VLevel.prependShift c.lparams.length,
        level.WF (fresh :: c.lparams).length := by
      simpa using VLevel.prependShift_wf (n := c.lparams.length)
    have Hwf := (show VLCtx.WF R.context.venv (VLevel.prependShift c.lparams.length).length
        (abstractForallContext R.parameterScope.toCtx.reverse []) from by
          simpa using R.sourceAnonymousParameterWF).instL hshift
    have HsourceLeft := Hleft'.dropFreshLevelParam Hwf
    have HsourceRight := Hright'.dropFreshLevelParam Hwf
    rw [levelParamsIn_fixed_dropFresh hleft hfresh,
      R.sourceAnonymousParameterWF.prepend_drop_levels] at HsourceLeft
    rw [levelParamsIn_fixed_dropFresh hright hfresh,
      R.sourceAnonymousParameterWF.prepend_drop_levels] at HsourceRight
    have Htype'' : R.context.venv.IsType (fresh :: c.lparams).length
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length)).toCtx
        leftTarget := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Htype'
    have Heq'' : R.context.venv.IsDefEqU (fresh :: c.lparams).length
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL (VLevel.prependShift c.lparams.length)).toCtx
        leftTarget rightTarget := by
      simpa [Hctx, H.recursorEnv, helim, AddInductive.getRecLevelParams] using Heq'
    have HsourceType := Htype''.instL (recursorDropLevels_wf (n := c.lparams.length))
    have HsourceEq := Heq''.instL (recursorDropLevels_wf (n := c.lparams.length))
    have hcontext := congrArg VLCtx.toCtx R.sourceAnonymousParameterWF.prepend_drop_levels
    rw [VLCtx.instL_toCtx] at hcontext
    rw [hcontext] at HsourceType HsourceEq
    exact ⟨_, _, HsourceLeft, HsourceRight,
      by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HsourceType,
      by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HsourceEq⟩

end Lean4Lean.VerifyInductive
