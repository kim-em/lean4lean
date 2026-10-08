import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.SourceUniverses
import Lean4Lean.Verify.Inductive.Recursor.LoopUniverses
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
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorDeclarationAbstractLevels_zero H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hidentity
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hrec := Hsource.prependLevelParam R.context.checking.tr.wf R.sourceAnonymousParameterWF hfresh
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorDeclarationAbstractLevels_param H.elimLevelAdmissible helim]
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
