import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorIndices
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldConsumption
import Lean4Lean.Verify.Inductive.Recursor.CanonicalUniversePair
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem TrExprS.dropFVarPrefix_defeq
    (henv : env.WF) (hscope : (added ++ suffix).WF env Us.length)
    (hnoBV : (added ++ suffix).NoBV)
    (Hleft : TrExprS env Us (added ++ suffix) sourceLeft targetLeft)
    (Hright : TrExprS env Us (added ++ suffix) sourceRight targetRight)
    (Heq : env.IsDefEqU Us.length (added ++ suffix).toCtx targetLeft targetRight)
    (hfvarsLeft : FVarsIn (· ∈ suffix.fvars) sourceLeft)
    (hfvarsRight : FVarsIn (· ∈ suffix.fvars) sourceRight) :
    ∃ left right, TrExprS env Us suffix sourceLeft left ∧
      TrExprS env Us suffix sourceRight right ∧
      env.IsDefEqU Us.length suffix.toCtx left right := by
  obtain ⟨left, HnewLeft⟩ := TrExprS.dropFVarPrefix henv hscope hnoBV Hleft hfvarsLeft
  obtain ⟨right, HnewRight⟩ := TrExprS.dropFVarPrefix henv hscope hnoBV Hright hfvarsRight
  let W := (VLCtx.FVLift.to_append suffix (VLCtx.NoBV.leftOfAppend added suffix hnoBV)).toFVLift'
  have HweakLeft := HnewLeft.weakFV' henv.ordered W hscope
  have HweakRight := HnewRight.weakFV' henv.ordered W hscope
  have HeqLeft := HweakLeft.uniq henv (.refl henv hscope) Hleft
  have HeqRight := HweakRight.uniq henv (.refl henv hscope) Hright
  have HweakEq := (HeqLeft.trans henv hscope.toCtx Heq).trans henv hscope.toCtx HeqRight.symm
  exact ⟨left, right, HnewLeft, HnewRight,
    (VEnv.IsDefEqU.weak'_iff henv hscope.toCtx W.toCtx).1 HweakEq⟩

theorem TrExprS.isType_dropFVarPrefix
    (henv : env.WF) (hscope : (added ++ suffix).WF env Us.length)
    (hnoBV : (added ++ suffix).NoBV)
    (Hfull : TrExprS env Us (added ++ suffix) source target)
    (Hsmall : TrExprS env Us suffix source targetSmall)
    (Htype : env.IsType Us.length (added ++ suffix).toCtx target) :
    env.IsType Us.length suffix.toCtx targetSmall := by
  let W := (VLCtx.FVLift.to_append suffix (VLCtx.NoBV.leftOfAppend added suffix hnoBV)).toFVLift'
  have Hweak := Hsmall.weakFV' henv.ordered W hscope
  have Heq := Hweak.uniq henv (.refl henv hscope) Hfull
  obtain ⟨level, HweakType⟩ := Htype.defeqU_l henv hscope.toCtx Heq.symm
  exact ⟨level, (VEnv.HasType.weak'_iff henv hscope.toCtx W.toCtx).1 HweakType⟩

/-- The actual field traversal relates the raw constructor source to its
annotation-consumed telescope in the common parameter context. -/
theorem RecInfoMinorSemanticSource.constructorDefEqAtSuffix
    {root : AddInductive.Context} {Rroot : RecursorContextWF root recLparams}
    {S : RecInfoMinorTypeShape} (HS : RecInfoMinorSemanticSource Rroot S) :
    ∃ raw consumed,
      TrExprS HS.rootWF.venv recLparams HS.parameterSuffix.parameterDecls
        HS.traversal.parameterTail raw ∧
      TrExprS HS.rootWF.venv recLparams HS.parameterSuffix.parameterDecls
        (HS.traversal.terminalContext.lctx.mkForall S.fields HS.traversal.terminal) consumed ∧
      HS.rootWF.venv.IsType recLparams.length HS.parameterSuffix.parameterDecls.toCtx raw ∧
      HS.rootWF.venv.IsDefEqU recLparams.length HS.parameterSuffix.parameterDecls.toCtx raw consumed := by
  obtain ⟨Htr, Htype⟩ := HS.fieldsRecent.mkForallExact HS.terminalTranslation HS.terminalType
  have Hraw := HS.parameterTranslation
  have Heq := HS.fieldTargetDefEq
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at Heq
  rw [HS.parameterSuffix.context] at Htr Hraw Heq
  have Hwf : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).WF
      HS.rootWF.venv recLparams.length := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx_wf.tr.wf
  have HnoBV : (HS.parameterSuffix.ambientDecls ++ HS.parameterSuffix.parameterDecls).NoBV := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx.noBV
  obtain ⟨raw, consumed, HrawSmall, HconsumedSmall, HsmallEq⟩ :=
    TrExprS.dropFVarPrefix_defeq HS.rootWF.checking.tr.wf Hwf HnoBV Hraw Htr Heq
      HS.parameterScope HS.constructorSourceFVars
  refine ⟨raw, consumed, HrawSmall, HconsumedSmall, ?_, HsmallEq⟩
  apply TrExprS.isType_dropFVarPrefix HS.rootWF.checking.tr.wf Hwf HnoBV Hraw HrawSmall
  simpa only [← HS.parameterSuffix.context] using HS.parameterType

/-- Close the related constructor sources over exactly the shared parameter
binders used by generation. Their typed equality remains in the same abstract
parameter context. -/
theorem CompletedRecursorConstruction.constructorDefEqAtParameters
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ∃ raw consumed,
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
        (HS.semantic.traversal.parameterTail.abstractList H.params.fvars) raw ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars) consumed ∧
      H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx raw ∧
      H.recursorWF.venv.IsDefEqU (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx raw consumed := by
  obtain ⟨raw, consumed, Hraw, Hconsumed, Htype, Heq⟩ := HS.semantic.constructorDefEqAtSuffix
  have hrootEnv : H.recursorWF.venv = HS.semantic.rootWF.venv :=
    HS.semantic.extension.venv_eq.trans
      (HS.semantic.hypothesesRecent.venv_eq.trans HS.semantic.fieldsRecent.venv_eq)
  rw [← hrootEnv, HS.parameterDecls_eq] at Hraw Hconsumed Htype Heq
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have hsource := HS.semantic.fieldsRecent.toBoundFVarArray.mkForall_mono Hext HS.semantic.traversal.terminal
  rw [← hsource] at Hconsumed
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have HabstractRaw := H.parameterSuffix.abstractParameters H.params hparams (domains := []) (by
    simpa [abstractForallContext] using Hraw)
  have HabstractConsumed := H.parameterSuffix.abstractParameters H.params hparams (domains := []) (by
    simpa [abstractForallContext] using Hconsumed)
  exact ⟨raw, consumed, by simpa using HabstractRaw, by simpa using HabstractConsumed, Htype, Heq⟩

/-- The one selected consumed constructor is definitionally equal to its
retained raw source model in the original header environment, before the
constructors are installed. -/
theorem CompletedRecursorConstruction.sourceConstructorDefEq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    R.headerVEnv.IsDefEqU c.lparams.length R.parameterScope.toCtx
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices))
      (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal)
        (VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (VLevel.params decl.uvars))
          (InductiveSignature.vars stats.params.size S.fields.size ++
            H.sourceConstructorIndices owner howner localIndex hlocal))) := by
  let HS := H.sourceMinorSemantics owner howner localIndex hlocal
  obtain ⟨consumed, Hconsumed, _, Heq⟩ := H.constructorConsumedHeaderReplay owner howner localIndex hlocal HS
  have HfixedConsumed := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).1
  have henv := R.headerCheckingAnnotations.1.wf
  have hΔ := R.headerAnonymousParameterWF
  have Hright := Hconsumed.uniq henv (.refl henv hΔ) HfixedConsumed
  simp only [abstractForallContext_toCtx, List.reverse_reverse, VLCtx.toCtx, List.append_nil] at Hright
  have Hctx : OnCtx R.parameterScope.toCtx (R.headerVEnv.IsType c.lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hΔ.toCtx
  exact Heq.trans henv Hctx Hright

end Lean4Lean.VerifyInductive
