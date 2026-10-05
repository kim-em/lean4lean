import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.CanonicalSourceBounds
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.ConsumedTelescopeSource
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem _root_.Lean4Lean.Closed.consumeTypeAnnotationsVerified {e : Expr} {k}
    (H : Closed e k) : Closed e.consumeTypeAnnotationsVerified k := by
  fun_induction Expr.consumeTypeAnnotationsVerified e
  case case1 ih => exact ih H.1.2
  case case2 => exact H
  case case3 ih => exact ih H.2
  case case4 => exact H
  case case5 => exact H

theorem _root_.Lean4Lean.Closed.consumeForallTypes {e : Expr} {k} (H : Closed e k) :
    Closed (Lean4Lean.Expr.consumeForallTypes e) k := by
  induction e generalizing k with
  | forallE _ _ _ _ _ ih => exact ⟨H.1.consumeTypeAnnotationsVerified, ih H.2⟩
  | _ => exact H

/-- Opening constructor fields preserves bound-variable closedness of the
remaining telescope. -/
theorem RecursorFieldDecisions.terminalClosed
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (hclosed : Closed source) : Closed terminal := by
  induction H with
  | nil => exact hclosed
  | nonrecursive _ _ ih | recursive _ _ ih =>
    have h := ih
    simp only [Closed] at h
    rw [Expr.instantiate1_eq]
    exact h.2.instantiate1 trivial

theorem RecursorFieldDecisions.consumeClosed
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars))
    (hclosed : Closed source)
    (C : Expr → Expr)
    (hforall : ∀ name dom body bi, C (.forallE name dom body bi) =
      .forallE name dom.consumeTypeAnnotationsVerified (C body) bi)
    (habstract : ∀ e fv, (C e).abstractN [fv] = C (e.abstractN [fv])) :
    current.lctx.mkForall fields (C terminal) = C source := by
  induction H with
  | nil => exact LocalContext.mkForall_empty _ _
  | @nonrecursive c name dom body bi fields selected positions H _ ih
  | @recursive c name dom body bi fields selected positions target H _ ih =>
    obtain ⟨Hc, _, ⟨Hfields⟩⟩ := H.freshBindings Hroot
    have hbodyScope := (H.currentFVarsIn Hroot hsource).2
    have hbodyFresh : body.FVarsIn (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
      apply hbodyScope.mono
      intro fv hfv heq
      subst fv
      exact Hc.current_not_mem hfv
    have hdecl : ∀ fv ∈ Hfields.fvars, ∃ decl, c.lctx.find? fv = some decl := by
      intro fv hf
      obtain ⟨index, name, type, bi, kind, hfind⟩ := Hc.findCDecl fv (Hfields.members fv hf)
      exact ⟨_, hfind⟩
    have hclose := LocalContext.mkForall_append_fresh Hc.wf Hc.currentFind?_eq_none hdecl Hfields.nodup
      (body := C (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) (name := name)
      (type := dom.consumeTypeAnnotationsVerified) (bi := bi)
    have hforallClosed := H.terminalClosed hclosed
    simp only [Closed] at hforallClosed
    have hbodyClose : (C (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))).abstractN [⟨c.ngen.curr⟩] = C body := by
      rw [habstract, Expr.instantiate1_eq, hbodyFresh.abstractN_instantiate1 hforallClosed.2]
    rw [hbodyClose, ← hforall] at hclose
    have harr : ((Hfields.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray =
        fields.push (.fvar ⟨c.ngen.curr⟩) := by simp [Hfields.expressions]
    rw [harr, ← Hfields.expressions] at hclose
    exact hclose.trans ih

theorem RecursorFieldDecisions.consumeForallTypes
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars))
    (hclosed : Closed source) :
    current.lctx.mkForall fields (Lean4Lean.Expr.consumeForallTypes terminal) =
      Lean4Lean.Expr.consumeForallTypes source :=
  H.consumeClosed Hroot hsource hclosed Lean4Lean.Expr.consumeForallTypes
    (fun _ _ _ _ => rfl) (fun e fv => Lean4Lean.Expr.abstractN_consumeForallTypes e [fv])

theorem CompletedRecursorConstruction.constructorConsumedSource
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    (H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars =
      Lean4Lean.Expr.consumeForallTypes
        (HS.semantic.traversal.parameterTail.abstractList H.params.fvars) := by
  have hsource : HS.semantic.traversal.parameterTail.FVarsIn
      (fun fv => fv ∈ HS.semantic.traversal.rootContext.lctx.fvars) := by
    apply HS.semantic.parameterScope.mono
    intro fv hfv
    rw [← HS.semantic.rootWF.lctx_eq, HS.semantic.rootWF.mlctx_wf.tr.fvars_eq,
      HS.semantic.parameterSuffix.context, VLCtx.fvars_append]
    exact List.mem_append_right _ hfv
  have hsourceBVar : Closed HS.semantic.traversal.parameterTail := by
    have h := HS.semantic.parameterTranslation.closed
    simpa [HS.semantic.rootWF.mlctx.noBV] using h
  have hclosed := HS.semantic.traversal.decisions.consumeForallTypes
    HS.semantic.rootWF.toBindingContextWF hsource hsourceBVar
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, _, hvalid, _⟩ :=
    H.minorSources owner howner (by rwa [← H.sourceFamilyCount]) localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at hvalid
  obtain ⟨htarget, hvalidIdx⟩ := checkPositivityStep.isValidIndApp?_some hvalid
  have htarget' : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).1 < decl.types.length := by
    rwa [H.cardinality.families] at htarget
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.validStats.indConstAt htarget')
  have hterminal : Lean4Lean.Expr.consumeForallTypes HS.semantic.traversal.terminal =
      HS.semantic.traversal.terminal := by
    have hterminalConst (e : Expr) (name : Name) (levels : List Level)
        (hhead : e.getAppFn = .const name levels) : Lean4Lean.Expr.consumeForallTypes e = e := by
      cases e <;> simp_all [Lean4Lean.Expr.consumeForallTypes, Expr.getAppFn]
    exact hterminalConst _ _ _ hhead
  rw [hterminal, HS.semantic.traversal_fields] at hclosed
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have hcontext := HS.semantic.fieldsRecent.toBoundFVarArray.mkForall_mono Hext
    HS.semantic.traversal.terminal
  dsimp only
  rw [hcontext, hclosed, Lean4Lean.Expr.abstractList_consumeForallTypes]

/-- The source header's cached parameter order also closes strict translations
in the original universe context. -/
theorem TrExprS.abstractCachedParameters {scope : VLCtx}
    (Hcached : List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
      params.toList.reverse scope)
    (Hparams : BoundFVarArray root params) (hnd : Hparams.fvars.Nodup)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList Hparams.fvars) target := by
  have hparamExprs : params.toList.reverse = Hparams.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList Hparams.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  rw [hparamExprs, List.forall₂_map_left_iff] at Hcached
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
      Hparams.fvars.reverse scope :=
    Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have Hclosed := TrExprS.abstractFVarLambdaSuffix (domains := []) Hdecls
    (List.nodup_reverse.mpr hnd) (by simpa [abstractForallContext] using Htr)
  simpa using Hclosed

theorem CompletedRecursorConstruction.constructorRawSourceReplay
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
      (HS.semantic.traversal.parameterTail.abstractList H.params.fvars)
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨traversal, htraversal, _, _, _, Hraw⟩ := H.minorSourceReplay owner howner
    (by rwa [← H.sourceFamilyCount]) localIndex hlocal
    (H.sourceMinorOffsetBound owner howner localIndex hlocal)
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at Hraw
  have Hcached := R.materializedFinal.parameterSuffix.cached
  have hscope : R.materializedFinal.parameterSuffix.parameterDecls = R.parameterScope :=
    R.materializedFinal_parameterScope
  rw [hscope] at Hcached
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  exact TrExprS.abstractCachedParameters Hcached H.params hparams
    Hraw

theorem CompletedRecursorConstruction.constructorRawSourceUniverses
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    (HS.semantic.traversal.parameterTail.abstractList H.params.fvars).levelParamsIn c.lparams = true :=
  (H.constructorRawSourceReplay owner howner localIndex hlocal HS).levelParamsIn


/-- Header installation preserves the local checking relation and annotation
wrapper bodies, even while primitive metadata is not yet complete. -/
theorem CompletedConstructorPhases.headerCheckingAnnotations
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    CheckingEnv c.safety R.headerEnv R.headerVEnv ∧ TypeAnnotationWrappers R.headerEnv := by
  have Hsource := R.sourceContext.checking
  rw [R.sourceContextVEnv] at Hsource
  cases R.installation with
  | ordinary Htypes _ =>
    exact ⟨(Htypes.validCore Hsource.toValidCore).tr, (Htypes.validCore Hsource.toValidCore).typeAnnotationWrappers⟩
  | primitive Htypes _ _ =>
    exact ⟨Htypes.checking Hsource.tr,
      Htypes.typeAnnotationWrappers Hsource.tr.map_wf Hsource.typeAnnotationWrappers⟩

theorem CompletedConstructorPhases.headerAnonymousParameterWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VLCtx.WF R.headerVEnv c.lparams.length
      (abstractForallContext R.parameterScope.toCtx.reverse []) := by
  have Hparams := R.materialized.paramsContext
  rw [R.materializedParameterScope] at Hparams
  have Hctx := abstractForallContext.isDefEq
    (right := R.parameterScope.toCtx.reverse) (by simpa using Hparams)
  exact (Hctx.symm R.headerCheckingAnnotations.1.wf.ordered).wf

/-- The raw source replay is typed before constructors are added. -/
theorem CompletedConstructorPhases.sourceConstructorTailType
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (index : Fin decl.ownedConstructors.length) :
    let ctor := R.sourceSignatureConstructor index
    R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨_, _, _, tailTarget, _, _, _, _, _, htail, _, htype⟩ := R.sourceSignatureConstructor_replay index
  have Htype := htail.isType
  rw [sourceConstructor_tail_eq htype] at Htype
  exact Eq.mp (congrArg (fun u => R.headerVEnv.IsType u R.parameterScope.toCtx
    (VExpr.wrapForalls (R.sourceSignature.fieldTypes (R.sourceSignatureConstructor index))
      (R.sourceSignature.familyApp (R.sourceSignatureConstructor index).owner
        (VLevel.params R.sourceSignature.uvars)
        (InductiveSignature.vars R.sourceSignature.params.length (R.sourceSignatureConstructor index).fields.length)
        (R.sourceSignatureConstructor index).indices))) R.materialized.uvars.symm) Htype

/-- Consume the original source constructor directly in the header
checking environment, using the actual production trace to identify its
closed native syntax. -/
theorem CompletedRecursorConstruction.constructorConsumedHeaderReplay
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    ∃ consumed,
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars) consumed ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx consumed ∧
      R.headerVEnv.IsDefEqU c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
          (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
            (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) consumed := by
  have Hraw := H.constructorRawSourceReplay owner howner localIndex hlocal HS
  have Htype := R.sourceConstructorTailType
    ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
  have hctx : (abstractForallContext R.parameterScope.toCtx.reverse []).toCtx = R.parameterScope.toCtx := by
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  rw [← hctx] at Htype
  obtain ⟨consumed, Hconsumed, HconsumedType, Heq⟩ := Hraw.consumeForallTypes_of_wrappers
    R.headerCheckingAnnotations.1 R.headerCheckingAnnotations.2 R.headerAnonymousParameterWF Htype
  rw [← H.constructorConsumedSource owner howner localIndex hlocal HS] at Hconsumed
  exact ⟨consumed, Hconsumed, by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HconsumedType,
    by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Heq⟩

end Lean4Lean.VerifyInductive
