import Lean4Lean.Verify.Inductive.Equation.RecursiveBody

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Fixed-frame package for one complete recursive result.  The generated
recursor telescope and rule-wide field narrowing are parameters, so every
array position is closed and typed in the same literal `equationDomains`;
only its higher-order local telescope varies with the recursive field. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResultTypingFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.NarrowFieldRuntimeFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    ∃ F : A.RecursiveCallRecursorFrame j hj,
      ∃ (localDomains : List VExpr)
          (resultBody resultType templateTarget : VExpr),
        equationDomains.length = A.rule.binders.length ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        OnCtx (abstractForallContext equationDomains []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext equationDomains [])
          ((F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs (.sort .zero)).abstractList
              A.rule.binders)
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        Expr.LambdaTelescope
          (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
          localDomains.length
          ((F.semantic.generated.body.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          ((F.semantic.generated.body.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size)
          resultBody ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMajor A.rule.binders)
          templateTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
          resultType ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (equationDomains ++ localDomains) []).toCtx resultType ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
          (VExpr.wrapLams localDomains resultBody)
          (VExpr.wrapForalls localDomains resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  rcases A.recursiveCallRecursorFrame j hj with ⟨F⟩
  rcases F.canonicalRecursiveCallBodyWF T (B := B) with
    ⟨actualDomains, localDomains, prefixTarget, indexTargets,
      majorTarget, ownerTarget, hlocal, hdomains, hequation, _Hctx,
      HlocalTemplate, Hbody, HtemplateResidual, HmotiveApplication,
      HbodyType, Hclosed, _HbodyWF⟩
  have hactual : actualDomains = equationDomains := by
    exact hdomains
  subst actualDomains
  let args := indexTargets ++ [majorTarget]
  let resultBody := VExpr.mkApps prefixTarget args
  let resultType := VExpr.mkApps ownerTarget args
  have Htelescope :=
    F.semantic.generated.outerAbstractedLambdaTelescope A.rule.binders
  have Htelescope' : Expr.LambdaTelescope
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      localDomains.length
      ((F.semantic.generated.body.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size) := by
    simpa [hlocal] using Htelescope
  have HequationCtx : OnCtx
      (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    have Hbase := _Hctx.drop localDomains.length
    simpa [equationDomains, Us, abstractForallContext_toCtx,
      List.reverse_append, List.drop_append, List.length_reverse,
      List.append_assoc] using Hbase
  have HresultType : H.outVEnv.IsType Us.length
      (abstractForallContext (equationDomains ++ localDomains) []).toCtx
      resultType := by
    simpa [equationDomains, Us, resultType, args,
      abstractForallContext_toCtx, List.reverse_append,
      List.append_assoc] using HbodyType.isType H.outVEnvWF _Hctx
  exact ⟨F, localDomains, resultBody, resultType, majorTarget,
    hequation, hlocal, HequationCtx, HlocalTemplate, Htelescope',
    by simpa [resultBody, args] using Hbody,
    HtemplateResidual,
    by simpa [resultType, args] using HmotiveApplication,
    HresultType,
    by simpa [resultBody, resultType, args] using Hclosed⟩

/-- One recursive result in the fixed rule-wide equation context.  The
higher-order local telescope remains entry-specific, while its closed lambda
and forall type both live in the single context shared by the whole RHS. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.NarrowFieldRuntimeFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) where
  frame : A.RecursiveCallRecursorFrame j hj
  localDomains : List VExpr
  resultBody : VExpr
  resultType : VExpr
  templateTarget : VExpr
  equation_length :
    (H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse).length = A.rule.binders.length
  local_length : localDomains.length = frame.semantic.generated.localArgs.size
  equation_context :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    OnCtx (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length)
  local_forall_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((frame.semantic.generated.current.lctx.mkForall
        frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      (VExpr.wrapForalls localDomains (.sort .zero))
  source_telescope : Expr.LambdaTelescope
    (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
    localDomains.length
    ((frame.semantic.generated.body.abstractList
      frame.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.binders frame.semantic.generated.localArgs.size)
  template_telescope : Expr.LambdaTelescope
    ((frame.semantic.generated.current.lctx.mkLambda
        frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          frame.semantic.generated.localArgs)).abstractList A.rule.binders)
    localDomains.length
    (frame.semantic.generated.outerAbstractedMajor A.rule.binders)
  source_template_prefix : Expr.SameLambdaPrefix localDomains.length
    (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
    ((frame.semantic.generated.current.lctx.mkLambda
        frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          frame.semantic.generated.localArgs)).abstractList A.rule.binders)
  residual_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      ((frame.semantic.generated.body.abstractList
        frame.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders frame.semantic.generated.localArgs.size)
      resultBody
  template_residual_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (frame.semantic.generated.outerAbstractedMajor A.rule.binders)
      templateTarget
  result_type_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      resultType
  result_type_isType :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    H.outVEnv.IsType Us.length
      (abstractForallContext (equationDomains ++ localDomains) []).toCtx
      resultType
  closed_typing :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.wrapLams localDomains resultBody)
      (VExpr.wrapForalls localDomains resultType)

/-- Open a canonical recursive result under its retained higher-order local
telescope.  The caller supplies well-formedness of the shared equation
context; lambda-telescope inversion then returns both the extended dependent
context and the result body's exact (not merely definitionally equal) type.

This is the form consumed by a left-to-right dependent application spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.openTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (Hctx :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType Us.length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    OnCtx
        (E.localDomains.reverse ++
          (abstractForallContext equationDomains []).toCtx)
        (H.outVEnv.IsType Us.length) ∧
      H.outVEnv.HasType Us.length
        (E.localDomains.reverse ++
          (abstractForallContext equationDomains []).toCtx)
        E.resultBody E.resultType := by
  dsimp only at Hctx ⊢
  exact VEnv.HasType.wrapLams_inv H.outVEnvWF Hctx E.closed_typing

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResultAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.NarrowFieldRuntimeFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    Nonempty (A.CanonicalRecursiveResultAt T B j hj) := by
  rcases A.canonicalRecursiveResultTypingFor T B j hj with
    ⟨F, localDomains, resultBody, resultType, templateTarget, hequation,
      hlocal, HequationCtx, HlocalForall, Htelescope, Htranslation,
      HtemplateResidual, HtypeTranslation, HresultType, Htyping⟩
  have HtemplateTelescope : Expr.LambdaTelescope
      ((F.semantic.generated.current.lctx.mkLambda
          F.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs)).abstractList A.rule.binders)
      localDomains.length
      (F.semantic.generated.outerAbstractedMajor A.rule.binders) := by
    simpa [hlocal, BoundGeneratedRecursiveCall.outerAbstractedMajor] using
      (F.semantic.generated.appliedFieldLambdaTelescope.abstractList
        A.rule.binders)
  have HsamePrefix : Expr.SameLambdaPrefix localDomains.length
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      ((F.semantic.generated.current.lctx.mkLambda
          F.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs)).abstractList A.rule.binders) := by
    simpa [hlocal] using
      F.semantic.generated.sameOuterAppliedFieldLambdaPrefix A.rule.binders
  exact ⟨{
    frame := F
    localDomains := localDomains
    resultBody := resultBody
    resultType := resultType
    templateTarget := templateTarget
    equation_length := hequation
    local_length := hlocal
    equation_context := HequationCtx
    local_forall_translation := HlocalForall
    source_telescope := Htelescope
    template_telescope := HtemplateTelescope
    source_template_prefix := HsamePrefix
    residual_translation := Htranslation
    template_residual_translation := HtemplateResidual
    result_type_translation := HtypeTranslation
    result_type_isType := HresultType
    closed_typing := Htyping }⟩

/-- Replace the neutral codomain in the retained local-forall template by
the independently checked selected-motive application.  The source is the
exact complete higher-order domain produced by the recursive-call replay,
closed over production's full rule binder list. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.fullForallTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let motiveApp := Expr.app
      (mkAppN
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs)
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      (VExpr.wrapForalls E.localDomains E.resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let selection :=
    E.frame.semantic.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      E.frame.semantic.generated.current_wf
  have Hsame := (selection.sameForallPrefix
    E.frame.semantic.generated.arguments_bound.nodup
    (.sort (.zero : Level)) motiveApp).abstractList A.rule.binders
  have Htemplate₀ := (selection.forallTelescope
    (.sort (.zero : Level))).abstractList A.rule.binders
  have Hreplacement₀ :=
    (selection.forallTelescope motiveApp).abstractList A.rule.binders
  have hselectionFVars : selection.fvars =
      E.frame.semantic.generated.arguments_bound.fvars := rfl
  rw [hselectionFVars] at Htemplate₀ Hreplacement₀
  have hsortLocal : (Expr.sort (.zero : Level)).abstractList
      E.frame.semantic.generated.arguments_bound.fvars = .sort .zero := by
    induction E.frame.semantic.generated.arguments_bound.fvars <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortLocal] at Htemplate₀
  simp only [Nat.zero_add] at Htemplate₀
  have hsortOuter : (Expr.sort (.zero : Level)).abstractList
      A.rule.binders E.frame.semantic.generated.localArgs.size = .sort .zero := by
    induction A.rule.binders <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortOuter] at Htemplate₀
  have Htemplate : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size (.sort .zero) := by
    exact Htemplate₀
  have hresidual := E.frame.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.binders
  have HreplacementRaw : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size
      ((motiveApp.abstractList
        E.frame.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders E.frame.semantic.generated.localArgs.size) := by
    simpa using Hreplacement₀
  have Hreplacement : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders) := by
    rw [← hresidual]
    exact HreplacementRaw
  have HresultTranslation : TrExprS H.outVEnv Us
      (abstractForallContext E.localDomains
        (abstractForallContext equationDomains []))
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains, Us, abstractForallContext_append,
      List.append_assoc] using E.result_type_translation
  have HresultType : H.outVEnv.IsType Us.length
      (abstractForallContext E.localDomains
        (abstractForallContext equationDomains [])).toCtx E.resultType := by
    simpa [equationDomains, Us, abstractForallContext_append,
      List.append_assoc] using E.result_type_isType
  exact Hsame.replaceTranslatedResidual Htemplate Hreplacement
    H.outVEnvWF E.equation_context E.local_length
    E.local_forall_translation HresultTranslation HresultType

/-- Insert an already consumed prefix of recursive hypotheses beneath the
fixed equation context while retaining the complete canonical higher-order
domain.  Both its dependent local domains and its real residual are lifted
at their exact respective cutoffs. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.fullForallTranslationAfter
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (previous : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let motiveApp := Expr.app
      (mkAppN
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs)
    let liftedLocals :=
      (liftContextPrefix previous.length E.localDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ previous) [])
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders).liftLooseBVars' 0 previous.length)
      (VExpr.wrapForalls liftedLocals
        (E.resultType.liftN previous.length E.localDomains.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let liftedLocals :=
    (liftContextPrefix previous.length E.localDomains.reverse).reverse
  have Hbase := E.fullForallTranslation
  have Hinserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := []) H.outVEnvWF.ordered
      (by simpa [equationDomains, motiveApp] using Hbase) previous
  simpa [equationDomains, liftedLocals, VExpr.liftN_wrapForalls,
    VExpr.liftN, liftContextPrefix, liftContextPrefixAt,
    List.append_assoc] using Hinserted

/-- Source-side counterpart of `fullForallTranslationAfter`.  It retains the
exact residual selected-motive application after inserting the already
consumed recursive hypotheses, so first-pass and second-pass telescopes can
use `SameForallPrefix.translatedTelescopeAlignment` directly. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.fullForallSourceTelescopeAfter
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (previous : List VExpr) :
    let motiveApp := Expr.app
      (mkAppN
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs)
    Expr.ForallTelescope
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders).liftLooseBVars' 0 previous.length)
      E.frame.semantic.generated.localArgs.size
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size previous.length) := by
  dsimp only
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let selection :=
    E.frame.semantic.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      E.frame.semantic.generated.current_wf
  have Hraw := (selection.forallTelescope motiveApp).abstractList
    A.rule.binders
  have hselectionFVars : selection.fvars =
      E.frame.semantic.generated.arguments_bound.fvars := rfl
  rw [hselectionFVars] at Hraw
  have hresidual := E.frame.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.binders
  have Hbase : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders) := by
    rw [← hresidual]
    simpa [motiveApp] using Hraw
  simpa [motiveApp] using Hbase.liftLooseBVars' 0 previous.length

/-- The retained eta-template residual has a completely forced abstract
shape.  In particular, its target is the selected constructor-field variable
shifted under exactly the call-local telescope and applied to the canonical
local de Bruijn spine.  Keeping the selected source free variable in the
result lets later field-position alignment identify the same dependent minor
domain without choosing another narrowing witness. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.templateTargetShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    ∃ fv fieldVar,
      A.rule.recursiveArgs[j] = .fvar fv ∧
      fv ∈ A.rule.binders ∧
      fieldVar < equationDomains.length ∧
      (Expr.fvar fv).abstractList A.rule.binders = .bvar fieldVar ∧
      E.templateTarget =
        VExpr.mkApps (.bvar (E.localDomains.length + fieldVar))
          (E.frame.semantic.generated.localIndices.map VExpr.bvar) := by
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
    ⟨hjFVars, hsource⟩
  let fv := A.rule.recursive_args_bound.fvars[j]
  have hfieldRoot : fv ∈ A.rule.root.lctx.fvars :=
    A.rule.recursive_args_bound.members fv
      (List.getElem_mem hjFVars)
  have hfieldAll : fv ∈ A.rule.all_args_bound.fvars :=
    A.rule.recursive_args_bound.fvars_subset_of_sublist
      A.rule.all_args_bound A.rule.recursive_args_sublist
      (List.getElem_mem hjFVars)
  have hfieldBinders : fv ∈ A.rule.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ hfieldAll
  have Hmajor : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext E.localDomains
        (abstractForallContext equationDomains []))
      (E.frame.semantic.generated.outerAbstractedMajor A.rule.binders)
      E.templateTarget := by
    simpa [equationDomains, abstractForallContext_append] using
      E.template_residual_translation
  rcases
      E.frame.semantic.generated.translatedOuterAbstractedMajor_eq_of_field_eq
        hsource hfieldRoot A.rule.binders_nodup hfieldBinders
        E.equation_length E.local_length Hmajor with
    ⟨fieldVar, hfieldVar, hfieldSource, htarget⟩
  exact ⟨fv, fieldVar, hsource, hfieldBinders,
    hfieldVar, hfieldSource, htarget⟩

/-- Position-indexed form of `templateTargetShape`.  The semantic recursive
mask and the rule's bound field array identify the existential field ordinal
with the reverse de Bruijn ordinal of the selected production field. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.templateTarget_eq_canonical
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let fieldPosition := A.semantics.recursivePositions[j]!
    E.templateTarget =
      VExpr.mkApps
        (.bvar (E.localDomains.length +
          (A.rule.allArgs.size - 1 - fieldPosition)))
        (E.frame.semantic.generated.localIndices.map VExpr.bvar) := by
  dsimp only
  rcases E.templateTargetShape with
    ⟨fv, fieldVar, hsource, _hfieldBinders, _hfieldVar,
      hfieldSource, htarget⟩
  let fieldPosition := A.semantics.recursivePositions[j]!
  have hfieldPosition : fieldPosition < A.rule.allArgs.size :=
    (A.semantics.decisions.selected_at j hj).1
  have hfieldPositionFVars : fieldPosition <
      A.rule.all_args_bound.fvars.length := by
    rw [A.rule.all_args_bound.length_fvars]
    exact hfieldPosition
  rcases A.rule.all_args_bound.getElem_eq_fvar fieldPosition
      hfieldPosition with ⟨_hpositionFVars, hfieldAt⟩
  have hrecursiveBang : A.rule.recursiveArgs[j]! = .fvar fv := by
    rw [getElem!_pos A.rule.recursiveArgs j hj]
    exact hsource
  have hfieldBang : A.rule.allArgs[fieldPosition]! =
      .fvar A.rule.all_args_bound.fvars[fieldPosition] :=
    (getElem!_pos A.rule.allArgs fieldPosition hfieldPosition).trans hfieldAt
  have hselected := (A.semantics.decisions.selected_at j hj).2
  have hfvExact : fv = A.rule.all_args_bound.fvars[fieldPosition] :=
    Expr.fvar.inj (hrecursiveBang.symm.trans (hselected.trans hfieldBang))
  have hfieldExact := Expr.abstractList_fvar_getElem
    A.rule.all_args_nodup fieldPosition hfieldPositionFVars (k := 0)
  rw [← hfvExact] at hfieldExact
  have hnotOuter : fv ∉
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars :=
    A.rule.all_args_outer_fresh fv <| by
      rw [hfvExact]
      exact List.getElem_mem hfieldPositionFVars
  have hfieldFullExact : (Expr.fvar fv).abstractList A.rule.binders =
      .bvar (A.rule.allArgs.size - 1 - fieldPosition) := by
    unfold BoundGeneratedRecursorRule.binders
    rw [Expr.abstractList_append,
      Expr.abstractList_fvar_of_not_mem hnotOuter]
    simpa [A.rule.all_args_bound.length_fvars] using hfieldExact
  have hfieldVarExact : fieldVar =
      A.rule.allArgs.size - 1 - fieldPosition :=
    Expr.bvar.inj (hfieldSource.symm.trans hfieldFullExact)
  simpa [fieldPosition, hfieldVarExact] using htarget

/-- Strict, witness-free residual translation of the eta-expanded recursive
field template.  This packages the retained derivation with its forced
position-indexed target, so downstream telescope reconstruction no longer
mentions the intermediate `templateTarget` witness. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.templateResidualTranslationCanonical
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let fieldPosition := A.semantics.recursivePositions[j]!
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMajor A.rule.binders)
      (VExpr.mkApps
        (.bvar (E.localDomains.length +
          (A.rule.allArgs.size - 1 - fieldPosition)))
        (E.frame.semantic.generated.localIndices.map VExpr.bvar)) := by
  dsimp only
  rw [← E.templateTarget_eq_canonical]
  exact E.template_residual_translation

/-- The checked local forall telescope supplies the strict domain
translations for the eta-expanded recursive-field lambda over the same local
selection. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.templateTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((E.frame.semantic.generated.current.lctx.mkLambda
          E.frame.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            E.frame.semantic.generated.localArgs)).abstractList
        A.rule.binders)
      (VExpr.wrapLams E.localDomains E.templateTarget) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let selection :=
    E.frame.semantic.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      E.frame.semantic.generated.current_wf
  have Hsame := (selection.sameForallLambdaPrefix
    E.frame.semantic.generated.arguments_bound.nodup
    (.sort (.zero : Level))
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)).abstractList A.rule.binders
  have Hforall₀ := (selection.forallTelescope
    (.sort (.zero : Level))).abstractList A.rule.binders
  have hselectionFVars : selection.fvars =
      E.frame.semantic.generated.arguments_bound.fvars := rfl
  rw [hselectionFVars] at Hforall₀
  have hsortLocal : (Expr.sort (.zero : Level)).abstractList
      E.frame.semantic.generated.arguments_bound.fvars = .sort .zero := by
    induction E.frame.semantic.generated.arguments_bound.fvars <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortLocal] at Hforall₀
  simp only [Nat.zero_add] at Hforall₀
  have hsortOuter : (Expr.sort (.zero : Level)).abstractList
      A.rule.binders E.frame.semantic.generated.localArgs.size = .sort .zero := by
    induction A.rule.binders <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortOuter] at Hforall₀
  have HforallTelescope : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size (.sort .zero) := Hforall₀
  have Hsame' : Expr.SameForallLambdaPrefix E.localDomains.length
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      ((E.frame.semantic.generated.current.lctx.mkLambda
        E.frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)).abstractList
            A.rule.binders) := by
    simpa [E.local_length] using Hsame
  have HforallTelescope' : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.localDomains.length (.sort .zero) := by
    simpa [E.local_length] using HforallTelescope
  exact Hsame'.translateLambda HforallTelescope' E.template_telescope
    rfl E.local_forall_translation (by
      simpa [equationDomains, Us, abstractForallContext_append,
        List.append_assoc] using E.template_residual_translation)

/-- Reconstruct the strict translation of the complete generated recursive
result from any translation of its eta-expanded field template in the fixed
equation context.  The template contributes only the shared lambda-domain
derivations; the actual recursive-call residual is the independently checked
one retained by `CanonicalRecursiveResultAt`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResultAt.fullTranslationOfTemplate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (templateTarget : VExpr)
    (Htemplate :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((E.frame.semantic.generated.current.lctx.mkLambda
            E.frame.semantic.generated.localArgs
            (mkAppN A.rule.recursiveArgs[j]
              E.frame.semantic.generated.localArgs)).abstractList
          A.rule.binders)
        (VExpr.wrapLams E.localDomains templateTarget)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      (VExpr.wrapLams E.localDomains E.resultBody) := by
  dsimp only at Htemplate ⊢
  exact E.source_template_prefix.symm.replaceTranslatedResidual
    E.template_telescope E.source_telescope rfl Htemplate
    (by simpa [abstractForallContext_append] using E.residual_translation)

/-- Pointwise handoff between the selected first-pass minor hypothesis and
the canonical recursive result produced by the second pass.  Both sides are
kept in one existential package: the source declaration is the exact
unconsumed production type and is translated to the selected minor domain,
while the corresponding recursive result is already closed and typed in the
fixed equation context.  The remaining RHS argument proof can therefore
focus solely on relating these two displayed types. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalResultFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ S : RecInfoMinorTypeShape,
      ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
          S.sourceFullContext S.recursiveFields S.hypotheses,
      ∃ traversal : RecInfoMinorTraversalShape,
      ∃ fieldDomains hypothesisDomains targetResidual,
      ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
      ∃ originRoot sourceType,
      ∃ O : RecInfoMinorHypothesisTypeOrigin
          hypothesisOrigins.stats hypothesisOrigins.recInfos
          originRoot S.recursiveFields[j]! sourceType,
        S.hypothesis_type_origins = some hypothesisOrigins ∧
        hypothesisOrigins.stats = stats ∧
        hypothesisOrigins.recInfos.map (·.motive) =
          H.recInfos.map (·.motive) ∧
        O.ownerIdx < H.recInfos.size ∧
        hypothesisOrigins.recInfos[O.ownerIdx]!.motive =
          H.recInfos[O.ownerIdx]!.motive ∧
        (let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          let position := A.rule.allArgs.size + j
          let motivePosition := H.params.fvars.length + O.ownerIdx
          ∃ motiveFVar,
            H.recInfos[O.ownerIdx]!.motive = .fvar motiveFVar ∧
            (Expr.fvar motiveFVar).abstractList sourceBinders position =
              .bvar (position +
                (sourceBinders.length - 1 - motivePosition))) ∧
        S.traversal = some traversal ∧
        traversal.fields = S.fields ∧
        traversal.recursiveFields = S.recursiveFields ∧
        traversal.stats = stats ∧
        traversal.parameterTail = A.semantics.parameterTail ∧
        traversal.recursivePositions = A.semantics.recursivePositions ∧
        S.recursiveFields[j]! =
          S.fields[A.semantics.recursivePositions[j]!]! ∧
        A.rule.recursiveArgs[j]! =
          A.rule.allArgs[A.semantics.recursivePositions[j]!]! ∧
        S.localIndex = i ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext ∧
        Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        D.type = sourceType ∧
        O.outerAbstractedField S.fields_bound.fvars =
          mkAppN
            (.bvar (O.args.size +
              (S.fields_bound.fvars.length - 1 -
                A.semantics.recursivePositions[j]!)))
            (O.localIndices.map Expr.bvar).toArray ∧
        E.frame.semantic.generated.outerAbstractedMajor A.rule.binders =
          mkAppN
            (.bvar (E.frame.semantic.generated.localArgs.size +
              (A.rule.allArgs.size - 1 -
                A.semantics.recursivePositions[j]!)))
            (E.frame.semantic.generated.localIndices.map Expr.bvar).toArray ∧
        E.frame.semantic.appliedFieldTarget =
          VExpr.mkApps
            (.bvar (E.frame.semantic.generated.localArgs.size +
              (A.rule.allArgs.size - 1 -
                A.semantics.recursivePositions[j]!)))
            (E.frame.semantic.generated.localIndices.map VExpr.bvar) ∧
        O.replayTrace S.fields_bound.fvars =
          E.frame.semantic.generated.replayTrace
            A.rule.all_args_bound.fvars ∧
        (O.current.lctx.mkForall O.args (.sort .zero)).abstractList
            S.fields_bound.fvars =
          (E.frame.semantic.generated.current.lctx.mkForall
              E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
            A.rule.all_args_bound.fvars ∧
        Expr.SameLambdaPrefix E.localDomains.length
          (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
          ((E.frame.semantic.generated.current.lctx.mkLambda
              E.frame.semantic.generated.localArgs
              (mkAppN A.rule.recursiveArgs[j]
                E.frame.semantic.generated.localArgs)).abstractList
            A.rule.binders) ∧
        (∀ left right,
          Expr.SameForallPrefix O.args.size
            ((O.current.lctx.mkForall O.args left).abstractList
              S.fields_bound.fvars)
            ((E.frame.semantic.generated.current.lctx.mkForall
                E.frame.semantic.generated.localArgs right).abstractList
              A.rule.all_args_bound.fvars)) ∧
        ((hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
              O.arguments_bound.fvars).abstractList
            S.fields_bound.fvars O.args.size) =
          ((((H.recInfos.map
                (fun info : AddInductive.RecInfo => info.motive))[
                E.frame.semantic.generated.ownerIdx]!).abstractList
              E.frame.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
              E.frame.semantic.generated.localArgs.size) ∧
        (((O.exposedType.getAppArgs[
              hypothesisOrigins.stats.params.size:] : Array Expr).map
            fun index =>
              (index.abstractList O.arguments_bound.fvars).abstractList
                S.fields_bound.fvars O.args.size) =
          ((E.frame.semantic.generated.exposedType.getAppArgs[
                stats.params.size:] : Array Expr).map
            fun index =>
              (index.abstractList
                E.frame.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.all_args_bound.fvars
                  E.frame.semantic.generated.localArgs.size)) ∧
        O.ownerIdx = E.frame.semantic.generated.ownerIdx ∧
        O.args.size = E.frame.semantic.generated.localArgs.size ∧
        O.outerAbstractedField S.fields_bound.fvars =
          E.frame.semantic.generated.outerAbstractedMajor A.rule.binders ∧
        O.outerAbstractedMotiveApp S.fields_bound.fvars =
          E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.all_args_bound.fvars ∧
        (∃ binding : RecursorMotiveBinding
              E.frame.semantic.current_context
              H.recInfos[E.frame.semantic.generated.ownerIdx]!
              H.elimLevel,
          ∃ evidence : RecursorMotiveTelescopeEvidence
              E.frame.semantic.current_context stats
              H.recInfos[E.frame.semantic.generated.ownerIdx]!
              binding E.frame.semantic.generated.exposedType
              E.frame.semantic.exposedTarget,
            ∃ (semanticLocalDomains semanticFieldDomains : List VExpr),
              semanticLocalDomains.length =
                  E.frame.semantic.generated.localArgs.size ∧
              semanticFieldDomains.length = A.rule.allArgs.size ∧
              E.frame.semantic.current_context.mlctx.vlctx.toCtx =
                semanticLocalDomains.reverse ++
                  semanticFieldDomains.reverse ++
                    A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
              let semanticTarget := VExpr.app
                (VExpr.mkApps binding.motiveTarget evidence.indices)
                E.frame.semantic.appliedFieldTarget
              TrExprS H.outVEnv Us
                  (abstractForallContext
                    (semanticFieldDomains ++ semanticLocalDomains)
                    A.semantics.fieldRootContext.mlctx.vlctx)
                  (O.outerAbstractedMotiveApp S.fields_bound.fvars)
                  semanticTarget ∧
                H.outVEnv.HasType Us.length
                  (abstractForallContext
                    (semanticFieldDomains ++ semanticLocalDomains)
                    A.semantics.fieldRootContext.mlctx.vlctx).toCtx
                  semanticTarget (.sort evidence.resultLevel) ∧
                TrExprS H.outVEnv Us
                  (abstractForallContext semanticFieldDomains
                    A.semantics.fieldRootContext.mlctx.vlctx)
                  ((E.frame.semantic.generated.current.lctx.mkForall
                    E.frame.semantic.generated.localArgs
                    (Expr.app
                      (mkAppN
                        H.recInfos[
                          E.frame.semantic.generated.ownerIdx]!.motive
                        E.frame.semantic.generated.exposedType.getAppArgs[
                          stats.params.size:])
                      (mkAppN A.rule.recursiveArgs[j]
                        E.frame.semantic.generated.localArgs))).abstractList
                    A.rule.all_args_bound.fvars)
                  (VExpr.wrapForalls semanticLocalDomains semanticTarget)) ∧
        (let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          let position := A.rule.allArgs.size + j
          let declarationDomain :=
            ((D.type.abstractList
                (S.hypotheses_bound.fvars.take j)).abstractList
              S.fields_bound.fvars j).abstractList sourceBinders position
          TrExprS H.outVEnv Us
            (abstractForallContext
              ((fieldDomains ++ hypothesisDomains).take position)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []))
            declarationDomain hypothesisDomains[j]!) ∧
        (let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          let position := A.rule.allArgs.size + j
          let declarationDomain :=
            ((D.type.abstractList
                (S.hypotheses_bound.fvars.take j)).abstractList
              S.fields_bound.fvars j).abstractList sourceBinders position
          ∃ hypothesisLocalDomains sourceResidual hypothesisResidual,
            hypothesisLocalDomains.length = O.args.size ∧
            Expr.ForallTelescope declarationDomain O.args.size
              sourceResidual ∧
            sourceResidual =
              (((((Expr.app
                  (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
                    O.exposedType.getAppArgs[
                      hypothesisOrigins.stats.params.size:])
                  (mkAppN S.recursiveFields[j]! O.args)).abstractList
                    O.arguments_bound.fvars).abstractList
                  (S.hypotheses_bound.fvars.take j) O.args.size).abstractList
                S.fields_bound.fvars (O.args.size + j)).abstractList
              sourceBinders (O.args.size + position)) ∧
            sourceResidual =
              ((((Expr.app
                  (mkAppN
                    (hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
                      O.arguments_bound.fvars)
                    (((O.exposedType.getAppArgs[
                        hypothesisOrigins.stats.params.size:] : Array Expr)
                      ).map fun index =>
                      index.abstractList O.arguments_bound.fvars))
                  O.abstractedField).abstractList
                (S.hypotheses_bound.fvars.take j) O.args.size).abstractList
              S.fields_bound.fvars (O.args.size + j)).abstractList
              sourceBinders (O.args.size + position)) ∧
            sourceResidual =
              ((O.outerAbstractedMotiveApp
                  S.fields_bound.fvars).liftLooseBVars'
                O.args.size j).abstractList sourceBinders
                  (O.args.size + position) ∧
            sourceResidual =
              ((O.outerAbstractedMotiveApp
                  S.fields_bound.fvars).abstractList sourceBinders
                (O.args.size + S.fields.size)).liftLooseBVars'
                  O.args.size j ∧
            sourceResidual =
              ((E.frame.semantic.generated.outerAbstractedMotiveApp
                  A.rule.all_args_bound.fvars).abstractList
                (A.rule.params_bound.fvars ++
                  A.rule.motives_bound.fvars ++
                    A.rule.minors_bound.fvars.take minorIdx)
                (E.frame.semantic.generated.localArgs.size +
                  A.rule.allArgs.size)).liftLooseBVars'
                    E.frame.semantic.generated.localArgs.size j ∧
            sourceResidual.liftLooseBVars'
                (E.frame.semantic.generated.localArgs.size +
                  A.rule.allArgs.size + j)
                (A.rule.minors_bound.fvars.drop minorIdx).length =
              (E.frame.semantic.generated.outerAbstractedMotiveApp
                A.rule.binders).liftLooseBVars'
                  E.frame.semantic.generated.localArgs.size j ∧
            (let hypothesisInner :=
                ((fieldDomains ++ hypothesisDomains).take position) ++
                  hypothesisLocalDomains
              let remainingMinorDomains := T.minors.drop minorIdx
              let liftedHypothesisInner :=
                (liftContextPrefix remainingMinorDomains.length
                  hypothesisInner.reverse).reverse
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (T.params ++ T.motives ++ T.minors ++
                    liftedHypothesisInner) [])
                ((E.frame.semantic.generated.outerAbstractedMotiveApp
                  A.rule.binders).liftLooseBVars'
                    E.frame.semantic.generated.localArgs.size j)
                (hypothesisResidual.liftN remainingMinorDomains.length
                  hypothesisInner.length)) ∧
            (let equationDomains :=
                H.parameterSuffix.parameterDecls.toCtx.reverse ++
                  T.motives ++ T.minors ++
                    (liftContextPrefix (T.motives ++ T.minors).length
                      B.fieldDomains.reverse).reverse
              let previousHypothesisDomains := hypothesisDomains.take j
              let liftedCanonicalLocals :=
                (liftContextPrefix previousHypothesisDomains.length
                  E.localDomains.reverse).reverse
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (equationDomains ++ previousHypothesisDomains ++
                    liftedCanonicalLocals) [])
                ((E.frame.semantic.generated.outerAbstractedMotiveApp
                  A.rule.binders).liftLooseBVars'
                    E.frame.semantic.generated.localArgs.size j)
                (E.resultType.liftN previousHypothesisDomains.length
                  E.localDomains.length)) ∧
            hypothesisDomains[j]! = VExpr.wrapForalls
              hypothesisLocalDomains hypothesisResidual ∧
            TrExprS H.outVEnv Us
              (abstractForallContext hypothesisLocalDomains
                (abstractForallContext
                  ((fieldDomains ++ hypothesisDomains).take position)
                  (abstractForallContext
                    (T.params ++ T.motives ++ T.minors.take minorIdx) [])))
              sourceResidual hypothesisResidual ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext hypothesisLocalDomains
                (abstractForallContext
                  ((fieldDomains ++ hypothesisDomains).take position)
                  (abstractForallContext
                    (T.params ++ T.motives ++ T.minors.take minorIdx) []))).toCtx
              hypothesisResidual) ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext
            (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              T.motives ++ T.minors ++
                (liftContextPrefix (T.motives ++ T.minors).length
                  B.fieldDomains.reverse).reverse) []).toCtx
          (VExpr.wrapLams E.localDomains E.resultBody)
          (VExpr.wrapForalls E.localDomains E.resultType) := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisDeclarationDomainAt j hj with
    ⟨T₀, S, hypothesisOrigins, traversal, fieldDomains,
      hypothesisDomains, targetResidual, D, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hsourceSelected,
      hruleSelected, hlocal, hsourceFields, hsourceHypotheses,
      hsourceContext,
      HminorSemantic,
      hfields, hhypotheses, htarget, _Hbinder, Hdomain, HdomainType,
      originRoot, sourceType, ⟨O⟩, _hdeclarationConsumed,
      hdeclarationExact⟩
  have htelescope : T₀ = T := T₀.eq T
  subst T₀
  subst stats
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  have hjTraversal : j < traversal.recursiveFields.size := by
    rw [htraversalRecursiveFields, ← S.hypotheses_size,
      hsourceHypotheses]
    exact hj
  have hjSourceRecursive : j < S.recursiveFields.size := by
    rw [← S.hypotheses_size, hsourceHypotheses]
    exact hj
  have HminorDecisions : RecursorFieldDecisions hypothesisOrigins.stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal S.fields S.recursiveFields
      traversal.recursivePositions := by
    simpa [htraversalStats, htraversalFields,
      htraversalRecursiveFields] using traversal.decisions
  have HruleDecisions : RecursorFieldDecisions hypothesisOrigins.stats
      A.semantics.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.semantics.recursivePositions := by
    rw [hparameterTail]
    exact A.semantics.decisions
  have HloopReplay : RecursorLoopUArgsReplayCompat := H.loopUArgsReplay
  unfold RecursorLoopUArgsReplayCompat at HloopReplay
  have Hreplay :
      O.replayTrace S.fields_bound.fvars =
        E.frame.semantic.generated.replayTrace
          A.rule.all_args_bound.fvars := by
    simpa only [getElem!_pos A.rule.recursiveArgs j hj] using HloopReplay
      (stats := hypothesisOrigins.stats)
      (recInfos := hypothesisOrigins.recInfos)
      (indTypes := indTypes)
      (motives := H.recInfos.map
        (fun info : AddInductive.RecInfo => info.motive))
      (minors := H.recInfos.flatMap
        (fun info : AddInductive.RecInfo => info.minors))
      (lvls := AddInductive.getRecLevels H.elimLevel
        hypothesisOrigins.stats.levels)
      (root₁ := traversal.rootContext)
      (root₂ := A.semantics.fieldRoot)
      (current₁ := traversal.terminalContext)
      (current₂ := A.rule.root)
      (originRoot := originRoot)
      (source := traversal.parameterTail)
      (terminal₁ := traversal.terminal)
      (terminal₂ := A.rule.target)
      (all₁ := S.fields)
      (recursive₁ := S.recursiveFields)
      (all₂ := A.rule.allArgs)
      (recursive₂ := A.rule.recursiveArgs)
      (positions₁ := traversal.recursivePositions)
      (positions₂ := A.semantics.recursivePositions)
      (j := j) (hj₁ := hjSourceRecursive) (hj₂ := hj)
      (sourceType := sourceType)
      (value := A.rule.recursiveResults[j]!)
      (O := O) (G := E.frame.semantic.generated)
      (fieldBinders₁ := S.fields_bound.fvars)
      (fieldBinders₂ := A.rule.all_args_bound.fvars)
      traversal.parameterTail_fvars HminorDecisions HruleDecisions
      S.fields_bound.expressions
      A.rule.all_args_bound.expressions hpositions
  have HlocalTelescopeReplay :
      (O.current.lctx.mkForall O.args (.sort .zero)).abstractList
          S.fields_bound.fvars =
        (E.frame.semantic.generated.current.lctx.mkForall
            E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars := by
    exact congrArg RecursorLoopUArgsTrace.localTelescope Hreplay
  have hownerReplay : O.ownerIdx =
      E.frame.semantic.generated.ownerIdx :=
    congrArg RecursorLoopUArgsTrace.ownerIdx Hreplay
  have hmotiveReplay :
      ((hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
            O.arguments_bound.fvars).abstractList
          S.fields_bound.fvars O.args.size) =
        ((((H.recInfos.map
              (fun info : AddInductive.RecInfo => info.motive))[
              E.frame.semantic.generated.ownerIdx]!).abstractList
            E.frame.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
            E.frame.semantic.generated.localArgs.size) := by
    exact congrArg RecursorLoopUArgsTrace.motive Hreplay
  have hindicesReplay :
      (((O.exposedType.getAppArgs[
            hypothesisOrigins.stats.params.size:] : Array Expr).map
          fun index =>
            (index.abstractList O.arguments_bound.fvars).abstractList
              S.fields_bound.fvars O.args.size) =
        ((E.frame.semantic.generated.exposedType.getAppArgs[
              hypothesisOrigins.stats.params.size:] : Array Expr).map
          fun index =>
            (index.abstractList
              E.frame.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                E.frame.semantic.generated.localArgs.size)) := by
    exact congrArg RecursorLoopUArgsTrace.indices Hreplay
  have hlocalArity : O.args.size =
      E.frame.semantic.generated.localArgs.size :=
    congrArg RecursorLoopUArgsTrace.localArity Hreplay
  have HlocalForallReplay : ∀ left right,
      Expr.SameForallPrefix O.args.size
        ((O.current.lctx.mkForall O.args left).abstractList
          S.fields_bound.fvars)
        ((E.frame.semantic.generated.current.lctx.mkForall
            E.frame.semantic.generated.localArgs right).abstractList
          A.rule.all_args_bound.fvars) := by
    intro left right
    let Oselection :=
      O.arguments_bound.toBoundFVarArray.toLocalForallSelection O.current_wf
    let Gselection :=
      E.frame.semantic.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
        E.frame.semantic.generated.current_wf
    have Hleft := (Oselection.sameForallPrefix
      O.arguments_bound.nodup left (.sort .zero)).abstractList
        S.fields_bound.fvars
    have Hright := ((Gselection.sameForallPrefix
      E.frame.semantic.generated.arguments_bound.nodup right
        (.sort .zero)).symm).abstractList A.rule.all_args_bound.fvars
    rw [HlocalTelescopeReplay] at Hleft
    exact Hleft.trans (by simpa [hlocalArity] using Hright)
  have HlocalLambdaReplay : Expr.SameLambdaPrefix E.localDomains.length
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      ((E.frame.semantic.generated.current.lctx.mkLambda
          E.frame.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            E.frame.semantic.generated.localArgs)).abstractList
        A.rule.binders) := by
    exact E.source_template_prefix
  have hownerStats : O.ownerIdx < hypothesisOrigins.stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
  have hownerRecInfos : O.ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records, ← H.cardinality.families]
    exact hownerStats
  have hownerOrigin : O.ownerIdx < hypothesisOrigins.recInfos.size := by
    have hsizes := congrArg Array.size hhypothesisRecInfos
    simp only [Array.size_map] at hsizes
    omega
  have hmotiveSnapshot :
      hypothesisOrigins.recInfos[O.ownerIdx]!.motive =
        H.recInfos[O.ownerIdx]!.motive := by
    have hget := congrArg (fun motives => motives[O.ownerIdx]!)
      hhypothesisRecInfos
    rw [getElem!_pos (hypothesisOrigins.recInfos.map (·.motive))
      O.ownerIdx (by simpa using hownerOrigin)] at hget
    rw [getElem!_pos (H.recInfos.map (·.motive)) O.ownerIdx
      (by simpa using hownerRecInfos)] at hget
    rw [getElem!_pos hypothesisOrigins.recInfos O.ownerIdx hownerOrigin,
      getElem!_pos H.recInfos O.ownerIdx hownerRecInfos]
    simpa only [Array.getElem_map] using hget
  rcases O.motive_is_fvar with
    ⟨motiveFVar, hmotiveOrigin, hmotiveOriginRoot⟩
  have hmotiveFinal : H.recInfos[O.ownerIdx]!.motive =
      .fvar motiveFVar := hmotiveSnapshot.symm.trans hmotiveOrigin
  have hownerMotiveArray : O.ownerIdx <
      (H.recInfos.map (·.motive)).size := by simpa using hownerRecInfos
  have hownerMotiveFVars : O.ownerIdx <
      H.bindings.motives.fvars.length := by
    rw [H.bindings.motives.length_fvars]
    exact hownerMotiveArray
  rcases H.bindings.motives.getElem_eq_fvar O.ownerIdx
      hownerMotiveArray with ⟨_hownerMotiveFVars, hmotiveAt⟩
  have hmotiveAt' : H.recInfos[O.ownerIdx]!.motive =
      .fvar H.bindings.motives.fvars[O.ownerIdx] := by
    rw [getElem!_pos H.recInfos O.ownerIdx hownerRecInfos]
    simpa only [Array.getElem_map] using hmotiveAt
  have hmotiveFVarExact : motiveFVar =
      H.bindings.motives.fvars[O.ownerIdx] :=
    Expr.fvar.inj (hmotiveFinal.symm.trans hmotiveAt')
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  let position := A.rule.allArgs.size + j
  let motivePosition := H.params.fvars.length + O.ownerIdx
  have hsourceBindersNodup : sourceBinders.Nodup := by
    have houter := H.bindings.outerNodup H.params H.noAlias
    have hsub :
        (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars.take
              (recursorMinorOffset indTypes owner + i) <+
          (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars :=
      (List.Sublist.refl
        (H.params.fvars ++ H.bindings.motives.fvars)).append
          (List.take_sublist _ H.bindings.flatMinors.fvars)
    simpa [sourceBinders, List.append_assoc] using houter.sublist hsub
  have hmotivePositionBound : motivePosition < sourceBinders.length := by
    simp only [sourceBinders, motivePosition, List.length_append,
      List.length_take]
    omega
  have hmotivePositionGet : sourceBinders[motivePosition] = motiveFVar := by
    dsimp only [sourceBinders, motivePosition]
    have hwithin : H.params.fvars.length + O.ownerIdx <
        (H.params.fvars ++ H.bindings.motives.fvars).length := by
      simp only [List.length_append]
      omega
    rw [List.getElem_append_left hwithin]
    simpa [hownerMotiveFVars] using hmotiveFVarExact.symm
  have hmotiveAbstract := Expr.abstractList_fvar_getElem
    hsourceBindersNodup motivePosition hmotivePositionBound (k := position)
  rw [hmotivePositionGet] at hmotiveAbstract
  have hmotiveNormal : (Expr.fvar motiveFVar).abstractList
      sourceBinders position =
      .bvar (position + (sourceBinders.length - 1 - motivePosition)) := by
    exact hmotiveAbstract
  let fieldPosition := A.semantics.recursivePositions[j]!
  have hfieldPositionRule : fieldPosition < A.rule.allArgs.size :=
    (A.semantics.decisions.selected_at j hj).1
  have hfieldPositionSource : fieldPosition < S.fields.size := by
    rw [hsourceFields]
    exact hfieldPositionRule
  have hfieldPositionFVars : fieldPosition <
      S.fields_bound.fvars.length := by
    rw [S.fields_bound.length_fvars]
    exact hfieldPositionSource
  rcases S.fields_bound.getElem_eq_fvar fieldPosition
      hfieldPositionSource with ⟨_hfieldPositionFVars, hfieldAt⟩
  have hsourceFieldExact : S.recursiveFields[j]! =
      .fvar S.fields_bound.fvars[fieldPosition] :=
    hsourceSelected.trans <| (getElem!_pos S.fields fieldPosition
      hfieldPositionSource).trans hfieldAt
  rcases O.field_fvar with ⟨sourceFVar, hsourceFVar, hsourceFVarRoot⟩
  have hsourceFVarExact : sourceFVar =
      S.fields_bound.fvars[fieldPosition] :=
    Expr.fvar.inj (hsourceFVar.symm.trans hsourceFieldExact)
  have houterField := O.outerAbstractedField_eq_bvar_at hsourceFVar
    hsourceFVarRoot S.fields_nodup hfieldPositionFVars
      hsourceFVarExact.symm
  have hrecursiveMajor := E.frame.outerAbstractedAppliedMajorOrdinal
  have hfieldBinderLength : S.fields_bound.fvars.length =
      A.rule.allArgs.size :=
    S.fields_bound.length_fvars.trans hsourceFields
  have horiginLocal : O.arguments_bound.fvars.length = O.args.size :=
    O.arguments_bound.toBoundFVarArray.length_fvars
  have hgeneratedLocal :
      E.frame.semantic.generated.arguments_bound.fvars.length =
        E.frame.semantic.generated.localArgs.size :=
    E.frame.semantic.generated.arguments_bound.toBoundFVarArray.length_fvars
  have hlocalIndices : O.localIndices =
      E.frame.semantic.generated.localIndices := by
    apply List.ext_getElem
    · simp [RecInfoMinorHypothesisTypeOrigin.localIndices,
        BoundGeneratedRecursiveCall.localIndices, horiginLocal,
        hgeneratedLocal, hlocalArity]
    · intro k hkOrigin hkGenerated
      simp [RecInfoMinorHypothesisTypeOrigin.localIndices,
        BoundGeneratedRecursiveCall.localIndices, horiginLocal,
        hgeneratedLocal, hlocalArity]
  have hmajorAlignment :
      O.outerAbstractedField S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMajor A.rule.binders := by
    rw [show O.outerAbstractedField S.fields_bound.fvars =
        mkAppN
          (.bvar (O.args.size +
            (S.fields_bound.fvars.length - 1 - fieldPosition)))
          (O.localIndices.map Expr.bvar).toArray by
        simpa [fieldPosition] using houterField]
    rw [hrecursiveMajor.1, hfieldBinderLength, hlocalArity, hlocalIndices]
  have hfieldPositionRuleFVars : fieldPosition <
      A.rule.all_args_bound.fvars.length := by
    rw [A.rule.all_args_bound.length_fvars]
    exact hfieldPositionRule
  rcases A.rule.all_args_bound.getElem_eq_fvar fieldPosition
      hfieldPositionRule with ⟨_hfieldPositionRuleFVars, hruleFieldAt⟩
  have hruleFieldExact : A.rule.recursiveArgs[j] =
      .fvar A.rule.all_args_bound.fvars[fieldPosition] := by
    rw [← getElem!_pos A.rule.recursiveArgs j hj]
    exact hruleSelected.trans <| (getElem!_pos A.rule.allArgs fieldPosition
      hfieldPositionRule).trans hruleFieldAt
  have hgeneratedMajorFields :=
    E.frame.semantic.generated.outerAbstractedMajor_eq_bvar_at
      hruleFieldExact
      (A.rule.all_args_bound.members
        A.rule.all_args_bound.fvars[fieldPosition]
        (List.getElem_mem hfieldPositionRuleFVars))
      A.rule.all_args_nodup hfieldPositionRuleFVars rfl
  have hmajorFieldAlignment :
      O.outerAbstractedField S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMajor
          A.rule.all_args_bound.fvars := by
    rw [show O.outerAbstractedField S.fields_bound.fvars =
        mkAppN
          (.bvar (O.args.size +
            (S.fields_bound.fvars.length - 1 - fieldPosition)))
          (O.localIndices.map Expr.bvar).toArray by
        simpa [fieldPosition] using houterField]
    rw [hgeneratedMajorFields, hfieldBinderLength,
      A.rule.all_args_bound.length_fvars, hlocalArity, hlocalIndices]
  have hmotiveAppAlignment :
      O.outerAbstractedMotiveApp S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars := by
    unfold RecInfoMinorHypothesisTypeOrigin.outerAbstractedMotiveApp
      BoundGeneratedRecursiveCall.outerAbstractedMotiveApp
    rw [Hreplay, hmajorFieldAlignment]
  rcases E.frame.finalFieldAbstractedNormalizedMotiveApplication with
    ⟨semanticBinding, semanticEvidence, semanticLocalDomains,
      semanticFieldDomains, hsemanticLocal, hsemanticFields,
      hsemanticContext, HsemanticGenerated, HsemanticType,
      HsemanticForall⟩
  let semanticTarget := VExpr.app
    (VExpr.mkApps semanticBinding.motiveTarget semanticEvidence.indices)
    E.frame.semantic.appliedFieldTarget
  have HsemanticOrigin : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (semanticFieldDomains ++ semanticLocalDomains)
        A.semantics.fieldRootContext.mlctx.vlctx)
      (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      semanticTarget := by
    rw [hmotiveAppAlignment]
    exact HsemanticGenerated
  let localMotiveApp :=
    (Expr.app
      (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
        O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
      (mkAppN S.recursiveFields[j]! O.args)).abstractList
        O.arguments_bound.fvars
  have hfieldClosedMotiveApp :
      localMotiveApp.abstractList S.fields_bound.fvars O.args.size =
        O.outerAbstractedMotiveApp S.fields_bound.fvars := by
    simpa [localMotiveApp] using
      O.outerAbstractedMotiveApp_eq S.fields_bound.fvars
  have HgeneratedMotiveScope :=
    E.frame.fieldAbstractedNormalizedMotiveSourceScope
  have HoriginMotiveScope :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn fun fv =>
        fv ∈ ExprArrayFVarIds hypothesisOrigins.stats.params ++
          ExprArrayFVarIds (H.recInfos.map (·.motive)) := by
    rw [hmotiveAppAlignment]
    exact HgeneratedMotiveScope
  have HoriginMotiveAvoidsHypotheses :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HoriginMotiveScope.mono
    intro fv houter hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · simpa [hhypothesisRecInfos] using houter
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HoriginMotiveClosed : Closed
      (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (O.args.size + S.fields.size) := by
    have hclosed := HsemanticOrigin.closed
    rw [abstractForallContext_bvars,
      A.semantics.fieldRootContext.mlctx.noBV, Nat.add_zero] at hclosed
    simpa [hsemanticLocal, hsemanticFields, hlocalArity,
      hsourceFields, Nat.add_comm] using hclosed
  have HlocalMotiveClosed : Closed localMotiveApp O.args.size := by
    apply Expr.closed_of_abstractList
    rw [hfieldClosedMotiveApp]
    simpa [S.fields_bound.length_fvars] using HoriginMotiveClosed
  have HlocalMotiveScope : localMotiveApp.FVarsIn fun fv =>
      fv ∈ S.fields_bound.fvars ∨
        fv ∉ S.hypotheses_bound.fvars := by
    apply FVarsIn.of_abstractList
    rw [hfieldClosedMotiveApp]
    exact HoriginMotiveAvoidsHypotheses
  have HlocalMotiveAvoidsHypotheses :
      localMotiveApp.FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HlocalMotiveScope.mono
    intro fv hfv hhypothesis
    rcases hfv with hfield | hnotHypothesis
    · exact S.hypotheses_fields_fresh fv hhypothesis hfield
    · exact hnotHypothesis hhypothesis
  let previousHypothesisFVars := S.hypotheses_bound.fvars.take j
  have hpreviousHypothesisFVarsLength :
      previousHypothesisFVars.length = j := by
    simp only [previousHypothesisFVars, List.length_take]
    have hjHypothesisFVars : j < S.hypotheses_bound.fvars.length := by
      rw [S.hypotheses_bound.length_fvars, hsourceHypotheses]
      exact hj
    omega
  have HlocalMotiveAvoidsPrevious : localMotiveApp.FVarsIn
      (fun fv => fv ∉ previousHypothesisFVars) := by
    apply HlocalMotiveAvoidsHypotheses.mono
    intro fv hnotAll hprevious
    exact hnotAll (List.mem_of_mem_take hprevious)
  have hpreviousMotiveAbstract :
      localMotiveApp.abstractList previousHypothesisFVars O.args.size =
        localMotiveApp :=
    HlocalMotiveAvoidsPrevious.abstractList_eq_self HlocalMotiveClosed
  have hfieldMotiveShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := localMotiveApp) (fvars := S.fields_bound.fvars)
    (depth := O.args.size) (extra := j)
    HlocalMotiveClosed S.fields_nodup
  have hpreviousFieldMotiveNormalization :
      (localMotiveApp.abstractList previousHypothesisFVars
          O.args.size).abstractList
        S.fields_bound.fvars (O.args.size + j) =
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).liftLooseBVars'
        O.args.size j := by
    rw [hpreviousMotiveAbstract, hfieldMotiveShift,
      hfieldClosedMotiveApp]
  subst sourceType
  have HsourceTelescope := O.sourceTelescope
  have HpreviousHypotheses := HsourceTelescope.abstractList
    (S.hypotheses_bound.fvars.take j) 0
  have HsourceFields := HpreviousHypotheses.abstractList
    S.fields_bound.fvars j
  have HsourceOuter := HsourceFields.abstractList sourceBinders position
  let declarationDomain :=
    ((D.type.abstractList
        (S.hypotheses_bound.fvars.take j)).abstractList
      S.fields_bound.fvars j).abstractList sourceBinders position
  change Expr.ForallTelescope declarationDomain O.args.size _ at HsourceOuter
  have HtypedDeclaration :=
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      HsourceOuter Hdomain HdomainType
  rcases HtypedDeclaration.toWrapForalls with
    ⟨hypothesisLocalDomains, sourceResidual, hypothesisResidual,
      hhypothesisLocalDomains, _HsourceResidual, hhypothesisDomain,
      HhypothesisResidual, HhypothesisResidualType⟩
  have hsourceResidual := _HsourceResidual.residual_eq HsourceOuter
  have hlocalMotiveApp := O.abstractedMotiveApp_eq
  have hlocalMotiveApp' :
      (Expr.app
        (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
          O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
        (mkAppN S.recursiveFields[j]! O.args)).abstractList
          O.arguments_bound.fvars =
        Expr.app
          (mkAppN
            (hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
              O.arguments_bound.fvars)
            (((O.exposedType.getAppArgs[
                hypothesisOrigins.stats.params.size:] : Array Expr)
              ).map fun index =>
              index.abstractList O.arguments_bound.fvars))
          O.abstractedField := by
    simpa [RecInfoMinorHypothesisTypeOrigin.abstractedField,
      RecInfoMinorHypothesisTypeOrigin.localIndices, List.map_ofFn,
      Function.comp_def] using hlocalMotiveApp
  have hsourceResidualStructured : sourceResidual =
      ((((Expr.app
          (mkAppN
            (hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
              O.arguments_bound.fvars)
            (((O.exposedType.getAppArgs[
                hypothesisOrigins.stats.params.size:] : Array Expr)
              ).map fun index =>
              index.abstractList O.arguments_bound.fvars))
          O.abstractedField).abstractList
        (S.hypotheses_bound.fvars.take j) O.args.size).abstractList
      S.fields_bound.fvars (O.args.size + j)).abstractList
      sourceBinders (O.args.size + position)) := by
    rw [← hlocalMotiveApp']
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hsourceResidual
  have hsourceResidualNormalized : sourceResidual =
      ((O.outerAbstractedMotiveApp
          S.fields_bound.fvars).liftLooseBVars'
        O.args.size j).abstractList sourceBinders
          (O.args.size + position) := by
    have hsourceResidualLocal : sourceResidual =
        ((localMotiveApp.abstractList previousHypothesisFVars
            O.args.size).abstractList S.fields_bound.fvars
          (O.args.size + j)).abstractList sourceBinders
            (O.args.size + position) := by
      simpa [localMotiveApp, previousHypothesisFVars, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hsourceResidual
    rw [hsourceResidualLocal, hpreviousFieldMotiveNormalization]
  have hsourceResidualOuterTransport : sourceResidual =
      ((O.outerAbstractedMotiveApp
          S.fields_bound.fvars).abstractList sourceBinders
        (O.args.size + S.fields.size)).liftLooseBVars'
          O.args.size j := by
    rw [hsourceResidualNormalized]
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (fvars := sourceBinders) (start := O.args.size)
      (cutoff := O.args.size + S.fields.size) (amount := j)
      (by omega) hsourceBindersNodup
    simpa [position, hsourceFields, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hcommute
  have hsourceParamsRule : H.params.fvars =
      A.rule.params_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.params
      A.rule.params_bound rfl
  have hsourceMotivesRule : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinorsRule : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBindersRule : sourceBinders =
      A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars ++
        A.rule.minors_bound.fvars.take
          (recursorMinorOffset indTypes owner + i) := by
    dsimp only [sourceBinders]
    rw [hsourceParamsRule, hsourceMotivesRule, hsourceMinorsRule]
  have hsourceResidualGeneratedPrefix : sourceResidual =
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars).abstractList
        (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars ++
          A.rule.minors_bound.fvars.take
            (recursorMinorOffset indTypes owner + i))
        (E.frame.semantic.generated.localArgs.size +
          A.rule.allArgs.size)).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
    rw [hsourceResidualOuterTransport, hmotiveAppAlignment,
      hsourceBindersRule, hlocalArity, hsourceFields]
  let generatedBase :=
    E.frame.semantic.generated.outerAbstractedMotiveApp
      A.rule.all_args_bound.fvars
  let generatedPrefix :=
    (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
      A.rule.minors_bound.fvars.take
        (recursorMinorOffset indTypes owner + i)
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop
    (recursorMinorOffset indTypes owner + i)
  let generatedCutoff :=
    E.frame.semantic.generated.localArgs.size + A.rule.allArgs.size
  have HgeneratedBaseClosed : Closed generatedBase generatedCutoff := by
    dsimp only [generatedBase, generatedCutoff]
    rw [← hmotiveAppAlignment, ← hlocalArity, ← hsourceFields]
    exact HoriginMotiveClosed
  have HgeneratedBaseAvoidsRemaining : generatedBase.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply HgeneratedMotiveScope.mono
    intro fv houter hremaining
    have houter' : fv ∈ A.rule.params_bound.fvars ++
        A.rule.motives_bound.fvars := by
      simpa [A.rule.params_bound.exprArrayFVarIds,
        A.rule.motives_bound.exprArrayFVarIds] using houter
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint :=
      (List.nodup_append.mp A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter' fv hminor rfl
  have hremainingAbstract : generatedBase.abstractList
      remainingMinorFVars generatedCutoff = generatedBase :=
    HgeneratedBaseAvoidsRemaining.abstractList_eq_self
      HgeneratedBaseClosed
  have hgeneratedPrefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+
        (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
          A.rule.minors_bound.fvars :=
      (List.Sublist.refl
        (A.rule.params_bound.fvars ++
          A.rule.motives_bound.fvars)).append
            (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist hsub
  have hgeneratedOuterSplit : generatedPrefix ++ remainingMinorFVars =
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars := by
    simp [generatedPrefix, remainingMinorFVars, List.append_assoc]
  have hgeneratedOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [hgeneratedOuterSplit]
    exact A.rule.outer_binders_nodup
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := generatedBase) (fvars := generatedPrefix)
    (depth := generatedCutoff) (extra := remainingMinorFVars.length)
    HgeneratedBaseClosed hgeneratedPrefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := generatedBase) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := generatedCutoff)
    hgeneratedOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hprefixToFull :
      (generatedBase.abstractList generatedPrefix generatedCutoff
        ).liftLooseBVars' generatedCutoff remainingMinorFVars.length =
      E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders := by
    have hcombined :
        (generatedBase.abstractList generatedPrefix generatedCutoff
          ).liftLooseBVars' generatedCutoff remainingMinorFVars.length =
        generatedBase.abstractList
          (generatedPrefix ++ remainingMinorFVars) generatedCutoff :=
      hprefixShift.symm.trans hprefixAppend
    rw [hgeneratedOuterSplit] at hcombined
    have hfullSource :=
      E.frame.outerAbstractedNormalizedMotiveSource
    rw [A.rule.all_args_bound.length_fvars] at hfullSource
    exact hcombined.trans <| by
      simpa [generatedBase, generatedCutoff] using hfullSource
  have hsourceResidualFullTransport :
      sourceResidual.liftLooseBVars'
          (E.frame.semantic.generated.localArgs.size +
            A.rule.allArgs.size + j) remainingMinorFVars.length =
        (E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.binders).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
    have hsourcePrefix : sourceResidual =
        (generatedBase.abstractList generatedPrefix generatedCutoff
          ).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
      simpa [generatedBase, generatedPrefix, generatedCutoff,
        List.append_assoc] using hsourceResidualGeneratedPrefix
    rw [hsourcePrefix]
    have hcommute := Expr.liftLooseBVars_comm
      (generatedBase.abstractList generatedPrefix generatedCutoff)
      remainingMinorFVars.length j generatedCutoff
      E.frame.semantic.generated.localArgs.size (by
        simp [generatedCutoff])
    rw [← hprefixToFull]
    simpa [generatedCutoff, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute.symm
  let hypothesisInner :=
    ((fieldDomains ++ hypothesisDomains).take position) ++
      hypothesisLocalDomains
  let remainingMinorDomains := T.minors.drop
    (recursorMinorOffset indTypes owner + i)
  let liftedHypothesisInner :=
    (liftContextPrefix remainingMinorDomains.length
      hypothesisInner.reverse).reverse
  have hpositionLE : position ≤
      (fieldDomains ++ hypothesisDomains).length := by
    simp only [position, List.length_append]
    rw [hfields, hhypotheses]
    omega
  have hhypothesisInnerLength : hypothesisInner.length =
      E.frame.semantic.generated.localArgs.size +
        A.rule.allArgs.size + j := by
    simp only [hypothesisInner, List.length_append]
    rw [List.length_take_of_le hpositionLE, hhypothesisLocalDomains,
      hlocalArity]
    simp only [position]
    omega
  have hremainingMinorDomainsLength : remainingMinorDomains.length =
      remainingMinorFVars.length := by
    simp only [remainingMinorDomains, remainingMinorFVars,
      List.length_drop]
    rw [T.minors_length, A.rule.minors_bound.length_fvars]
  have HhypothesisResidualFlat : TrExprS H.outVEnv Us
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors.take
            (recursorMinorOffset indTypes owner + i)) ++
          hypothesisInner) [])
      sourceResidual hypothesisResidual := by
    simpa only [hypothesisInner, abstractForallContext_append,
      List.append_assoc] using HhypothesisResidual
  have HhypothesisResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := T.params ++ T.motives ++ T.minors.take
        (recursorMinorOffset indTypes owner + i))
      (inner := hypothesisInner) H.outVEnvWF.ordered
      HhypothesisResidualFlat remainingMinorDomains
  have HhypothesisResidualFull : TrExprS H.outVEnv Us
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++
          liftedHypothesisInner) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (hypothesisResidual.liftN remainingMinorDomains.length
        hypothesisInner.length) := by
    rw [← hsourceResidualFullTransport,
      ← hremainingMinorDomainsLength, ← hhypothesisInnerLength]
    simpa [remainingMinorDomains, liftedHypothesisInner,
      List.append_assoc] using HhypothesisResidualInserted
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let previousHypothesisDomains := hypothesisDomains.take j
  let liftedCanonicalLocals :=
    (liftContextPrefix previousHypothesisDomains.length
      E.localDomains.reverse).reverse
  have hpreviousHypothesisDomainsLength :
      previousHypothesisDomains.length = j := by
    simp only [previousHypothesisDomains, List.length_take]
    rw [hhypotheses]
    omega
  have HcanonicalResultType : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa only [equationDomains] using E.result_type_translation
  have HcanonicalResultTypeInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.ordered HcanonicalResultType previousHypothesisDomains
  have HcanonicalResultTypeFull : TrExprS H.outVEnv Us
      (abstractForallContext
        (equationDomains ++ previousHypothesisDomains ++
          liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (E.resultType.liftN previousHypothesisDomains.length
        E.localDomains.length) := by
    simpa [liftedCanonicalLocals, hpreviousHypothesisDomainsLength,
      E.local_length] using HcanonicalResultTypeInserted
  exact ⟨S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, targetResidual, D, originRoot, D.type, O,
    hhypothesisOrigins, rfl, hhypothesisRecInfos,
    hownerRecInfos, hmotiveSnapshot,
    ⟨motiveFVar, hmotiveFinal, hmotiveNormal⟩,
    htraversal, htraversalFields,
    htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
    hsourceSelected, hruleSelected, hlocal, hsourceFields,
    hsourceHypotheses, hsourceContext, HminorSemantic, hfields, hhypotheses,
    htarget,
    rfl, by simpa [fieldPosition] using houterField,
    hrecursiveMajor.1, hrecursiveMajor.2, Hreplay,
    HlocalTelescopeReplay, HlocalLambdaReplay, HlocalForallReplay,
    hmotiveReplay,
    hindicesReplay, hownerReplay, hlocalArity, hmajorAlignment,
    hmotiveAppAlignment,
    ⟨semanticBinding, semanticEvidence, semanticLocalDomains,
      semanticFieldDomains, hsemanticLocal, hsemanticFields,
      hsemanticContext, HsemanticOrigin, HsemanticType,
      HsemanticForall⟩,
    Hdomain,
    ⟨hypothesisLocalDomains, sourceResidual, hypothesisResidual,
      hhypothesisLocalDomains, _HsourceResidual, by
        simpa [sourceBinders, position, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hsourceResidual,
      by
        simpa [sourceBinders, position, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hsourceResidualStructured,
      by
        simpa [sourceBinders, position] using hsourceResidualNormalized,
      by
        simpa [sourceBinders] using hsourceResidualOuterTransport,
      by
        simpa using hsourceResidualGeneratedPrefix,
      by
        simpa [remainingMinorFVars] using hsourceResidualFullTransport,
      by
        simpa [hypothesisInner, remainingMinorDomains,
          liftedHypothesisInner] using HhypothesisResidualFull,
      by
        simpa [equationDomains, previousHypothesisDomains,
          liftedCanonicalLocals] using HcanonicalResultTypeFull,
      hhypothesisDomain,
      HhypothesisResidual, HhypothesisResidualType⟩,
    E.closed_typing⟩

/-- Compact, synchronized interface to the dependent type comparison hidden
inside `finalSelectedMinorHypothesisCanonicalResultFrame`.  The installed
hypothesis residual and the canonical result type translate the very same
source motive application, with the exact telescope, narrow field frame, and
canonical-result witness supplied by the caller.  The remaining induction
step only has to relate the two displayed anonymous contexts. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalTranslationPair
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ fieldDomains hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
    ∃ hypothesisLocalDomains : List VExpr,
    ∃ hypothesisResidual : VExpr,
      fieldDomains.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      T.minors[minorIdx]! = VExpr.wrapForalls
        (fieldDomains ++ hypothesisDomains) targetResidual ∧
      hypothesisLocalDomains.length = E.localDomains.length ∧
      hypothesisDomains[j]! = VExpr.wrapForalls
        hypothesisLocalDomains hypothesisResidual ∧
      (let position := A.rule.allArgs.size + j
        let hypothesisInner :=
          ((fieldDomains ++ hypothesisDomains).take position) ++
            hypothesisLocalDomains
        let remainingMinorDomains := T.minors.drop minorIdx
        let liftedHypothesisInner :=
          (liftContextPrefix remainingMinorDomains.length
            hypothesisInner.reverse).reverse
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors ++
              liftedHypothesisInner) [])
          ((E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.binders).liftLooseBVars'
              E.frame.semantic.generated.localArgs.size j)
          (hypothesisResidual.liftN remainingMinorDomains.length
            hypothesisInner.length)) ∧
      (let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++
            T.motives ++ T.minors ++
              (liftContextPrefix (T.motives ++ T.minors).length
                B.fieldDomains.reverse).reverse
        let previousHypothesisDomains := hypothesisDomains.take j
        let liftedCanonicalLocals :=
          (liftContextPrefix previousHypothesisDomains.length
            E.localDomains.reverse).reverse
        TrExprS H.outVEnv Us
          (abstractForallContext
            (equationDomains ++ previousHypothesisDomains ++
              liftedCanonicalLocals) [])
          ((E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.binders).liftLooseBVars'
              E.frame.semantic.generated.localArgs.size j)
          (E.resultType.liftN previousHypothesisDomains.length
            E.localDomains.length)) ∧
      H.outVEnv.HasType Us.length
        (abstractForallContext
          (H.parameterSuffix.parameterDecls.toCtx.reverse ++
            T.motives ++ T.minors ++
              (liftContextPrefix (T.motives ++ T.minors).length
                B.fieldDomains.reverse).reverse) []).toCtx
        (VExpr.wrapLams E.localDomains E.resultBody)
        (VExpr.wrapForalls E.localDomains E.resultType) := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisCanonicalResultFrame j hj B T E with
    ⟨_S, _hypothesisOrigins, _traversal, fieldDomains,
      hypothesisDomains, targetResidual, _D, _originRoot, _sourceType, _O,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      hownerRecInfos, _hmotiveSnapshot, _hmotivePosition,
      _htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, _hparameterTail, _hpositions,
      _hsourceSelected, _hruleSelected, _hlocal, hsourceFields,
      hsourceHypotheses, _hsourceContext, _HminorSemantic,
      hfields, hhypotheses, htarget, _hdeclarationType,
      _houterField, _hmajorOuter, _hmajorApplied, _Hreplay,
      _HlocalTelescopeReplay, _HlocalLambdaReplay, _HlocalForallReplay,
      _hmotiveReplay, _hindicesReplay, hownerReplay, hlocalArity,
      _hmajorAlignment, _hmotiveAppAlignment, _Hsemantic,
      _Hdomain, Hresiduals, Htyping⟩
  rcases Hresiduals with
    ⟨hypothesisLocalDomains, _sourceResidual, hypothesisResidual,
      hhypothesisLocalDomains, _HsourceTelescope,
      _hsourceResidual, _hsourceResidualStructured,
      _hsourceResidualNormalized, _hsourceResidualOuter,
      _hsourceResidualGenerated, _hsourceResidualFull,
      HhypothesisResidualFull, HcanonicalResultTypeFull,
      hhypothesisDomain, _HhypothesisResidual,
      _HhypothesisResidualType⟩
  have hlocal : hypothesisLocalDomains.length = E.localDomains.length := by
    exact hhypothesisLocalDomains.trans <|
      hlocalArity.trans E.local_length.symm
  exact ⟨fieldDomains, hypothesisDomains, targetResidual,
    hypothesisLocalDomains, hypothesisResidual, hfields, hhypotheses,
    htarget, hlocal, hhypothesisDomain, HhypothesisResidualFull,
    HcanonicalResultTypeFull, Htyping⟩

/-- The exact first-pass and second-pass higher-order local telescopes share
one concrete forall prefix.  This is the source-side half of the dependent
context induction; `finalSelectedMinorHypothesisCanonicalTranslationPair`
supplies the corresponding strict target translations.  Both interfaces are
indexed by the same caller-selected `T`, `B`, and `E`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalLocalPrefix
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ S : RecInfoMinorTypeShape,
    ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
        S.sourceFullContext S.recursiveFields S.hypotheses,
    ∃ fieldDomains hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
    ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
    ∃ originRoot sourceType,
    ∃ O : RecInfoMinorHypothesisTypeOrigin
        hypothesisOrigins.stats hypothesisOrigins.recInfos
        originRoot S.recursiveFields[j]! sourceType,
      fieldDomains.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      T.minors[minorIdx]! = VExpr.wrapForalls
        (fieldDomains ++ hypothesisDomains) targetResidual ∧
      D.type = sourceType ∧
      O.args.size = E.localDomains.length ∧
      ∀ left right,
        Expr.SameForallPrefix O.args.size
          ((O.current.lctx.mkForall O.args left).abstractList
            S.fields_bound.fvars)
          ((E.frame.semantic.generated.current.lctx.mkForall
              E.frame.semantic.generated.localArgs right).abstractList
            A.rule.all_args_bound.fvars) := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisCanonicalResultFrame j hj B T E with
    ⟨S, hypothesisOrigins, _traversal, fieldDomains,
      hypothesisDomains, targetResidual, D, originRoot, sourceType, O,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      _hownerRecInfos, _hmotiveSnapshot, _hmotivePosition,
      _htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, _hparameterTail, _hpositions,
      _hsourceSelected, _hruleSelected, _hlocal, hsourceFields,
      hsourceHypotheses, _hsourceContext, _HminorSemantic,
      hfields, hhypotheses, htarget, hdeclarationType,
      _houterField, _hmajorOuter, _hmajorApplied, _Hreplay,
      _HlocalTelescopeReplay, _HlocalLambdaReplay, HlocalForallReplay,
      _hmotiveReplay, _hindicesReplay, hownerReplay, hlocalArity,
      _hmajorAlignment, _hmotiveAppAlignment, _Hsemantic,
      _Hdomain, _Hresiduals, _Htyping⟩
  exact ⟨S, hypothesisOrigins, fieldDomains, hypothesisDomains,
    targetResidual, D, originRoot, sourceType, O, hfields, hhypotheses,
    htarget, hdeclarationType,
    hlocalArity.trans E.local_length.symm, HlocalForallReplay⟩

/-- Whole-domain form of the synchronized first-pass/second-pass comparison.
The selected installed hypothesis is transported past the remaining minors;
the canonical recursive-result domain is transported past the already
consumed hypotheses.  Both targets expose their exact dependent local
domain lists, ready for `SameForallPrefix.translatedContextsExact`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalWholeDomains
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.CanonicalRecursiveResultAt T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ S : RecInfoMinorTypeShape,
    ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
        S.sourceFullContext S.recursiveFields S.hypotheses,
    ∃ fieldDomains hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
    ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
    ∃ originRoot sourceType,
    ∃ O : RecInfoMinorHypothesisTypeOrigin
        hypothesisOrigins.stats hypothesisOrigins.recInfos
        originRoot S.recursiveFields[j]! sourceType,
    ∃ hypothesisLocalDomains : List VExpr,
    ∃ hypothesisResidual : VExpr,
      let position := A.rule.allArgs.size + j
      let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take minorIdx
      let declarationDomain :=
        ((D.type.abstractList
            (S.hypotheses_bound.fvars.take j)).abstractList
          S.fields_bound.fvars j).abstractList sourceBinders position
      let prior := (fieldDomains ++ hypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let previous := hypothesisDomains.take j
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let liftedFields :=
        (liftContextPrefix remaining.length fieldDomains.reverse).reverse
      let liftedPrevious :=
        (liftContextPrefixAt remaining.length fieldDomains.length
          previous.reverse).reverse
      let liftedHypothesisLocals :=
        (liftContextPrefixAt remaining.length position
          hypothesisLocalDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let motiveApp := Expr.app
        (mkAppN
          (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
          E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)
      let liftedCanonicalLocals :=
        (liftContextPrefix liftedPrevious.length
          E.localDomains.reverse).reverse
      let residualSource :=
        (E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.binders).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j
      fieldDomains.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      T.minors[minorIdx]! = VExpr.wrapForalls
        (fieldDomains ++ hypothesisDomains) targetResidual ∧
      liftedPrior = liftedFields ++ liftedPrevious ∧
      hypothesisLocalDomains.length = E.localDomains.length ∧
      hypothesisDomains[j]! =
        VExpr.wrapForalls hypothesisLocalDomains hypothesisResidual ∧
      TrExprS H.outVEnv Us
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors ++ liftedPrior) [])
        (declarationDomain.liftLooseBVars' position remaining.length)
        (VExpr.wrapForalls liftedHypothesisLocals
          (hypothesisResidual.liftN remaining.length
            (position + hypothesisLocalDomains.length))) ∧
      TrExprS H.outVEnv Us
        (abstractForallContext (equationDomains ++ liftedPrevious) [])
        (((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs motiveApp).abstractList
            A.rule.binders).liftLooseBVars' 0 liftedPrevious.length)
        (VExpr.wrapForalls liftedCanonicalLocals
          (E.resultType.liftN liftedPrevious.length
            E.localDomains.length)) ∧
      Expr.SameForallPrefix E.localDomains.length
        (declarationDomain.liftLooseBVars' position remaining.length)
        (((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs motiveApp).abstractList
            A.rule.binders).liftLooseBVars' 0 liftedPrevious.length) ∧
      TrExprS H.outVEnv Us
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors ++ liftedPrior ++
            liftedHypothesisLocals) [])
        residualSource
        (hypothesisResidual.liftN remaining.length
          (position + hypothesisLocalDomains.length)) ∧
      TrExprS H.outVEnv Us
        (abstractForallContext
          (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) [])
        residualSource
        (E.resultType.liftN liftedPrevious.length E.localDomains.length) ∧
      H.outVEnv.IsType Us.length
        (abstractForallContext
          (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) []).toCtx
        (E.resultType.liftN liftedPrevious.length E.localDomains.length) := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisCanonicalResultFrame j hj B T E with
    ⟨S, hypothesisOrigins, _traversal, fieldDomains,
      hypothesisDomains, targetResidual, D, originRoot, sourceType, O,
      _hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos,
      hownerRecInfos, _hmotiveSnapshot, _hmotivePosition,
      _htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, _hparameterTail, _hpositions,
      _hsourceSelected, _hruleSelected, _hlocal, hsourceFields,
      hsourceHypotheses, _hsourceContext, _HminorSemantic,
      hfields, hhypotheses, htarget, hdeclarationType,
      _houterField, _hmajorOuter, _hmajorApplied, _Hreplay,
      _HlocalTelescopeReplay, _HlocalLambdaReplay, HlocalForallReplay,
      _hmotiveReplay, _hindicesReplay, _hownerReplay, hlocalArity,
      _hmajorAlignment, hmotiveAppAlignment, Hsemantic,
      Hdomain, Hresiduals, _Htyping⟩
  rcases Hresiduals with
    ⟨hypothesisLocalDomains, _sourceResidual, hypothesisResidual,
      hhypothesisLocalDomains, _HsourceTelescope,
      _hsourceResidual, _hsourceResidualStructured,
      _hsourceResidualNormalized, _hsourceResidualOuter,
      _hsourceResidualGenerated, _hsourceResidualFull,
      HhypothesisResidualFull, _HcanonicalResultTypeFull,
      hhypothesisDomain, _HhypothesisResidual,
      _HhypothesisResidualType⟩
  let minorIdx := recursorMinorOffset indTypes owner + i
  let position := A.rule.allArgs.size + j
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let declarationDomain :=
    ((D.type.abstractList
        (S.hypotheses_bound.fvars.take j)).abstractList
      S.fields_bound.fvars j).abstractList sourceBinders position
  let prior := (fieldDomains ++ hypothesisDomains).take position
  let remaining := T.minors.drop minorIdx
  let previous := hypothesisDomains.take j
  let liftedPrior :=
    (liftContextPrefix remaining.length prior.reverse).reverse
  let liftedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let liftedPrevious :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      previous.reverse).reverse
  let liftedHypothesisLocals :=
    (liftContextPrefixAt remaining.length position
      hypothesisLocalDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix liftedPrevious.length
      E.localDomains.reverse).reverse
  have hpositionLE : position ≤
      (fieldDomains ++ hypothesisDomains).length := by
    simp only [position, List.length_append]
    rw [hfields, hhypotheses]
    omega
  have hprior : prior.length = position := by
    simp [prior, List.length_take_of_le hpositionLE]
  have hpriorSplit : prior = fieldDomains ++ previous := by
    unfold prior position previous
    rw [← hfields, List.take_length_add_append]
  have hpreviousLength₀ : previous.length = j := by
    simp only [previous, List.length_take]
    rw [hhypotheses]
    omega
  have hliftedPreviousLength₀ : liftedPrevious.length = j := by
    simp [liftedPrevious, hpreviousLength₀]
  have hliftedPriorSplit : liftedPrior = liftedFields ++ liftedPrevious := by
    simpa [liftedPrior, liftedFields, liftedPrevious, hpriorSplit] using
      liftContextPrefix_reverse_append remaining.length fieldDomains previous
  have HdomainFlat : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors.take minorIdx) ++ prior) [])
      declarationDomain (VExpr.wrapForalls
        hypothesisLocalDomains hypothesisResidual) := by
    rw [hhypothesisDomain] at Hdomain
    simpa [minorIdx, position, sourceBinders, declarationDomain, prior,
      abstractForallContext_append, List.append_assoc] using Hdomain
  have Hinstalled₀ :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := T.params ++ T.motives ++ T.minors.take minorIdx)
      (inner := prior) H.outVEnvWF.ordered HdomainFlat remaining
  have Hinstalled : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ liftedPrior) [])
      (declarationDomain.liftLooseBVars' position remaining.length)
      (VExpr.wrapForalls liftedHypothesisLocals
        (hypothesisResidual.liftN remaining.length
          (position + hypothesisLocalDomains.length))) := by
    simpa [remaining, liftedPrior, liftedHypothesisLocals, hprior,
      VExpr.liftN_wrapForalls, List.append_assoc] using Hinstalled₀
  have Hcanonical := E.fullForallTranslationAfter liftedPrevious
  have hlocalLength : hypothesisLocalDomains.length = E.localDomains.length :=
    hhypothesisLocalDomains.trans (hlocalArity.trans E.local_length.symm)
  have hliftedHypothesisInner :
      (liftContextPrefix remaining.length
        (prior ++ hypothesisLocalDomains).reverse).reverse =
        liftedPrior ++ liftedHypothesisLocals := by
    simpa [liftedPrior, liftedHypothesisLocals, hprior] using
      liftContextPrefix_reverse_append remaining.length prior
        hypothesisLocalDomains
  have HinstalledResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ liftedPrior ++
          liftedHypothesisLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (hypothesisResidual.liftN remaining.length
        (position + hypothesisLocalDomains.length)) := by
    have HinstalledResidual₀ : TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors ++
            (liftContextPrefix remaining.length
              (prior ++ hypothesisLocalDomains).reverse).reverse) [])
        ((E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.binders).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j)
        (hypothesisResidual.liftN remaining.length
          (prior ++ hypothesisLocalDomains).length) := by
      simpa only [minorIdx, position, prior, remaining] using
        HhypothesisResidualFull
    rw [hliftedHypothesisInner, List.length_append, hprior] at HinstalledResidual₀
    simpa [List.append_assoc] using HinstalledResidual₀
  have HcanonicalResidual₀ : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains] using E.result_type_translation
  have HcanonicalResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.ordered HcanonicalResidual₀ liftedPrevious
  have HcanonicalResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size liftedPrevious.length)
      (E.resultType.liftN liftedPrevious.length E.localDomains.length) := by
    simpa [liftedCanonicalLocals, E.local_length, List.append_assoc] using
      HcanonicalResidualInserted
  have Wcanonical : Ctx.LiftN liftedPrevious.length E.localDomains.length
      (abstractForallContext
        (equationDomains ++ E.localDomains) []).toCtx
      (abstractForallContext
        (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) []).toCtx := by
    have W := Ctx.LiftN.insertAfterPrefix E.localDomains.reverse
      liftedPrevious.reverse equationDomains.reverse
    simpa [liftedCanonicalLocals, List.reverse_append,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc] using W
  have HcanonicalResidualType : H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) []).toCtx
      (E.resultType.liftN liftedPrevious.length E.localDomains.length) := by
    exact E.result_type_isType.weakN H.outVEnvWF.ordered Wcanonical
  let originMotiveApp := Expr.app
    (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
      O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
    (mkAppN S.recursiveFields[j]! O.args)
  let generatedMotiveApp := Expr.app
    (mkAppN
      H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let originFieldSource :=
    D.type.abstractList S.fields_bound.fvars
  let generatedFieldSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
        A.rule.all_args_bound.fvars
  have horiginSourceShape : D.type =
      O.current.lctx.mkForall O.args originMotiveApp := by
    exact hdeclarationType.trans (by simpa [originMotiveApp] using O.type_eq)
  have HfieldPrefix : Expr.SameForallPrefix O.args.size
      originFieldSource generatedFieldSource := by
    have Hprefix := HlocalForallReplay originMotiveApp generatedMotiveApp
    dsimp only [originFieldSource, generatedFieldSource]
    rw [horiginSourceShape]
    simpa [originMotiveApp, generatedMotiveApp] using Hprefix
  have HoriginTelescope : Expr.ForallTelescope originFieldSource O.args.size
      (O.outerAbstractedMotiveApp S.fields_bound.fvars) := by
    have Hsource := O.sourceTelescope.abstractList
      S.fields_bound.fvars 0
    have hresidual :
        (originMotiveApp.abstractList
          O.arguments_bound.fvars).abstractList
            S.fields_bound.fvars O.args.size =
          O.outerAbstractedMotiveApp S.fields_bound.fvars := by
      simpa [originMotiveApp] using
        O.outerAbstractedMotiveApp_eq S.fields_bound.fvars
    have Hsource' : Expr.ForallTelescope
        (sourceType.abstractList S.fields_bound.fvars) O.args.size
        ((originMotiveApp.abstractList
          O.arguments_bound.fvars).abstractList
            S.fields_bound.fvars O.args.size) := by
      simpa [originMotiveApp] using Hsource
    rw [hresidual] at Hsource'
    simpa [originFieldSource, hdeclarationType] using Hsource'
  have HgeneratedNeutralScope :=
    E.frame.fieldAbstractedNeutralLocalForallSourceScope B
  have HgeneratedNeutralAvoidsHypotheses :
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars).FVarsIn
            (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HgeneratedNeutralScope.mono
    intro fv hparam hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · apply List.mem_append_left
      simpa [hhypothesisStats] using hparam
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HgeneratedMotiveScope :=
    E.frame.fieldAbstractedNormalizedMotiveSourceScope
  have HoriginMotiveScope :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn fun fv =>
        fv ∈ ExprArrayFVarIds stats.params ++
          ExprArrayFVarIds (H.recInfos.map (·.motive)) := by
    rw [hmotiveAppAlignment]
    exact HgeneratedMotiveScope
  have HoriginMotiveAvoidsHypotheses :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HoriginMotiveScope.mono
    intro fv houter hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · simpa [hhypothesisStats, hhypothesisRecInfos] using houter
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HneutralPrefix : Expr.SameForallPrefix O.args.size
      originFieldSource
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars) := by
    have Hprefix := HlocalForallReplay originMotiveApp (.sort .zero)
    dsimp only [originFieldSource]
    rw [horiginSourceShape]
    simpa [originMotiveApp] using Hprefix
  have HoriginFieldAvoidsHypotheses : originFieldSource.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) :=
    HneutralPrefix.leftFVarsIn HoriginTelescope
      HgeneratedNeutralAvoidsHypotheses HoriginMotiveAvoidsHypotheses
  have HDomainAvoidsHypotheses : D.type.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    have Hraw := FVarsIn.of_abstractList HoriginFieldAvoidsHypotheses
    apply Hraw.mono
    intro fv hfv hhypothesis
    rcases hfv with hfield | hnotHypothesis
    · exact S.hypotheses_fields_fresh fv hhypothesis hfield
    · exact hnotHypothesis hhypothesis
  rcases Hsemantic with
    ⟨_semanticBinding, _semanticEvidence, semanticLocalDomains,
      semanticFieldDomains, hsemanticLocal, hsemanticFields,
      _hsemanticContext, HsemanticOrigin, _HsemanticType,
      HsemanticForall⟩
  have HgeneratedFieldClosed : Closed generatedFieldSource
      A.rule.allArgs.size := by
    have hclosed := HsemanticForall.closed
    rw [abstractForallContext_bvars,
      A.semantics.fieldRootContext.mlctx.noBV, Nat.add_zero] at hclosed
    simpa [generatedFieldSource, generatedMotiveApp, hsemanticFields] using
      hclosed
  have HoriginMotiveClosed : Closed
      (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (A.rule.allArgs.size + O.args.size) := by
    have hclosed := HsemanticOrigin.closed
    rw [abstractForallContext_bvars,
      A.semantics.fieldRootContext.mlctx.noBV, Nat.add_zero] at hclosed
    simpa [hsemanticLocal, hsemanticFields, hlocalArity,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hclosed
  have HoriginFieldClosed : Closed originFieldSource
      A.rule.allArgs.size := by
    exact HfieldPrefix.leftClosed HoriginTelescope HgeneratedFieldClosed
      (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        HoriginMotiveClosed)
  have HDomainClosed : Closed D.type 0 := by
    apply Expr.closed_of_abstractList
      (e := D.type) (fvars := S.fields_bound.fvars) (depth := 0)
    simpa [originFieldSource, S.fields_bound.length_fvars,
      hsourceFields] using HoriginFieldClosed
  let previousHypothesisFVars := S.hypotheses_bound.fvars.take j
  have hpreviousHypothesisFVarsLength : previousHypothesisFVars.length = j := by
    simp only [previousHypothesisFVars, List.length_take]
    have hjHypothesisFVars : j < S.hypotheses_bound.fvars.length := by
      rw [S.hypotheses_bound.length_fvars, hsourceHypotheses]
      exact hj
    omega
  have HDomainAvoidsPrevious : D.type.FVarsIn
      (fun fv => fv ∉ previousHypothesisFVars) := by
    apply HDomainAvoidsHypotheses.mono
    intro fv hnotAll hprevious
    exact hnotAll (List.mem_of_mem_take hprevious)
  have hpreviousDomainAbstract :
      D.type.abstractList previousHypothesisFVars = D.type :=
    HDomainAvoidsPrevious.abstractList_eq_self HDomainClosed
  have hfieldDomainShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := D.type) (fvars := S.fields_bound.fvars)
    (depth := 0) (extra := j) HDomainClosed S.fields_nodup
  have hleftFieldNormalization :
      (D.type.abstractList previousHypothesisFVars).abstractList
          S.fields_bound.fvars j =
        originFieldSource.liftLooseBVars' 0 j := by
    rw [hpreviousDomainAbstract]
    simpa [originFieldSource] using hfieldDomainShift
  let generatedNeutralSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
  let Gselection :=
    E.frame.semantic.generated.arguments_bound.toBoundFVarArray.toLocalForallSelection
      E.frame.semantic.generated.current_wf
  have HgeneratedActualNeutral : Expr.SameForallPrefix
      E.frame.semantic.generated.localArgs.size
      generatedFieldSource generatedNeutralSource := by
    have Hprefix := (Gselection.sameForallPrefix
      E.frame.semantic.generated.arguments_bound.nodup
      generatedMotiveApp (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
    simpa [generatedFieldSource, generatedNeutralSource,
      generatedMotiveApp, Gselection] using Hprefix
  have HgeneratedTelescope : Expr.ForallTelescope generatedFieldSource
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars) := by
    have Hsource :=
      E.frame.semantic.generated.arguments_bound.toBoundFVarArray.mkForall_forallTelescope
        E.frame.semantic.generated.current_wf generatedMotiveApp
    have Hsource' := Hsource.abstractList
      A.rule.all_args_bound.fvars 0
    have hresidual :=
      E.frame.semantic.generated.outerAbstractedMotiveApp_eq
        A.rule.all_args_bound.fvars
    have hgeneratedOwnerRecInfos :
        E.frame.semantic.generated.ownerIdx < H.recInfos.size := by
      simpa [H.generated.length] using E.frame.entry_lt
    have hselectedMotive :
        (H.recInfos.map (·.motive))[
            E.frame.semantic.generated.ownerIdx]! =
          H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive := by
      rw [getElem!_pos (H.recInfos.map (·.motive))
          E.frame.semantic.generated.ownerIdx
            (by simpa using hgeneratedOwnerRecInfos),
        getElem!_pos H.recInfos E.frame.semantic.generated.ownerIdx
          hgeneratedOwnerRecInfos]
      simp
    rw [hselectedMotive] at hresidual
    have hresidual' :
        (generatedMotiveApp.abstractList
          E.frame.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
              E.frame.semantic.generated.localArgs.size =
          E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.all_args_bound.fvars := by
      simpa [generatedMotiveApp] using hresidual
    simpa [generatedFieldSource, Nat.zero_add, hresidual'] using Hsource'
  have HgeneratedNeutralScope' : generatedNeutralSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
    simpa [generatedNeutralSource] using HgeneratedNeutralScope
  have HgeneratedNeutralOuterScope : generatedNeutralSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (H.recInfos.map (·.motive))) := by
    exact HgeneratedNeutralScope'.mono fun fv hfv =>
      List.mem_append_left _ hfv
  have HgeneratedFieldOuterScope : generatedFieldSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (H.recInfos.map (·.motive))) :=
    HgeneratedActualNeutral.leftFVarsIn HgeneratedTelescope
      HgeneratedNeutralOuterScope HgeneratedMotiveScope
  let generatedOuter :=
    A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let generatedPrefix := generatedOuter ++
    A.rule.minors_bound.fvars.take minorIdx
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
  have HgeneratedFieldScope : generatedFieldSource.FVarsIn
      (fun fv => fv ∈ generatedOuter) := by
    simpa [generatedOuter, A.rule.params_bound.exprArrayFVarIds,
      A.rule.motives_bound.exprArrayFVarIds] using HgeneratedFieldOuterScope
  have HgeneratedFieldAvoidsRemaining : generatedFieldSource.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply HgeneratedFieldScope.mono
    intro fv houter hremaining
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint :=
      (List.nodup_append.mp A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter fv hminor rfl
  have hsourceParamsRule : H.params.fvars =
      A.rule.params_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.params
      A.rule.params_bound rfl
  have hsourceMotivesRule : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinorsRule : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBindersRule : sourceBinders = generatedPrefix := by
    dsimp only [sourceBinders, generatedPrefix, generatedOuter]
    rw [hsourceParamsRule, hsourceMotivesRule, hsourceMinorsRule]
  have hremainingLength : remaining.length = remainingMinorFVars.length := by
    simp only [remaining, remainingMinorFVars, List.length_drop]
    rw [T.minors_length, A.rule.minors_bound.length_fvars]
  have hgeneratedPrefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+
        generatedOuter ++ A.rule.minors_bound.fvars :=
      (List.Sublist.refl generatedOuter).append
        (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist <| by
      simpa [generatedPrefix, generatedOuter, List.append_assoc] using hsub
  have hgeneratedOuterSplit : generatedPrefix ++ remainingMinorFVars =
      generatedOuter ++ A.rule.minors_bound.fvars := by
    simp [generatedPrefix, generatedOuter, remainingMinorFVars,
      List.append_assoc]
  have hgeneratedOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [hgeneratedOuterSplit]
    simpa [generatedOuter, List.append_assoc] using
      A.rule.outer_binders_nodup
  have hremainingAbstract : generatedFieldSource.abstractList
      remainingMinorFVars A.rule.allArgs.size = generatedFieldSource :=
    HgeneratedFieldAvoidsRemaining.abstractList_eq_self
      HgeneratedFieldClosed
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := generatedFieldSource) (fvars := generatedPrefix)
    (depth := A.rule.allArgs.size) (extra := remainingMinorFVars.length)
    HgeneratedFieldClosed hgeneratedPrefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := generatedFieldSource) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := A.rule.allArgs.size)
    hgeneratedOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hgeneratedOuterFull :
      (generatedFieldSource.abstractList generatedPrefix
        A.rule.allArgs.size).liftLooseBVars'
          A.rule.allArgs.size remainingMinorFVars.length =
        (E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
            A.rule.binders := by
    have hcombined :
        (generatedFieldSource.abstractList generatedPrefix
          A.rule.allArgs.size).liftLooseBVars'
            A.rule.allArgs.size remainingMinorFVars.length =
          generatedFieldSource.abstractList
            (generatedPrefix ++ remainingMinorFVars)
              A.rule.allArgs.size :=
      hprefixShift.symm.trans hprefixAppend
    rw [hgeneratedOuterSplit] at hcombined
    have hclose := Expr.abstractList_after_inner
      (e := E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs generatedMotiveApp)
      (outer := generatedOuter ++ A.rule.minors_bound.fvars)
      (inner := A.rule.all_args_bound.fvars) (k := 0)
      (by simpa [generatedOuter, BoundGeneratedRecursorRule.binders,
        List.append_assoc] using A.rule.binders_nodup)
    exact hcombined.trans <| by
      simpa [generatedFieldSource, generatedOuter,
        BoundGeneratedRecursorRule.binders,
        A.rule.all_args_bound.length_fvars, List.append_assoc] using hclose
  have Htransformed := ((HfieldPrefix.liftLooseBVars' 0 j).abstractList
    sourceBinders position).liftLooseBVars' position remaining.length
  have hleftTransformed :
      ((originFieldSource.liftLooseBVars' 0 j).abstractList
        sourceBinders position).liftLooseBVars'
          position remaining.length =
        declarationDomain.liftLooseBVars' position remaining.length := by
    rw [← hleftFieldNormalization]
  have hrightAbstract :
      (generatedFieldSource.liftLooseBVars' 0 j).abstractList
          sourceBinders position =
        (generatedFieldSource.abstractList generatedPrefix
          A.rule.allArgs.size).liftLooseBVars' 0 j := by
    rw [hsourceBindersRule]
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := generatedFieldSource) (fvars := generatedPrefix)
      (start := 0) (cutoff := A.rule.allArgs.size) (amount := j)
      (by omega) hgeneratedPrefixNodup
    simpa [position, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hcommute
  have hrightTransformed :
      ((generatedFieldSource.liftLooseBVars' 0 j).abstractList
        sourceBinders position).liftLooseBVars'
          position remaining.length =
        ((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
            A.rule.binders).liftLooseBVars' 0 j := by
    rw [hrightAbstract, hremainingLength]
    have hcommute := Expr.liftLooseBVars_comm
      (generatedFieldSource.abstractList generatedPrefix
        A.rule.allArgs.size)
      remainingMinorFVars.length j A.rule.allArgs.size 0 (by omega)
    rw [← hgeneratedOuterFull]
    simpa [position, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute.symm
  have HwholePrefixJ : Expr.SameForallPrefix O.args.size
      (declarationDomain.liftLooseBVars' position remaining.length)
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
          A.rule.binders).liftLooseBVars' 0 j) := by
    rw [← hleftTransformed, ← hrightTransformed]
    exact Htransformed
  have hpreviousLength : previous.length = j := by
    simp only [previous, List.length_take]
    rw [hhypotheses]
    omega
  have hliftedPreviousLength : liftedPrevious.length = j := by
    simp [liftedPrevious, hpreviousLength]
  have hselectedMotive :
      (H.recInfos.map (·.motive))[
          E.frame.semantic.generated.ownerIdx]! =
        H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive := by
    have hgeneratedOwnerRecInfos :
        E.frame.semantic.generated.ownerIdx < H.recInfos.size := by
      simpa [H.generated.length] using E.frame.entry_lt
    rw [getElem!_pos (H.recInfos.map (·.motive))
        E.frame.semantic.generated.ownerIdx
          (by simpa using hgeneratedOwnerRecInfos),
      getElem!_pos H.recInfos E.frame.semantic.generated.ownerIdx
        hgeneratedOwnerRecInfos]
    simp
  have HwholePrefix : Expr.SameForallPrefix E.localDomains.length
      (declarationDomain.liftLooseBVars' position remaining.length)
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs
          (Expr.app
            (mkAppN
              (H.recInfos.map (·.motive))[
                E.frame.semantic.generated.ownerIdx]!
              E.frame.semantic.generated.exposedType.getAppArgs[
                stats.params.size:])
            (mkAppN A.rule.recursiveArgs[j]
              E.frame.semantic.generated.localArgs))).abstractList
          A.rule.binders).liftLooseBVars' 0 liftedPrevious.length) := by
    simpa [generatedMotiveApp, hselectedMotive, hliftedPreviousLength,
      hlocalArity, E.local_length] using HwholePrefixJ
  exact ⟨S, hypothesisOrigins, fieldDomains, hypothesisDomains,
    targetResidual, D, originRoot, sourceType, O,
    hypothesisLocalDomains, hypothesisResidual, hfields, hhypotheses,
    htarget, hliftedPriorSplit, hlocalLength, hhypothesisDomain, Hinstalled,
    ⟨by simpa [liftedPrevious, remaining, previous] using Hcanonical,
      HwholePrefix, HinstalledResidual,
      by simpa [equationDomains, liftedCanonicalLocals,
        liftedPrevious, hliftedPreviousLength₀, hpreviousLength₀,
        hhypotheses, remaining, previous] using
          HcanonicalResidual,
      by simpa [equationDomains, liftedCanonicalLocals,
        liftedPrevious, hliftedPreviousLength₀, hpreviousLength₀,
        hhypotheses, remaining, previous] using
          HcanonicalResidualType⟩⟩


end VerifyInductive
end Lean4Lean
