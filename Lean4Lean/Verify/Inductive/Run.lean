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

/-- One dependent recursive-hypothesis step, after the already-consumed
hypotheses have been aligned.  Syntactic uniqueness of the selected minor
telescope identifies the caller's installed domains with the domains used by
the source replay; the common residual translation then closes the complete
higher-order domain on both sides. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalWholeDomainDefEq
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
    (installedFieldDomains installedHypothesisDomains : List VExpr)
    (installedResidual : VExpr)
    (hinstalledFields : installedFieldDomains.length = A.rule.allArgs.size)
    (hinstalledHypotheses :
      installedHypothesisDomains.length = A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls
          (installedFieldDomains ++ installedHypothesisDomains)
          installedResidual)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (canonicalPrevious : List VExpr)
    (hcanonicalPreviousLength : canonicalPrevious.length = j)
    (Hbase :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (equationDomains ++ canonicalPrevious).reverse) :
    ∃ hypothesisLocalDomains : List VExpr,
    ∃ hypothesisResidual : VExpr,
      installedHypothesisDomains[j]! =
        VExpr.wrapForalls hypothesisLocalDomains hypothesisResidual ∧
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let liftedHypothesisLocals :=
        (liftContextPrefixAt remaining.length position
          hypothesisLocalDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let liftedCanonicalLocals :=
        (liftContextPrefix canonicalPrevious.length
          E.localDomains.reverse).reverse
      ∃ level, H.outVEnv.IsDefEq Us.length
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (VExpr.wrapForalls liftedHypothesisLocals
          (hypothesisResidual.liftN remaining.length
            (position + hypothesisLocalDomains.length)))
        (VExpr.wrapForalls liftedCanonicalLocals
          (E.resultType.liftN canonicalPrevious.length
            E.localDomains.length)) (.sort level) := by
  dsimp only at Hbase ⊢
  rcases A.finalSelectedMinorHypothesisCanonicalWholeDomains j hj B T E with
    ⟨S, hypothesisOrigins, fieldDomains, hypothesisDomains,
      targetResidual, D, originRoot, sourceType, O,
      hypothesisLocalDomains, hypothesisResidual,
      hfields, hhypotheses, htarget', hliftedPrior,
      hlocal, hhypothesisDomain, Hinstalled, _HcanonicalInstalled,
      Hprefix, HinstalledResidual, _HcanonicalResidualInstalled,
      _HcanonicalResidualTypeInstalled⟩
  have hdomains : fieldDomains ++ hypothesisDomains =
      installedFieldDomains ++ installedHypothesisDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq
      (n := A.rule.allArgs.size + A.rule.recursiveArgs.size)
      (suffix := [])
    · simp [hfields, hhypotheses]
    · simp [hinstalledFields, hinstalledHypotheses]
    · simpa [VExpr.wrapForalls_append] using htarget'.symm.trans htarget
  have hfieldDomains : fieldDomains = installedFieldDomains := by
    have Htake := congrArg
      (List.take A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Htake
  subst fieldDomains
  have hhypothesisDomains :
      hypothesisDomains = installedHypothesisDomains := by
    have Hdrop := congrArg
      (List.drop A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Hdrop
  subst hypothesisDomains
  refine ⟨hypothesisLocalDomains, hypothesisResidual,
    hhypothesisDomain, ?_⟩
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix canonicalPrevious.length
      E.localDomains.reverse).reverse
  have Hcanonical := E.fullForallTranslationAfter canonicalPrevious
  have HcanonicalResidual₀ : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains] using E.result_type_translation
  have HcanonicalResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.ordered HcanonicalResidual₀ canonicalPrevious
  have HcanonicalResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size canonicalPrevious.length)
      (E.resultType.liftN canonicalPrevious.length E.localDomains.length) := by
    simpa [liftedCanonicalLocals, E.local_length,
      List.append_assoc] using HcanonicalResidualInserted
  have Wcanonical : Ctx.LiftN canonicalPrevious.length E.localDomains.length
      (abstractForallContext
        (equationDomains ++ E.localDomains) []).toCtx
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) []).toCtx := by
    have W := Ctx.LiftN.insertAfterPrefix E.localDomains.reverse
      canonicalPrevious.reverse equationDomains.reverse
    simpa [liftedCanonicalLocals, List.reverse_append,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc] using W
  have HcanonicalResidualType : H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) []).toCtx
      (E.resultType.liftN canonicalPrevious.length E.localDomains.length) :=
    E.result_type_isType.weakN H.outVEnvWF.ordered Wcanonical
  have Hprefix' := Hprefix
  simp only [List.length_reverse, liftContextPrefixAt_length,
    List.length_take, hinstalledHypotheses,
    Nat.min_eq_left (Nat.le_of_lt hj), hcanonicalPreviousLength] at Hprefix'
  exact Hprefix'.translatedWholeTargetsOfResidualRightSort
    H.outVEnvWF Hbase
      (by simpa using Hinstalled)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using Hcanonical)
      (by simpa using hlocal) (by simp)
      (by simpa using HinstalledResidual)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using HcanonicalResidual)
      (by simpa [equationDomains, liftedCanonicalLocals] using
        HcanonicalResidualType)

/-- All recursive results of one generated rule, chosen in their production
array order and fixed to one recursor telescope and one narrowed field frame. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults
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
    (B : A.NarrowFieldRuntimeFrame) where
  resultAt : ∀ j (hj : j < A.rule.recursiveArgs.size),
    A.CanonicalRecursiveResultAt T B j hj

def
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodies
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
    (C : A.CanonicalRecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapLams E.localDomains E.resultBody

/-- The closed dependent types corresponding pointwise to `bodies`.  Keeping
this as a parallel list makes the later minor-application fold explicit:
each recursive-result term is consumed at exactly the same ordinal as the
installed minor hypothesis it discharges. -/
def
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypes
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
    (C : A.CanonicalRecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapForalls E.localDomains E.resultType

@[simp] theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodies_length
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
    (C : A.CanonicalRecursiveResults T B) :
    C.bodies.length = A.rule.recursiveArgs.size := by
  simp [CanonicalRecursiveResults.bodies]

@[simp] theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypes_length
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
    (C : A.CanonicalRecursiveResults T B) :
    C.bodyTypes.length = A.rule.recursiveArgs.size := by
  simp [CanonicalRecursiveResults.bodyTypes]

/-- Exact pointwise typing of the two parallel recursive-result lists in the
fixed equation context.  This is stronger than `bodyWF`: the latter is useful
for translation constructors, while this theorem retains the dependent type
required by the application spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTyping
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
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let hjType : j < C.bodyTypes.length := by simpa using hj
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      C.bodies[j]
      (C.bodyTypes)[j] := by
  let E := C.resultAt j (by simpa using hj)
  simpa [CanonicalRecursiveResults.bodies,
    CanonicalRecursiveResults.bodyTypes, E] using E.closed_typing

/-- Ordered list-level form of `bodyTyping`, ready for the generic closed
domain application fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypings
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
    (C : A.CanonicalRecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx)
      C.bodies C.bodyTypes := by
  dsimp only
  apply Lean4Lean.VerifyInductive.List.forall₂_of_getElem
  · simp
  · intro j hjBodies hjTypes
    simpa using C.bodyTyping j hjBodies

/-- The chronological `j`th closed-domain entry is exactly the canonical
higher-order result type weakened below the `j` earlier hypotheses. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.liftClosedBodyType_getElem
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
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodyTypes.length) :
    let E := C.resultAt j (by simpa using hj)
    (VExpr.liftClosedDomains C.bodyTypes 0)[j]'(by simpa using hj) =
      VExpr.wrapForalls
        (liftContextPrefix j E.localDomains.reverse).reverse
        (E.resultType.liftN j E.localDomains.length) := by
  dsimp only
  let E := C.resultAt j (by simpa using hj)
  rw [VExpr.liftClosedDomains_getElem C.bodyTypes 0 j hj]
  have hbodyType : C.bodyTypes[j] =
      VExpr.wrapForalls E.localDomains E.resultType := by
    simp [CanonicalRecursiveResults.bodyTypes, E]
  rw [hbodyType, VExpr.liftN_wrapForalls]
  simp [E, liftContextPrefix, liftContextPrefixAt, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]

/-- Inductively align the complete installed recursive-hypothesis telescope
with the canonical closed result types.  At ordinal `j`, the induction
hypothesis is exactly the base-context conversion required by
`finalSelectedMinorHypothesisCanonicalWholeDomainDefEq`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRecursiveHypothesisContext
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (C : A.CanonicalRecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hbase :
      let minorIdx := recursorMinorOffset indTypes owner + i
      let remaining := T.minors.drop minorIdx
      let installedFields :=
        (liftContextPrefix remaining.length fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
        equationDomains.reverse) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let remaining := T.minors.drop minorIdx
    let installedHypotheses :=
      (liftContextPrefixAt remaining.length fieldDomains.length
        hypothesisDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ equationDomains.reverse)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        equationDomains.reverse) := by
  dsimp only at Hbase ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let installedBase :=
    (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
  let canonicalDomains := VExpr.liftClosedDomains C.bodyTypes 0
  have hinstalledLength : installedHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [installedHypotheses, hhypotheses]
  have hcanonicalLength : canonicalDomains.length =
      A.rule.recursiveArgs.size := by
    simp [canonicalDomains]
  have go : ∀ n, n ≤ A.rule.recursiveArgs.size →
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((installedHypotheses.take n).reverse ++ installedBase)
        ((canonicalDomains.take n).reverse ++ equationDomains.reverse) := by
    intro n hn
    induction n with
    | zero =>
      simpa [Us, remaining, installedFields, installedBase,
        equationDomains] using Hbase
    | succ n ih =>
      have hnlt : n < A.rule.recursiveArgs.size := by omega
      have Hprior := ih (by omega)
      let E := C.resultAt n hnlt
      let canonicalPrevious := canonicalDomains.take n
      have hcanonicalPreviousLength : canonicalPrevious.length = n := by
        exact List.length_take_of_le (by rw [hcanonicalLength]; omega)
      have hpriorSplit :
          (fieldDomains ++ hypothesisDomains).take
              (A.rule.allArgs.size + n) =
            fieldDomains ++ hypothesisDomains.take n := by
        rw [← hfields, List.take_length_add_append]
      have hnHypotheses : n ≤ hypothesisDomains.length := by
        rw [hhypotheses]
        omega
      have hinstalledPrevious : installedHypotheses.take n =
          (liftContextPrefixAt remaining.length fieldDomains.length
            (hypothesisDomains.take n).reverse).reverse := by
        have Htake := liftContextPrefixAt_reverse_append_take_left
          remaining.length fieldDomains.length
          (hypothesisDomains.take n) (hypothesisDomains.drop n)
        rw [List.take_append_drop n hypothesisDomains] at Htake
        simpa only [installedHypotheses,
          List.length_take_of_le hnHypotheses] using Htake
      have HpointBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
          (T.params ++ T.motives ++ T.minors ++
            (liftContextPrefix remaining.length
              ((fieldDomains ++ hypothesisDomains).take
                (A.rule.allArgs.size + n)).reverse).reverse).reverse
          (equationDomains ++ canonicalPrevious).reverse := by
        rw [hpriorSplit, liftContextPrefix_reverse_append,
          ← hinstalledPrevious]
        simpa [installedFields, installedBase, equationDomains,
          canonicalPrevious,
          List.reverse_append, List.append_assoc] using Hprior
      rcases A.finalSelectedMinorHypothesisCanonicalWholeDomainDefEq
          fieldDomains hypothesisDomains targetResidual hfields hhypotheses
          B T htarget n hnlt E canonicalPrevious hcanonicalPreviousLength
          HpointBase with
        ⟨localDomains, residual, hhypothesisDomain, Hdomain⟩
      have hinstalledDomain : installedHypotheses[n] =
          VExpr.wrapForalls
            ((liftContextPrefixAt remaining.length
              (A.rule.allArgs.size + n) localDomains.reverse).reverse)
            (residual.liftN remaining.length
              (A.rule.allArgs.size + n + localDomains.length)) := by
        rw [← getElem!_pos installedHypotheses n (by
          rw [hinstalledLength]; exact hnlt)]
        simp only [installedHypotheses]
        rw [liftContextPrefixAt_reverse_getElem
          remaining.length fieldDomains.length hypothesisDomains n
          (by simpa [hhypotheses] using hnlt),
          hhypothesisDomain, VExpr.liftN_wrapForalls]
        simp [hfields, Nat.add_assoc]
      have hcanonicalDomain : canonicalDomains[n] =
          VExpr.wrapForalls
            (liftContextPrefix n E.localDomains.reverse).reverse
            (E.resultType.liftN n E.localDomains.length) := by
        simpa [canonicalDomains, E] using
          C.liftClosedBodyType_getElem n (by
            simpa [canonicalDomains, hcanonicalLength] using hnlt)
      have Hdomain' : ∃ level, H.outVEnv.IsDefEq Us.length
          ((installedHypotheses.take n).reverse ++ installedBase)
          installedHypotheses[n] canonicalDomains[n] (.sort level) := by
        rw [hinstalledDomain, hcanonicalDomain]
        have hliftedPriorCtx := congrArg List.reverse
          (liftContextPrefix_reverse_append remaining.length fieldDomains
            (hypothesisDomains.take n))
        dsimp only at Hdomain
        rw [hpriorSplit] at Hdomain
        simp only [List.reverse_append, List.reverse_reverse] at Hdomain hliftedPriorCtx
        rw [hliftedPriorCtx] at Hdomain
        simpa [Us, remaining, hinstalledPrevious, installedFields, installedBase,
          equationDomains, canonicalPrevious, hcanonicalPreviousLength,
          E, List.reverse_append, List.append_assoc] using Hdomain
      rcases Hdomain' with ⟨level, Hdomain'⟩
      have Hnext := VEnv.IsDefEqCtx.succ Hprior Hdomain'
      have hinstalledTakeSucc : installedHypotheses.take (n + 1) =
          installedHypotheses.take n ++ [installedHypotheses[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hinstalledLength]; exact hnlt)
      have hcanonicalTakeSucc : canonicalDomains.take (n + 1) =
          canonicalDomains.take n ++ [canonicalDomains[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hcanonicalLength]; exact hnlt)
      rw [hinstalledTakeSucc]
      rw [hcanonicalTakeSucc]
      simp only [List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact Hnext
  have Hmixed := go A.rule.recursiveArgs.size (by omega)
  have HmixedFull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ installedBase)
      (canonicalDomains.reverse ++ equationDomains.reverse) := by
    have hinstalledTake : installedHypotheses.take
        A.rule.recursiveArgs.size = installedHypotheses :=
      by rw [← hinstalledLength, List.take_length]
    have hcanonicalTake : canonicalDomains.take
        A.rule.recursiveArgs.size = canonicalDomains :=
      by rw [← hcanonicalLength, List.take_length]
    simpa only [hinstalledTake, hcanonicalTake] using Hmixed
  have Hleft := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
    Hbase HmixedFull.isType
  have Hresult := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty
    H.outVEnvWF (Hleft.symm H.outVEnvWF.ordered) HmixedFull
  simpa [remaining, installedHypotheses, canonicalDomains, equationDomains,
    installedBase, hinstalledLength, hcanonicalLength,
    List.append_assoc] using Hresult

/-- Pointwise strict source translation for the canonical result list, once
the shared lambda-domain template has been translated in the fixed equation
context.  The same `resultAt` witness determines the source array position,
the target body, and the retained typing used by `bodyTyping`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslationOfTemplate
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
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length)
    (templateTarget : VExpr)
    (Htemplate :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
      let E := C.resultAt j hjArg
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((E.frame.semantic.generated.current.lctx.mkLambda
            E.frame.semantic.generated.localArgs
            (mkAppN (A.rule.recursiveArgs)[j]
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
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  have Hfull := E.fullTranslationOfTemplate templateTarget (by
    simpa only [E] using Htemplate)
  simpa [CanonicalRecursiveResults.bodies, E] using Hfull

/-- Pointwise strict translation of a generated recursive result to its
canonical closed body in the fixed equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslation
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
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  apply C.bodyTranslationOfTemplate j hj E.templateTarget
  simpa only [E] using E.templateTranslation

/-- List-level strict translation for the complete generated recursive-result
spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslations
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
    (C : A.CanonicalRecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext equationDomains []))
      (A.rule.recursiveResults.toList.map
        (fun result => result.abstractList A.rule.binders))
      C.bodies := by
  apply List.forall₂_of_getElem
  · simp [C.bodies_length, A.rule.recursive_calls.size]
  · intro j hsource htarget
    have hj : j < C.bodies.length := htarget
    have hresult : j < A.rule.recursiveResults.size := by
      rw [A.rule.recursive_calls.size]
      simpa [C.bodies_length] using hj
    have Htranslation := C.bodyTranslation j hj
    rw [getElem!_pos A.rule.recursiveResults j hresult] at Htranslation
    simpa using Htranslation

/-- Every selected recursive-result body is already well formed in the one
fixed equation context shared by the entire rule.  This is the list-level
typing invariant consumed by the minor-application fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyWF
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
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VExpr.WF H.outVEnv Us.length
      (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  have hj' : j < A.rule.recursiveArgs.size := by
    simpa using hj
  let E := C.resultAt j hj'
  have hbody : C.bodies[j] =
      VExpr.wrapLams E.localDomains E.resultBody := by
    simp [CanonicalRecursiveResults.bodies, E]
  rw [hbody]
  refine ⟨VExpr.wrapForalls E.localDomains E.resultType, ?_⟩
  change H.outVEnv.HasType Us.length
    (abstractForallContext equationDomains []).toCtx
    (VExpr.wrapLams E.localDomains E.resultBody)
    (VExpr.wrapForalls E.localDomains E.resultType)
  simpa only [Us, equationDomains] using E.closed_typing

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResults
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
    (B : A.NarrowFieldRuntimeFrame) :
    Nonempty (A.CanonicalRecursiveResults T B) := by
  classical
  exact ⟨{
    resultAt := fun j hj => Classical.choice
      (A.canonicalRecursiveResultAt T B j hj) }⟩

/-- Synchronize the selected minor and every canonical recursive result on one
recursor telescope, one narrowed field frame, and one literal anonymous
equation context.  No existential witness chosen by a pointwise theorem may
drift after this boundary. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationFrame
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          (∃ checkedDomains checkedEquationFieldDomains : List VExpr,
            checkedDomains.length = A.rule.allArgs.size ∧
            checkedEquationFieldDomains =
              (liftContextPrefix inserted.length
                checkedDomains.reverse).reverse ∧
            VEnv.IsDefEqCtx H.outVEnv Us.length []
              (checkedEquationFieldDomains.reverse ++
                (T.params ++ inserted).reverse)
              (abstractForallContext equationDomains []).toCtx) ∧
          H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          (∀ j (hj : j < C.bodies.length),
            let hjType : j < C.bodyTypes.length := by simpa using hj
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j]
              (C.bodyTypes)[j]) ∧
          (∀ j (hj : j < A.rule.recursiveArgs.size),
            let E := C.resultAt j hj
            OnCtx
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                (H.outVEnv.IsType Us.length) ∧
              H.outVEnv.HasType Us.length
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                E.resultBody E.resultType) ∧
          ∀ j (hj : j < C.bodies.length),
            VExpr.WF H.outVEnv Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.narrowFieldRuntimeFrame with ⟨B⟩
  rcases A.finalNarrowSelectedMinorTypeFrame B with
    ⟨T, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext, Hminor⟩
  rcases A.canonicalRecursiveResults T B with ⟨C⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        (liftContextPrefix inserted.length B.fieldDomains.reverse) ++
          inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HfixedEquationContext : OnCtx
      (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    rw [hequationContext]
    simpa only [inserted] using HfixedContext
  rcases A.finalCheckedNarrowEquationContextAlignmentFor B T with
    ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      hcheckedEquationFields, HcheckedEquation⟩
  have HcheckedEquation' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (checkedEquationFieldDomains.reverse ++
        (T.params ++ inserted).reverse)
      (abstractForallContext equationDomains []).toCtx := by
    rw [hequationContext]
    simpa only [inserted, List.append_assoc] using HcheckedEquation
  refine ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HfixedEquationContext
  · exact ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      by simpa only [inserted] using hcheckedEquationFields,
      HcheckedEquation'⟩
  · rw [hequationContext]
    simpa only [inserted, equationFieldDomains, later, minorVar,
      List.length_reverse] using Hminor
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyTyping j hj
  · intro j hj
    let E := C.resultAt j hj
    have Hclosed : H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.wrapLams E.localDomains E.resultBody)
        (VExpr.wrapForalls E.localDomains E.resultType) := by
      simpa only [equationDomains, inserted, equationFieldDomains,
        List.append_assoc] using E.closed_typing
    have Hopen := VEnv.HasType.wrapLams_inv H.outVEnvWF
      HfixedEquationContext Hclosed
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using Hopen
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyWF j hj

/-- A well-formed canonical application of the selected minor to the fixed
equation fields forces those fields to agree with the installed field
telescope.  The selected minor is stored outside the equation fields, so its
lookup typing is first recognized as a common weakening of the still-open
installed telescope; `canonicalApplicationContext_of_weakened` then performs
the dependent binder-by-binder inversion. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorFieldContextOfApplication
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx :
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hminor :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      let later := T.minors.drop (minorIdx + 1)
      let minorVar := equationFieldDomains.length + later.length
      H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (.bvar minorVar)
        ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
          targetResidual).liftN
            (later.length + 1 + equationFieldDomains.length) 0))
    (Happlication :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      let later := T.minors.drop (minorIdx + 1)
      let minorVar := equationFieldDomains.length + later.length
      VExpr.WF H.outVEnv Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.mkApps (.bvar minorVar)
          (recursorCanonicalVars equationFieldDomains.length))) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFieldDomains :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let outer := inserted.reverse ++
      H.parameterSuffix.parameterDecls.toCtx
    let later := T.minors.drop (minorIdx + 1)
    let shift := later.length + 1
    let installedEquationFields :=
      (liftContextPrefix shift fieldDomains.reverse).reverse
    let installedEquationHypotheses :=
      (liftContextPrefixAt shift fieldDomains.length
        hypothesisDomains.reverse).reverse
    let installedEquationResidual := targetResidual.liftN shift
      (fieldDomains.length + hypothesisDomains.length)
    VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++ outer)
        (installedEquationFields.reverse ++ outer) ∧
      H.outVEnv.HasType Us.length
        (equationFieldDomains.reverse ++ outer)
        (VExpr.mkApps (.bvar
          (equationFieldDomains.length + later.length))
          (recursorCanonicalVars equationFieldDomains.length))
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual) := by
  dsimp only at Hctx Hminor Happlication ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let outer := inserted.reverse ++
    H.parameterSuffix.parameterDecls.toCtx
  let later := T.minors.drop (recursorMinorOffset indTypes owner + i + 1)
  let shift := later.length + 1
  let installedEquationFields :=
    (liftContextPrefix shift fieldDomains.reverse).reverse
  let installedEquationHypotheses :=
    (liftContextPrefixAt shift fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedEquationResidual := targetResidual.liftN shift
    (fieldDomains.length + hypothesisDomains.length)
  have hequationLength : equationFieldDomains.length =
      fieldDomains.length := by
    simp [equationFieldDomains, hfields, B.fieldDomains_length]
  have hctxShape :
      (abstractForallContext
        (H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains) []).toCtx =
        equationFieldDomains.reverse ++ outer := by
    simp [abstractForallContext_toCtx, equationFieldDomains, outer,
      List.reverse_append, List.append_assoc, VLCtx.toCtx]
  rw [hctxShape] at Hctx Hminor Happlication
  have htypeShape :
      ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
          targetResidual).liftN
        (later.length + 1 + equationFieldDomains.length) 0) =
      ((VExpr.wrapForalls installedEquationFields
          (VExpr.wrapForalls installedEquationHypotheses
            installedEquationResidual)).liftN
        equationFieldDomains.length 0) := by
    rw [← VExpr.liftN_liftN]
    rw [VExpr.liftN_wrapForalls]
    simp only [Nat.zero_add]
    have hprefix : liftContextPrefixAt (later.length + 1) 0
        (fieldDomains ++ hypothesisDomains).reverse =
        liftContextPrefix (later.length + 1)
          (fieldDomains ++ hypothesisDomains).reverse := rfl
    rw [hprefix]
    rw [liftContextPrefix_reverse_append]
    simp [shift, installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, VExpr.wrapForalls_append,
      equationFieldDomains, Nat.add_assoc]
  rw [htypeShape] at Hminor
  have htermShape :
      (VExpr.bvar later.length).liftN equationFieldDomains.length 0 =
        .bvar (equationFieldDomains.length + later.length) := by
    simp [VExpr.liftN, Nat.add_comm]
  rw [← htermShape] at Hminor Happlication
  have HfieldContext :=
    VEnv.HasType.canonicalApplicationContext_of_weakened
    H.outVEnvWF equationFieldDomains installedEquationFields outer Hctx
      Hminor (by simpa [installedEquationFields] using hequationLength)
      Happlication
  have W : Ctx.LiftN equationFieldDomains.length 0 outer
      (equationFieldDomains.reverse ++ outer) := by
    exact Ctx.LiftN.zero equationFieldDomains.reverse (by simp)
  have HminorBase : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls installedEquationFields
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual)) :=
    (VEnv.HasType.weakN_iff H.outVEnvWF Hctx W).mp Hminor
  have HminorBase' : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls
        (installedEquationFields ++ installedEquationHypotheses)
        installedEquationResidual) := by
    rw [VExpr.wrapForalls_append]
    exact HminorBase
  have HpartialInstalled :=
    VEnv.HasType.mkApps_wrapForalls_prefix_canonical
      H.outVEnvWF.ordered
      (initial := installedEquationFields)
      (suffix := installedEquationHypotheses) HminorBase'
  have HpartialFixed := HpartialInstalled.defeqDFC
    H.outVEnvWF.ordered (HfieldContext.symm H.outVEnvWF.ordered)
  exact ⟨HfieldContext, by
    simpa [Us, inserted, equationFieldDomains, outer, later, shift,
      installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, hequationLength, hfields,
      B.fieldDomains_length, VExpr.liftN, recursorCanonicalVars,
      List.length_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      HpartialFixed⟩

/-- Positive-arity selected minors admit their canonical field application
in the one fixed equation context shared by all recursive results.  The
application is first typed using the source-stable outer telescope, then
transported through the exact same checked field frame to the narrowed
equation fields.  Inverting that well-formed application additionally
identifies those fixed fields with the selected minor's installed fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationPositiveArity
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          VExpr.WF H.outVEnv Us.length
            (abstractForallContext equationDomains []).toCtx
            (VExpr.mkApps (.bvar minorVar)
              (recursorCanonicalVars equationFieldDomains.length)) ∧
          let outer := inserted.reverse ++
            H.parameterSuffix.parameterDecls.toCtx
          let shift := later.length + 1
          let installedEquationFields :=
            (liftContextPrefix shift fieldDomains.reverse).reverse
          let installedEquationHypotheses :=
            (liftContextPrefixAt shift fieldDomains.length
              hypothesisDomains.reverse).reverse
          let installedEquationResidual := targetResidual.liftN shift
            (fieldDomains.length + hypothesisDomains.length)
          VEnv.IsDefEqCtx H.outVEnv Us.length []
              (equationFieldDomains.reverse ++ outer)
              (installedEquationFields.reverse ++ outer) ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx
              (VExpr.mkApps (.bvar minorVar)
                (recursorCanonicalVars equationFieldDomains.length))
              (VExpr.wrapForalls installedEquationHypotheses
                installedEquationResidual) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCanonicalMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext,
      _HcheckedFrame, Hminor, _HbodyTyping, _HopenTyping, _HbodyWF⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  rcases A.finalSelectedOuterRuntimeFieldAlignmentFor B T hpositive with
    ⟨selectedScope, Hselected, outerScope, Houter,
      selectedFields, outerFields, applicationHypotheses,
      applicationResidual, outerResidual,
      _hselectedScope, _hselectedShift, houterScope, houterShift,
      hscopeSplit, _hfactor, hrelative, hselectedFields, houterFields,
      _happlicationHypotheses, HouterTail, HselectedPrefix, HouterPrefix,
      Happlication, Hnatural, _Hruntime⟩
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremainingLength :
      (H.bindings.flatMinors.fvars.drop minorIdx).length =
        (T.minors.drop minorIdx).length := by
    simp only [List.length_drop]
    rw [H.bindings.flatMinors.length_fvars, T.minors_length]
  have hdrop : T.minors.drop minorIdx = T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hgeneratedRemaining : (T.minors.drop minorIdx).length =
      later.length + 1 := by
    simp [hdrop]
  have Hnatural' := Hnatural
  rw [hrelative, liftForallDomains_skipN_consN_refl,
    hremainingLength, hgeneratedRemaining] at Hnatural'
  have HselectedOuter := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HouterPrefix.symm H.outVEnvWF.ordered) Hnatural'
  have HouterApplication := Happlication.defeqDFC H.outVEnvWF.ordered
    HselectedOuter
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T₁, checkedDomains, checkedResidual, _introTarget, hparams,
      hchecked, Hchecked, _HcheckedResidual, _HcheckedType,
      _HcheckedTypeT, HcheckedContext, _HintroType, _Hintro,
      _HintroShape⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparamsT, hmotivesT, hminorsT,
      _hindicesT, _hmajorT, _hresultT⟩
  rw [hparamsT] at hparams HcheckedContext
  have hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [← H.parameterDecls] using hparams
  have Hchecked' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual) := by
    simpa only [← H.parameterDecls] using Hchecked
  rcases A.finalOuterCheckedEquationFieldAlignmentFor T outerScope Houter
      outerFields outerResidual houterScope houterShift houterFields
      HouterTail HouterPrefix checkedDomains checkedResidual hchecked
      Hchecked' with
    ⟨outerCheckedFields, houterCheckedFields, HouterChecked⟩
  rcases A.finalCheckedNarrowEquationContextAlignmentFromFrameFor B T
      checkedDomains checkedResidual hparams' hchecked Hchecked'
      HcheckedContext with
    ⟨checkedEquationFields, hcheckedEquationFields, HcheckedFixed⟩
  rw [houterCheckedFields] at HouterChecked
  rw [hcheckedEquationFields] at HcheckedFixed
  have HouterFixed := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HouterChecked HcheckedFixed
  have HfixedApplication := HouterApplication.defeqDFC
    H.outVEnvWF.ordered HouterFixed
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        equationFieldDomains.reverse ++ inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HapplicationWF : VExpr.WF H.outVEnv Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length)) := by
    rw [hequationContext]
    let applicationType := VExpr.wrapForalls
      (liftContextPrefixAt (later.length + 1) selectedFields.length
        applicationHypotheses.reverse).reverse
      (applicationResidual.liftN (later.length + 1)
        (selectedFields.length + applicationHypotheses.length))
    refine ⟨applicationType, ?_⟩
    change H.outVEnv.HasType Us.length
      (equationFieldDomains.reverse ++ inserted.reverse ++
        H.parameterSuffix.parameterDecls.toCtx)
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length))
      applicationType
    simpa [applicationType, minorVar, minorIdx, equationFieldDomains,
      inserted, later, VExpr.liftN, hselectedFields, houterFields,
      B.fieldDomains_length, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using HfixedApplication
  have HinstalledFields :=
    A.finalCanonicalMinorFieldContextOfApplication B T fieldDomains
      hypothesisDomains targetResidual hfields HfixedContext Hminor
      HapplicationWF
  have HinstalledTyping : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length))
      (VExpr.wrapForalls
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length))) := by
    rw [hequationContext]
    simpa only [Us, minorIdx, equationFieldDomains, inserted, later,
      minorVar, List.append_assoc] using HinstalledFields.2
  exact ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, HfixedContext, Hminor,
    HapplicationWF, HinstalledFields.1, HinstalledTyping⟩

/-- Apply all canonical recursive results to a selected minor that has
already been applied to the fixed equation fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorRecursiveApplicationOfContext
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (C : A.CanonicalRecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget : T.minors[recursorMinorOffset indTypes owner + i]! =
      VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hctx :
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hfield :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let later := T.minors.drop (minorIdx + 1)
      let installedFields :=
        (liftContextPrefix (later.length + 1) fieldDomains.reverse).reverse
      let outer := inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFields.reverse ++ outer)
        (installedFields.reverse ++ outer))
    (Hpartial :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      let later := T.minors.drop (minorIdx + 1)
      let installedHypotheses :=
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
      let installedResidual := targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)
      H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.mkApps (.bvar (equationFields.length + later.length))
          (recursorCanonicalVars equationFields.length))
        (VExpr.wrapForalls installedHypotheses installedResidual)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFields :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
        equationFields
    let later := T.minors.drop (minorIdx + 1)
    let fn := VExpr.mkApps
      (.bvar (equationFields.length + later.length))
      (recursorCanonicalVars equationFields.length)
    let finalType := VExpr.applyForallType
      (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length)))
      C.bodies
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps fn C.bodies) finalType := by
  dsimp only at Hctx Hfield Hpartial ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++ equationFields
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedResidual := targetResidual.liftN remaining.length
    (fieldDomains.length + hypothesisDomains.length)
  let fn := VExpr.mkApps
    (.bvar (equationFields.length + later.length))
    (recursorCanonicalVars equationFields.length)
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simpa [remaining, later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
  have Hparams := H.finalRecursorParameterContextFor howner T
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [Us, ← H.parameterDecls] using Hparams
  let equationPrefix := equationFields.reverse ++ inserted.reverse
  let installedPrefix := installedFields.reverse ++ inserted.reverse
  have Hfield' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ H.parameterSuffix.parameterDecls.toCtx)
      (installedPrefix ++ H.parameterSuffix.parameterDecls.toCtx) := by
    simpa [Us, equationPrefix, installedPrefix, installedFields,
      equationFields, inserted, later, hremainingLength,
      List.append_assoc] using Hfield
  have HfieldT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ T.params.reverse)
      (installedPrefix ++ T.params.reverse) := by
    have Hrebased := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.rebaseCommonSuffix
      H.outVEnvWF Hparams' Hfield'
    simpa [equationPrefix, installedPrefix, installedFields,
      hremainingLength, List.append_assoc] using Hrebased
  have HequationParams :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hparams' HfieldT.isType
  have HbaseMixed := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty
    H.outVEnvWF (HfieldT.symm H.outVEnvWF.ordered) HequationParams
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      equationDomains.reverse := by
    simpa [equationPrefix, installedPrefix, equationDomains,
      equationFields, inserted, List.reverse_append,
      List.append_assoc] using HbaseMixed
  have Hhypotheses := A.finalCanonicalRecursiveHypothesisContext B T C
    fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      htarget (by simpa [Us, minorIdx, remaining, installedFields,
        equationDomains, equationFields, inserted,
        List.append_assoc] using Hbase)
  have Hhypotheses' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++
        (abstractForallContext equationDomains []).toCtx)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        (abstractForallContext equationDomains []).toCtx) := by
    simpa [remaining, installedHypotheses, equationDomains,
      equationFields, inserted, abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc] using Hhypotheses
  have Hpartial' : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx fn
      (VExpr.wrapForalls installedHypotheses installedResidual) := by
    simpa [remaining, installedHypotheses, installedResidual,
      hremainingLength, equationDomains, equationFields, inserted,
      later, fn] using Hpartial
  have HbodyTypings := C.bodyTypings
  have Hexact := VEnv.HasType.mkApps_of_defeqLiftClosedDomains_exact
    (installedDomains := installedHypotheses)
    (resultType := installedResidual) (types := C.bodyTypes)
    (args := C.bodies) H.outVEnvWF Hctx Hpartial' Hhypotheses' (by
      simpa only [Us, equationDomains, inserted, equationFields,
        List.append_assoc] using HbodyTypings)
  simpa [installedResidual, hremainingLength, fn, later, equationFields,
    inserted, B.fieldDomains_length] using Hexact

/-- Degenerate generated rules need no application fold: when the selected
constructor has neither fields nor recursive hypotheses, the selected minor
variable itself is the complete RHS and is already typed in the fixed
equation context.  Isolating this case lets the positive-arity replay theorem
remain honest about the nonempty telescope premise it uses. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationZeroArity
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
    (hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ targetResidual : VExpr,
        C.bodies = [] ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted
        let later := T.minors.drop (minorIdx + 1)
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar later.length)
            (targetResidual.liftN (later.length + 1) 0) := by
  dsimp only
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hhypothesesZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.finalCanonicalMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, _hminorType, Hctx, _HcheckedEquation, Hminor,
      _HbodyTyping, _HopenBodyTyping, _HbodyWF⟩
  have hfieldDomains : fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero (hfields.trans hfieldsZero)
  have hhypothesisDomains : hypothesisDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hhypotheses.trans hhypothesesZero)
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  have hbodies : C.bodies = [] :=
    List.eq_nil_of_length_eq_zero (by
      rw [C.bodies_length, hhypothesesZero])
  subst fieldDomains
  subst hypothesisDomains
  exact ⟨B, T, C, targetResidual, hbodies,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      List.append_assoc] using Hctx,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      VExpr.wrapForalls, VLCtx.toCtx, List.append_assoc] using Hminor⟩

/-- Positive-arity generated RHS in its fixed narrowed equation context.
The selected minor, constructor fields, and generated recursive results are
all translated strictly to the same application spine that is independently
typed by the canonical minor fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRhsPositiveArity
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ equationFields : List VExpr,
      ∃ rhsBody typeBody : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCanonicalMinorApplicationPositiveArity hpositive with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, Hctx, _Hminor, HpartialWF,
      Hfield, Hpartial⟩
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFields.length + later.length
  let fn := VExpr.mkApps (.bvar minorVar)
    (recursorCanonicalVars equationFields.length)
  have Hrhs := A.finalCanonicalMinorRecursiveApplicationOfContext B T C
      fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      hminorType Hctx Hfield Hpartial
  let finalType := VExpr.applyForallType
    (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
      (targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)))
    C.bodies
  let rhsBody := VExpr.mkApps fn C.bodies
  have HrhsTyped : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx rhsBody finalType := by
    simpa only [Us, minorIdx, inserted, equationFields, equationDomains,
      later, minorVar, fn, rhsBody, List.append_assoc] using Hrhs
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorVar : minorVar < equationDomains.length := by
    dsimp only [minorVar, equationDomains, equationFields, inserted, later]
    simp only [List.length_append, List.length_reverse,
      liftContextPrefix_length, List.length_drop]
    omega
  have HminorTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar minorVar) (.bvar minorVar) :=
    TrExprS.bvar_of_abstractForallContext equationDomains [] minorVar hminorVar
  have HfieldsTr := A.finalNarrowEquationFieldTranslationsFor B T
  have HpartialTr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HminorTr HfieldsTr HpartialWF
  have HresultsTr : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext equationDomains []))
      ((A.rule.recursiveResults.map fun result =>
        result.abstractList A.rule.binders).toList) C.bodies := by
    simpa only [Us, equationDomains, inserted, equationFields,
      Array.toList_map, List.append_assoc] using C.bodyTranslations
  have HrhsTr₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HpartialTr HresultsTr
      (show VExpr.WF H.outVEnv Us.length
        (abstractForallContext equationDomains []).toCtx rhsBody from
          ⟨finalType, HrhsTyped⟩)
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        minorVar := by
    dsimp only [minorVar, equationFields, inserted, later]
    simp only [List.length_reverse, liftContextPrefix_length,
      List.length_drop, B.fieldDomains_length, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have HrhsTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsourceShape]
    simpa [rhsBody, fn, Expr.mkAppN_eq_mkAppList, equationFields,
      equationDomains, inserted, B.fieldDomains_length,
      List.append_assoc] using HrhsTr₀
  exact ⟨B, T, C, equationFields, rhsBody, finalType,
    by simp [equationFields, B.fieldDomains_length], Hctx, HrhsTr,
    HrhsTyped⟩

/-- Zero-arity counterpart of `finalCanonicalRhsPositiveArity`.  Both
application arrays are empty, so the complete source RHS and canonical RHS
are the selected minor variable itself. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRhsZeroArity
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
    (hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ equationFields : List VExpr,
      ∃ rhsBody typeBody : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hresultsZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.finalCanonicalMinorApplicationZeroArity hzero with
    ⟨B, T, C, targetResidual, hbodies, Hctx, Hminor⟩
  let inserted := T.motives ++ T.minors
  let equationFields : List VExpr := []
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let rhsBody : VExpr := .bvar later.length
  let typeBody := targetResidual.liftN (later.length + 1) 0
  have Hctx' : OnCtx (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa only [Us, inserted, equationFields, equationDomains,
      List.append_nil] using Hctx
  have HrhsTyped : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx rhsBody typeBody := by
    simpa only [Us, minorIdx, inserted, equationFields, equationDomains,
      later, rhsBody, typeBody, List.append_nil] using Hminor
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorVar : later.length < equationDomains.length := by
    dsimp only [later, equationDomains, equationFields, inserted]
    simp only [List.length_append, List.length_drop, List.length_nil,
      Nat.add_zero]
    omega
  have HvarTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar later.length) rhsBody := by
    exact TrExprS.bvar_of_abstractForallContext equationDomains []
      later.length hminorVar
  have hallArgs : A.rule.allArgs = #[] :=
    Array.eq_empty_of_size_eq_zero hfieldsZero
  have hrecursiveResultsSize : A.rule.recursiveResults.size = 0 := by
    rw [A.rule.recursive_calls.size]
    exact hresultsZero
  have hrecursiveResults : A.rule.recursiveResults = #[] :=
    Array.eq_empty_of_size_eq_zero hrecursiveResultsSize
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        later.length := by
    dsimp only [later]
    simp only [List.length_drop, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have hsource : A.rule.sourceRhsBody.abstractList A.rule.binders =
      .bvar later.length := by
    simpa [hallArgs, hrecursiveResults, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList] using hsourceShape
  have HrhsTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsource]
    exact HvarTr
  exact ⟨B, T, C, equationFields, rhsBody, typeBody,
    by simp [equationFields, hfieldsZero], Hctx', HrhsTr, HrhsTyped⟩

/-- Rule-indexed existential specialization of
`canonicalRecursiveResultTypingFor`.  It remains convenient for pointwise
consumers that do not need to retain a common equation frame. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResultTyping
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
    (B : A.NarrowFieldRuntimeFrame :=
      Classical.choice A.narrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ F : A.RecursiveCallRecursorFrame j hj,
      ∃ (equationDomains localDomains : List VExpr)
          (resultBody resultType : VExpr),
        equationDomains.length = A.rule.binders.length ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
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
        H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
          (VExpr.wrapLams localDomains resultBody)
          (VExpr.wrapForalls localDomains resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.recursiveCallRecursorFrame j hj with ⟨F⟩
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  rcases F.canonicalRecursiveCallBodyWF T (B := B) with
    ⟨equationDomains, localDomains, prefixTarget, indexTargets,
      majorTarget, ownerTarget, hlocal, _hequationFixed, hequation, _Hctx,
      _HlocalTemplate, Hbody,
      _HtemplateResidual, _HmotiveApplication, _HbodyType, Hclosed, _HbodyWF⟩
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
  exact ⟨F, equationDomains, localDomains, resultBody, resultType,
    hequation, hlocal, Htelescope', by simpa [resultBody, args] using Hbody,
    by simpa [resultBody, resultType, args] using Hclosed⟩

/-- Weaken the canonical recursive-call prefix beneath the higher-order
lambda domains and identify its source with the exact two-stage abstraction
performed by production. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedCommonPrefixTranslation
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains localDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hlocal : localDomains.length = F.semantic.generated.localArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    let localPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg => arg.abstractList
              F.semantic.generated.arguments_bound.fvars))
          ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList
            F.semantic.generated.arguments_bound.fvars))
        ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars)
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    let target :=
      ((VExpr.mkApps
          ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
    TrExprS H.outVEnv Us
      (abstractForallContext localDomains
        (abstractForallContext equationDomains []))
      (localPrefix.abstractList A.rule.binders
        F.semantic.generated.localArgs.size)
      (target.liftN localDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let localPrefix :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg => arg.abstractList
            F.semantic.generated.arguments_bound.fvars))
        ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars))
      ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList
        F.semantic.generated.arguments_bound.fvars)
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let target :=
    ((VExpr.mkApps
        ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0)
  have Hbase := F.canonicalPrefixResidualTranslation
    T fieldDomains hfields Hctx
  have Hweak := Hbase.weakBV H.outVEnvWF.ordered
    (abstractForallContext.bvLift localDomains
      (abstractForallContext equationDomains []))
  have hsource := F.outerAbstractedCommonPrefix_eq_lift
  dsimp only at hsource
  dsimp only [Us, equationDomains, localPrefix, selectedOwner, recursor,
    target] at Hweak ⊢
  rw [hsource]
  simpa only [hlocal] using Hweak

/-- Canonical equation frame with the source recursor prefix translated and
the matching abstract prefix and constructor major already typed.  All
components share the same telescope witnesses, which is the handoff point
for consuming the target indices and major premise. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRecursorPrefixFrame
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (recursorCanonicalVars
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0)
          ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
            fieldDomains.length 0) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
          (mkAppN
            (mkAppN
              (mkAppN
                (.const (Lean.mkRecName indTypes[owner]!.name)
                  (AddInductive.getRecLevels H.elimLevel stats.levels))
                (stats.params.map fun arg =>
                  arg.abstractList A.rule.binders))
              ((H.recInfos.map (·.motive)).map fun arg =>
                arg.abstractList A.rule.binders))
            ((H.recInfos.flatMap (·.minors)).map fun arg =>
              arg.abstractList A.rule.binders))
          ((VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (recursorCanonicalVars
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
          (mkAppN
            (mkAppN
              (.const
                ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
                stats.levels)
              (stats.params.map fun arg =>
                arg.abstractList A.rule.binders))
            (A.rule.allArgs.map fun arg =>
              arg.abstractList A.rule.binders))
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalRecursorPrefixEquationContext with
    ⟨T, fieldDomains, fieldResult, introTarget,
      hparams, hfields, Hctx, Hmajor, Hprefix, Htarget, HintroShape⟩
  have Htr := A.canonicalRecursorPrefixResidualTranslation
    T fieldDomains hfields Hctx Hprefix
  have HmajorTr := A.canonicalConstructorMajorResidualTranslation
    T fieldDomains fieldResult introTarget hfields Hctx Hmajor HintroShape
  exact ⟨T, fieldDomains, fieldResult, introTarget,
    hparams, hfields, Hctx, Hmajor, Hprefix, Htarget, HintroShape, Htr,
    HmajorTr⟩

/-- Move the canonical recursor/constructor frame to the independently
cached parameter context.  Context conversion can in general choose a new
translation target; uniqueness of the closed rule binders shows that both
applications retain the exact abstract terms already typed by the recursor
and constructor phases. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedCanonicalRecursorPrefixFrame
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv Us stats decl
          owner H.recInfos[owner]! H.elimLevel,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        let canonicalDomains :=
          (T.params ++ T.motives ++ T.minors) ++ fieldDomains
        let cachedDomains :=
          (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains
        let added := T.motives ++ T.minors ++ fieldDomains
        let prefixSource :=
          mkAppN
            (mkAppN
              (mkAppN
                (.const (Lean.mkRecName indTypes[owner]!.name)
                  (AddInductive.getRecLevels H.elimLevel stats.levels))
                (stats.params.map fun arg =>
                  arg.abstractList A.rule.binders))
              ((H.recInfos.map (·.motive)).map fun arg =>
                arg.abstractList A.rule.binders))
            ((H.recInfos.flatMap (·.minors)).map fun arg =>
              arg.abstractList A.rule.binders)
        let prefixTarget :=
          (VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (recursorCanonicalVars
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0
        let majorSource :=
          mkAppN
            (mkAppN
              (.const
                ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
                stats.levels)
              (stats.params.map fun arg =>
                arg.abstractList A.rule.binders))
            (A.rule.allArgs.map fun arg =>
              arg.abstractList A.rule.binders)
        let majorTarget :=
          (VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size
        ∃ (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse parameterDecls.toCtx ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            C.params.reverse parameterDecls.toCtx ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            canonicalDomains.reverse cachedDomains.reverse ∧
          OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse majorTarget
            (fieldResult.liftN
              (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse majorTarget
            (VExpr.mkApps (C.family.liftN added.length 0) indexTargets) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse prefixTarget
            ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
              fieldDomains.length 0) ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            (A.rule.target.abstractList A.rule.binders)
            (fieldResult.liftN
              (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
          introTarget = VExpr.mkApps
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              (recursorDeclarationAbstractLevels c.lparams
                H.elimLevelAdmissible))
            (recursorCanonicalVars stats.params.size) ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            prefixSource prefixTarget ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            majorSource majorTarget ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            (H.recInfos[owner]!.motive.abstractList A.rule.binders)
            (.bvar (fieldDomains.length +
              (T.motives.drop (owner + 1) ++ T.minors).length)) ∧
          (fieldResult.liftN
              (T.motives ++ T.minors).length
              A.rule.allArgs.size).getAppFnArgs =
            (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
              parameterTargets ++ indexTargets) ∧
          stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
          levels = recursorDeclarationAbstractLevels c.lparams
            H.elimLevelAdmissible ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext cachedDomains []))
            ((stats.params.map fun arg =>
              arg.abstractList A.rule.binders).toList)
            parameterTargets ∧
          parameterTargets =
            (List.ofFn fun i : Fin stats.params.size =>
              VExpr.bvar (A.rule.binders.length - 1 - i)) ∧
          (let familyTarget :=
              VExpr.mkApps
                (.const (decl.types[owner]'A.abstractOwner_lt).name levels)
                parameterTargets
            let added := T.motives ++ T.minors ++ fieldDomains
            ∃ familyType,
              familyTarget = C.family.liftN added.length 0 ∧
              (fieldResult.liftN
                  (T.motives ++ T.minors).length
                  A.rule.allArgs.size) =
                VExpr.mkApps familyTarget indexTargets ∧
              H.outVEnv.HasType Us.length cachedDomains.reverse
                familyTarget familyType) ∧
          indexTargets.length = T.indices.length ∧
          indexTargets.length = C.indices.length ∧
          (let added := T.motives ++ T.minors ++ fieldDomains
            let ownerTarget := .bvar
              (fieldDomains.length +
                (T.motives.drop (owner + 1) ++ T.minors).length)
            H.outVEnv.HasType Us.length cachedDomains.reverse
              (.app (VExpr.mkApps ownerTarget indexTargets) majorTarget)
              (.sort C.resultLevel)) ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext cachedDomains []))
            (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
              arg.abstractList A.rule.binders).toList)
            indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCanonicalRecursorPrefixFrame with
    ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields, Hctx,
      Hmajor, Hprefix, Htarget, HintroShape, HprefixTr, HmajorTr⟩
  rcases H.finalOwnerCanonicalMotiveDomainAt owner howner with
    ⟨T₀, S, hgeneratedSource, HmotiveDomain₀⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams₀, hmotives₀, _hminors₀, _hindices₀, _hmajor₀, _hresult₀⟩
  rw [hparams₀] at hgeneratedSource
  rw [hparams₀, hmotives₀] at HmotiveDomain₀
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  let C := S.canonical.mono hbase
  have hcanonicalSource : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse S.motiveSourceScope.toCtx := by
    simpa [C, RecursorCanonicalMotiveTelescope.mono] using
      S.motiveSourceAlignment.mono hbase
  have hcanonicalGenerated : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse T.params.reverse :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
      hcanonicalSource
      (hgeneratedSource.symm H.outVEnvWF.ordered)
  have hcanonicalParams : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse parameterDecls.toCtx :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
      hcanonicalGenerated hparams
  have HmotiveDomain : H.outVEnv.IsDefEqU Us.length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      T.motives[owner]!
      (C.motiveType.liftN (T.motives.take owner).length 0) := by
    simpa [C, RecursorCanonicalMotiveTelescope.mono] using HmotiveDomain₀
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  let commonPrefix :=
    fieldDomains.reverse ++ T.minors.reverse ++ T.motives.reverse
  have Hctx' : OnCtx (commonPrefix ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [canonicalDomains, commonPrefix, List.reverse_append,
      List.append_assoc] using Hctx
  have Hfull₀ :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      hparams Hctx'
  have Hfull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      canonicalDomains.reverse cachedDomains.reverse := by
    simpa [canonicalDomains, cachedDomains, commonPrefix,
      List.reverse_append, List.append_assoc] using Hfull₀
  have HcachedCtx : OnCtx cachedDomains.reverse
      (H.outVEnv.IsType Us.length) :=
    (Hfull.symm H.outVEnvWF.ordered).isType
  have HmajorCached := Hmajor.defeqDFC H.outVEnvWF.ordered Hfull
  have HprefixCached := Hprefix.defeqDFC H.outVEnvWF.ordered Hfull
  have Hvlctx := abstractForallContext.isDefEq Hfull
  have hdomainLengths : canonicalDomains.length = cachedDomains.length := by
    simpa using Hfull.length_eq
  have HuniqueCtx := abstractForallContext.isUniqueCtx hdomainLengths
  let prefixSource :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const (Lean.mkRecName indTypes[owner]!.name)
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((H.recInfos.flatMap (·.minors)).map fun arg =>
        arg.abstractList A.rule.binders)
  let prefixTarget :=
    (VExpr.mkApps
        ((VExpr.const recursor.name
          (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0
  have HprefixUnique : TrExprS.IsUnique prefixSource := by
    exact TrExprS.IsUnique.mkAppN
      (TrExprS.IsUnique.mkAppN
        (TrExprS.IsUnique.mkAppN (by trivial)
          (fun arg harg => A.rule.abstractedParamsUnique arg
            (Array.mem_toList_iff.mpr harg)))
        (fun arg harg => A.rule.abstractedMotivesUnique arg
          (Array.mem_toList_iff.mpr harg)))
      (fun arg harg => A.rule.abstractedMinorsUnique arg
        (Array.mem_toList_iff.mpr harg))
  rcases HprefixTr.defeqDFC H.outVEnvWF Hvlctx with
    ⟨prefixTarget', HprefixTr'⟩
  have hprefixTarget : prefixTarget = prefixTarget' :=
    TrExprS.unique' HuniqueCtx HprefixUnique HprefixTr HprefixTr'
  rw [← hprefixTarget] at HprefixTr'
  let majorSource :=
    mkAppN
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        (stats.params.map fun arg =>
          arg.abstractList A.rule.binders))
      (A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders)
  let majorTarget :=
    (VExpr.mkApps
        (introTarget.liftN A.rule.allArgs.size 0)
        (recursorCanonicalVars A.rule.allArgs.size)).liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size
  have HmajorUnique : TrExprS.IsUnique majorSource := by
    exact TrExprS.IsUnique.mkAppN
      (TrExprS.IsUnique.mkAppN (by trivial)
        (fun arg harg => A.rule.abstractedParamsUnique arg
          (Array.mem_toList_iff.mpr harg)))
      (fun arg harg => A.rule.abstractedAllArgsUnique arg
        (Array.mem_toList_iff.mpr harg))
  rcases HmajorTr.defeqDFC H.outVEnvWF Hvlctx with
    ⟨majorTarget', HmajorTr'⟩
  have hmajorTarget : majorTarget = majorTarget' :=
    TrExprS.unique' HuniqueCtx HmajorUnique HmajorTr HmajorTr'
  rw [← hmajorTarget] at HmajorTr'
  rcases A.cachedConstructorIndexSpineOfTarget
      T fieldDomains fieldResult hfields Htarget with
    ⟨levels, parameterTargets, indexTargets, hspine, hlevels,
      HparameterTargets, hindexLength, HindexTargets⟩
  have hcanonicalLevels := R.materialized.recursorLevelTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlevelsCanonical : levels =
      recursorDeclarationAbstractLevels c.lparams
        H.elimLevelAdmissible := by
    exact Option.some.inj (hlevels.symm.trans hcanonicalLevels)
  rcases A.canonicalEquationBinderTranslations T fieldDomains hfields with
    ⟨HcanonicalParameters, HcanonicalMotives, _HcanonicalMinors,
      _HcanonicalFields⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hownerBang : H.recInfos[owner]! = H.recInfos[owner] := by
    simp [Array.getElem!_eq_getD, Array.getD, hownerRecInfo]
  have HownerMotive :=
    Lean4Lean.VerifyInductive.List.Forall₂.getElem HcanonicalMotives owner
      (by simpa using hownerMotive) (by simpa using hownerMotive)
  have HownerMotiveCanonical : TrExprS H.outVEnv Us
      (abstractForallContext canonicalDomains [])
      (H.recInfos[owner]!.motive.abstractList A.rule.binders)
      (.bvar (A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + owner))) := by
    simpa [canonicalDomains, List.append_assoc, hownerBang] using
      HownerMotive
  have HownerMotiveUnique : TrExprS.IsUnique
      (H.recInfos[owner]!.motive.abstractList A.rule.binders) := by
    apply A.rule.abstractedMotivesUnique
    have hownerAbstract : owner <
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders).size := by
      simpa using hownerMotive
    have hmem := Array.getElem_mem
      (xs := (H.recInfos.map (·.motive)).map fun arg =>
        arg.abstractList A.rule.binders) hownerAbstract
    simpa [hownerBang] using hmem
  rcases HownerMotiveCanonical.defeqDFC H.outVEnvWF Hvlctx with
    ⟨ownerMotiveTarget, HownerMotiveCached⟩
  have hownerMotiveTarget :
      VExpr.bvar (A.rule.binders.length - 1 -
          (A.rule.params_bound.fvars.length + owner)) =
        ownerMotiveTarget :=
    TrExprS.unique' HuniqueCtx HownerMotiveUnique
      HownerMotiveCanonical HownerMotiveCached
  rw [← hownerMotiveTarget] at HownerMotiveCached
  rw [A.canonicalOwnerMotiveBvarIndex T fieldDomains hfields] at HownerMotiveCached
  have HownerMotive' : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      (H.recInfos[owner]!.motive.abstractList A.rule.binders)
      (.bvar (fieldDomains.length +
        (T.motives.drop (owner + 1) ++ T.minors).length)) := by
    exact HownerMotiveCached
  have hparameterTargets : parameterTargets =
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (A.rule.binders.length - 1 - i)) := by
    exact (Lean4Lean.VerifyInductive.TrExprS.forall₂_unique HuniqueCtx
      A.rule.abstractedParamsUnique HcanonicalParameters
      HparameterTargets).symm
  let familyTarget := VExpr.mkApps
    (.const (decl.types[owner]'A.abstractOwner_lt).name levels)
    parameterTargets
  let added := T.motives ++ T.minors ++ fieldDomains
  have hcanonicalFamilyLevels : C.levels = levels := by
    exact Option.some.inj (C.levels_translation.symm.trans hlevels)
  have hbindersLength : A.rule.binders.length =
      stats.params.size + added.length := by
    have hdomains := A.canonicalEquationDomains_length
      T fieldDomains hfields
    simp only [canonicalDomains, added, List.length_append,
      T.params_length] at hdomains ⊢
    omega
  have hparameterTargetsLifted : parameterTargets =
      (recursorCanonicalVars stats.params.size).map
        (fun arg => arg.liftN added.length 0) := by
    rw [hparameterTargets,
      recursorCanonicalVars_liftN_zero_eq_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hleft hright
      have hj : j < stats.params.size := by simpa using hright
      simp only [List.getElem_ofFn]
      congr 1
      omega
  have hfamilyTargetCanonical :
      familyTarget = C.family.liftN added.length 0 := by
    dsimp only [familyTarget]
    rw [C.family_eq]
    simp only [C.params_length, VExpr.liftN_mkApps]
    rw [hcanonicalFamilyLevels, hparameterTargetsLifted]
    simp [familyTarget, VExpr.liftN, VExpr.liftN_liftN]
  have hfamilyApplication :
      (fieldResult.liftN
          (T.motives ++ T.minors).length A.rule.allArgs.size) =
        VExpr.mkApps familyTarget indexTargets := by
    have hrebuild := VExpr.mkApps_getAppFnArgs
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size)
    rw [hspine] at hrebuild
    simpa [familyTarget, VExpr.mkApps_append] using hrebuild.symm
  have HmajorCanonical : H.outVEnv.HasType Us.length cachedDomains.reverse
      majorTarget
      (VExpr.mkApps (C.family.liftN added.length 0) indexTargets) := by
    rw [← hfamilyTargetCanonical, ← hfamilyApplication]
    exact HmajorCached
  have hindexCanonical : indexTargets.length = C.indices.length := by
    rw [hindexLength, T.indices_length, C.indices_length]
  let ownerTarget : VExpr := .bvar
    (fieldDomains.length +
      (T.motives.drop (owner + 1) ++ T.minors).length)
  let newer := T.motives.drop owner ++ T.minors ++ fieldDomains
  have hownerT : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerMotive
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have hearlierCtx :
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx =
        (T.params ++ T.motives.take owner).reverse := by
    simpa [abstractForallContext] using
      htoCtx ((T.params ++ T.motives.take owner).reverse)
  have hcanonicalSplit : canonicalDomains.reverse =
      newer.reverse ++
        (T.params ++ T.motives.take owner).reverse := by
    dsimp only [canonicalDomains, newer]
    have hmotives : T.motives =
        T.motives.take owner ++ T.motives.drop owner :=
      (List.take_append_drop owner T.motives).symm
    have hmotivesReverse : T.motives.reverse =
        (T.motives.drop owner).reverse ++
          (T.motives.take owner).reverse := by
      calc
        T.motives.reverse =
            (T.motives.take owner ++ T.motives.drop owner).reverse :=
          congrArg List.reverse hmotives
        _ = (T.motives.drop owner).reverse ++
            (T.motives.take owner).reverse :=
          by simp only [List.reverse_append]
    simp only [List.reverse_append]
    rw [hmotivesReverse]
    simp only [List.append_assoc]
  have Wmotive : Ctx.LiftN newer.length 0
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      canonicalDomains.reverse := by
    rw [hearlierCtx, hcanonicalSplit]
    exact .zero newer.reverse (by simp)
  have HmotiveDomainFull := HmotiveDomain.weakN
    H.outVEnvWF.ordered Wmotive
  have hcanonicalLift :
      (T.motives.take owner).length + newer.length = added.length := by
    simp only [newer, added, List.length_append, List.length_take,
      List.length_drop]
    omega
  have HmotiveDomainCanonical : H.outVEnv.IsDefEqU Us.length
      canonicalDomains.reverse
      (T.motives[owner]!.liftN newer.length 0)
      (C.motiveType.liftN added.length 0) := by
    simpa only [VExpr.liftN_liftN, hcanonicalLift] using
      HmotiveDomainFull
  have HownerOuter := T.ownerMotiveOuterBvarTyping hownerT
  have Wfields : Ctx.LiftN fieldDomains.length 0
      (T.params ++ T.motives ++ T.minors).reverse
      canonicalDomains.reverse := by
    have hcanonicalFields : canonicalDomains.reverse =
        fieldDomains.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse := by
      simp [canonicalDomains, List.reverse_append, List.append_assoc]
    rw [hcanonicalFields]
    exact Ctx.LiftN.zero (n := fieldDomains.length)
      (Γ := (T.params ++ T.motives ++ T.minors).reverse)
      fieldDomains.reverse (by simp)
  have HownerCanonical := HownerOuter.weakN H.outVEnvWF.ordered Wfields
  have HownerCanonical' : H.outVEnv.HasType Us.length
      canonicalDomains.reverse ownerTarget
      (T.motives[owner]!.liftN newer.length 0) := by
    let later := T.motives.drop (owner + 1) ++ T.minors
    have hownerTargetEq :
        (VExpr.bvar later.length).liftN fieldDomains.length 0 =
          ownerTarget := by
      simp only [ownerTarget, later, VExpr.liftN, liftVar_base,
        List.length_append]
    have hownerGet : T.motives[owner]'hownerT = T.motives[owner]! :=
      (getElem!_pos T.motives owner hownerT).symm
    have hownerTypeEq :
        ((T.motives[owner]'hownerT).liftN (later.length + 1) 0).liftN
            fieldDomains.length 0 =
          T.motives[owner]!.liftN newer.length 0 := by
      rw [hownerGet, VExpr.liftN_liftN]
      have hlength : later.length + 1 + fieldDomains.length =
          newer.length := by
        dsimp only [later, newer]
        simp only [List.length_append, List.length_drop]
        omega
      rw [hlength]
    rw [hownerTargetEq, hownerTypeEq] at HownerCanonical
    exact HownerCanonical
  have HownerCached := HownerCanonical'.defeqDFC
    H.outVEnvWF.ordered Hfull
  have HmotiveDomainCached := HmotiveDomainCanonical.defeqDFC
    H.outVEnvWF.ordered Hfull
  have HmotiveCanonical : H.outVEnv.HasType Us.length
      cachedDomains.reverse ownerTarget
      (C.motiveType.liftN added.length 0) :=
    HownerCached.defeqU_r H.outVEnvWF HcachedCtx HmotiveDomainCached
  have HapplyCanonical : H.outVEnv.HasType Us.length cachedDomains.reverse
      (.app (VExpr.mkApps ownerTarget indexTargets) majorTarget)
      (.sort C.resultLevel) := by
    have Happ := C.applyMajorTypedAfterDefEq H.outVEnvWF
      parameterDecls.toCtx added hcanonicalParams
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HcachedCtx)
      indexTargets hindexCanonical ownerTarget majorTarget
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HmotiveCanonical)
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HmajorCanonical)
    simpa [cachedDomains, added, List.reverse_append,
      List.append_assoc] using Happ
  have HfieldResultType := HmajorCached.isType H.outVEnvWF HcachedCtx
  have HfieldResultWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
    rcases HfieldResultType with ⟨fieldLevel, HfieldResultType⟩
    exact ⟨.sort fieldLevel, HfieldResultType⟩
  rw [hfamilyApplication] at HfieldResultWF
  rcases VExpr.WF.mkApps_fn H.outVEnvWF.ordered HcachedCtx
      HfieldResultWF with ⟨familyType, Hfamily⟩
  exact ⟨T, C, fieldDomains, fieldResult, introTarget, levels,
    parameterTargets, indexTargets, hparams, hcanonicalParams, hfields,
    Hfull, HcachedCtx,
    HmajorCached, HmajorCanonical, HprefixCached, Htarget, HintroShape,
    HprefixTr',
    HmajorTr', HownerMotive', hspine, hlevels, hlevelsCanonical,
    HparameterTargets, hparameterTargets,
    (by exact ⟨familyType, hfamilyTargetCanonical,
      hfamilyApplication, Hfamily⟩),
    hindexLength, hindexCanonical, HapplyCanonical, HindexTargets⟩

/-- Complete cached equation left-hand side.  The translated recursor prefix
is applied to the independently recovered constructor indices and major;
canonical-result instantiation identifies its exact type with the parallel
owner-motive application. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedCanonicalLhsBody
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains lhsBody typeBody,
        let cachedDomains :=
          (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse lhsBody typeBody ∧
        H.outVEnv.IsType Us.length cachedDomains.reverse typeBody ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          ((Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats A.rule.target).2)
            A.rule.sourceConstructorMajor).abstractList A.rule.binders)
          typeBody := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCachedCanonicalRecursorPrefixFrame with
    ⟨T, C, fieldDomains, fieldResult, introTarget, levels,
      parameterTargets, indexTargets, hparams, hcanonicalParams, hfields,
      Hfull, HcachedCtx, HmajorCached, HmajorCanonical, HprefixCached,
      Htarget, HintroShape, HprefixTr, HmajorTr, HownerMotiveTr, hspine,
      hlevels, hlevelsCanonical, HparameterTargets, hparameterTargets,
      Hfamily, hindexLength, hindexCanonical, HapplyCanonical,
      HindexTargets⟩
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  let prefixSource :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const (Lean.mkRecName indTypes[owner]!.name)
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((H.recInfos.flatMap (·.minors)).map fun arg =>
        arg.abstractList A.rule.binders)
  let prefixTarget :=
    (VExpr.mkApps
        ((VExpr.const H.entries[owner].2.name
          (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0
  let majorSource :=
    mkAppN
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        (stats.params.map fun arg =>
          arg.abstractList A.rule.binders))
      (A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders)
  let majorTarget :=
    (VExpr.mkApps
        (introTarget.liftN A.rule.allArgs.size 0)
        (recursorCanonicalVars A.rule.allArgs.size)).liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size
  let ownerTarget : VExpr := .bvar
    (fieldDomains.length +
      (T.motives.drop (owner + 1) ++ T.minors).length)
  let args := indexTargets ++ [majorTarget]
  let lhsBody := VExpr.mkApps prefixTarget args
  let typeBody := VExpr.mkApps ownerTarget args
  rcases A.finalCachedPrefixOwnerTelescope T fieldDomains prefixTarget
      Hfull HcachedCtx HprefixCached with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
      HprefixExpected, HownerExpected, Hsame⟩
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix fieldDomains.length expected.reverse).reverse
  have hargsLength : args.length = expectedDomains.length := by
    simp only [args, expectedDomains, expected, List.length_append,
      List.length_singleton, List.length_reverse, liftContextPrefix_length,
      liftContextPrefixAt_length, hindexLength, T.indices_length,
      hdomainLength]
  have Hsame' : SameTelescopeDomains args.length
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length))
      (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
    simpa [suffix, later, expected, expectedDomains, hargsLength] using Hsame
  have HrightWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      (VExpr.mkApps ownerTarget args) := by
    refine ⟨.sort C.resultLevel, ?_⟩
    change H.outVEnv.HasType Us.length cachedDomains.reverse
      (VExpr.mkApps ownerTarget args) (.sort C.resultLevel)
    have hshape : VExpr.mkApps ownerTarget args =
        .app (VExpr.mkApps ownerTarget indexTargets) majorTarget := by
      simp [args, VExpr.mkApps_append, VExpr.mkApps]
    rw [hshape]
    simpa only [Us, cachedDomains, parameterDecls, ownerTarget,
      majorTarget, List.reverse_append, List.reverse_reverse,
      List.append_assoc] using HapplyCanonical
  have Hlhs := VEnv.HasType.mkApps_sameTelescopeDomains_exact
    H.outVEnvWF HcachedCtx Hsame' HprefixExpected HownerExpected HrightWF
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hsuffixLength : suffix.length = expectedDomains.length := by
    simp only [suffix, expectedDomains, expected, List.length_append,
      List.length_reverse, liftContextPrefix_length,
      liftContextPrefixAt_length, T.indices_length, T.major_length,
      hdomainLength]
  have hexpectedArity :
      expectedDomains.length = H.recInfos[owner]!.indices.size + 1 := by
    rw [← hsuffixLength]
    simp [suffix, T.indices_length, T.major_length]
  have hresultCanonical : T.result.liftN fieldDomains.length suffix.length =
      VExpr.mkApps (ownerTarget.liftN expectedDomains.length 0)
        (recursorCanonicalVars expectedDomains.length) := by
    rw [T.resultShape hownerMotive,
      concreteRecursorResultArgs_eq_canonical]
    rw [VExpr.liftN_mkApps]
    rw [hsuffixLength]
    congr 1
    · simp only [ownerTarget, VExpr.liftN]
      congr 1
      have hcut : expectedDomains.length ≤
          1 + H.recInfos[owner]!.indices.size +
            (H.recInfos.flatMap (·.minors)).size +
            ((H.recInfos.map (·.motive)).size - 1 - owner) := by
        rw [← hsuffixLength]
        simp only [suffix, List.length_append, T.indices_length,
          T.major_length]
        omega
      rw [liftVar_le hcut]
      rw [liftVar_base]
      simp only [suffix, later,
        List.length_append, List.length_drop, T.indices_length, T.major_length,
        T.minors_length, T.motives_length]
      omega
    · rw [hexpectedArity]
      exact recursorCanonicalVars_liftN_at_length _ _
  rw [hresultCanonical] at Hlhs
  have htypeResult := VExpr.applyForallType_wrapForalls_canonical
    expectedDomains args ownerTarget hargsLength
  rw [htypeResult] at Hlhs
  have Hlhs' : H.outVEnv.HasType Us.length cachedDomains.reverse
      lhsBody typeBody := by
    simpa only [Us, cachedDomains, parameterDecls, lhsBody, typeBody,
      List.reverse_append, List.append_assoc] using Hlhs
  have HtypeBody : H.outVEnv.IsType Us.length cachedDomains.reverse
      typeBody := by
    refine ⟨C.resultLevel, ?_⟩
    change H.outVEnv.HasType Us.length cachedDomains.reverse
      typeBody (.sort C.resultLevel)
    have hshape : typeBody =
        .app (VExpr.mkApps ownerTarget indexTargets) majorTarget := by
      simp [typeBody, args, VExpr.mkApps_append, VExpr.mkApps]
    rw [hshape]
    simpa only [Us, cachedDomains, parameterDecls, ownerTarget,
      majorTarget, List.reverse_append, List.reverse_reverse,
      List.append_assoc] using HapplyCanonical
  have HargsTr := Lean4Lean.VerifyInductive.List.Forall₂.append'
    HindexTargets (List.Forall₂.cons HmajorTr List.Forall₂.nil)
  have HlhsWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      lhsBody := ⟨typeBody, Hlhs'⟩
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have HabstractCtx : OnCtx
      (abstractForallContext cachedDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HcachedCtx
  have HlhsWF' : VExpr.WF H.outVEnv Us.length
      (abstractForallContext cachedDomains []).toCtx lhsBody := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HlhsWF
  have HrightWF' : VExpr.WF H.outVEnv Us.length
      (abstractForallContext cachedDomains []).toCtx
      (VExpr.mkApps ownerTarget args) := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HrightWF
  have HlhsTr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered HabstractCtx HprefixTr HargsTr (by
      simpa only [lhsBody, args, prefixTarget, majorTarget,
        List.length_append] using HlhsWF')
  have HlhsResidual : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    have hsourceShape := A.rule.abstractedSourceLhs
    rcases htarget : AddInductive.getIIndices stats A.rule.target with
      ⟨selectedOwner, sourceIndices⟩
    have hselectedOwner : selectedOwner = owner := by
      have hfirst := checkPositivityStep.getIIndices.fst_eq_of_valid
        A.semantics.target_valid
      rw [htarget] at hfirst
      exact hfirst.trans A.semantic_owner
    subst selectedOwner
    rw [htarget] at hsourceShape HlhsTr
    rw [hsourceShape]
    simpa [prefixSource, majorSource, lhsBody, args,
      prefixTarget, majorTarget,
      Expr.mkAppN_eq_mkAppList, VExpr.mkApps_append,
      getElem!_pos indTypes owner A.sourceOwner_lt] using HlhsTr
  have HtypeTranslation₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered HabstractCtx HownerMotiveTr HargsTr HrightWF'
  have HtypeTranslation : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      ((Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats A.rule.target).2)
        A.rule.sourceConstructorMajor).abstractList A.rule.binders)
      typeBody := by
    unfold BoundGeneratedRecursorRule.sourceConstructorMajor
    simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
    simpa [typeBody, ownerTarget, args, majorSource, majorTarget,
      Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.mkAppN_eq_mkAppList, VExpr.mkApps_append, VExpr.mkApps,
      getElem!_pos indTypes owner A.sourceOwner_lt] using
      HtypeTranslation₀
  exact ⟨T, fieldDomains, lhsBody, typeBody, hfields, HcachedCtx,
    HlhsResidual, Hlhs', HtypeBody, HtypeTranslation⟩

/-- Witness-stable form of `finalCachedCanonicalLhsBody`.  A final equation
already carries the telescope selected by its RHS construction, so transport
the independently reconstructed LHS frame to that exact decomposition. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedCanonicalLhsBodyFor
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
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ fieldDomains lhsBody typeBody,
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse lhsBody typeBody ∧
        H.outVEnv.IsType Us.length cachedDomains.reverse typeBody ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          ((Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats A.rule.target).2)
            A.rule.sourceConstructorMajor).abstractList A.rule.binders)
          typeBody := by
  dsimp only
  rcases A.finalCachedCanonicalLhsBody with
    ⟨T₀, fieldDomains, lhsBody, typeBody, hfields, Hctx,
      Htranslation, Htyping, Htype, HtypeTranslation⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hmotives, hminors] at Hctx Htranslation Htyping Htype HtypeTranslation
  exact ⟨fieldDomains, lhsBody, typeBody, hfields, Hctx,
    Htranslation, Htyping, Htype, HtypeTranslation⟩

/-- Extend the completed cached left-hand-side frame with the exact minor
variable selected by this constructor.  Its de Bruijn offset is the number
of constructor fields plus the number of later flattened minors, exactly as
in `abstractedSourceRhsAtMinorArray`; its lookup type is the corresponding
generated minor domain weakened below itself, those later minors, and the
constructor fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedCanonicalMinorFrame
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains lhsBody typeBody,
        let cachedDomains :=
          (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := fieldDomains.length + later.length
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse lhsBody typeBody ∧
        H.outVEnv.IsType Us.length cachedDomains.reverse typeBody ∧
        minorIdx < T.minors.length ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse (.bvar minorVar)
          (T.minors[minorIdx]!.liftN
            (later.length + 1 + fieldDomains.length) 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCachedCanonicalLhsBody with
    ⟨T, fieldDomains, lhsBody, typeBody, hfields, HcachedCtx,
      HlhsResidual, Hlhs, HtypeBody, _HtypeTranslation⟩
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := fieldDomains.length + later.length
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  let older := (T.minors.take minorIdx).reverse ++
    T.motives.reverse ++ parameterDecls.toCtx
  have hsplit : T.minors = T.minors.take minorIdx ++
      T.minors[minorIdx] :: T.minors.drop (minorIdx + 1) := by
    calc
      T.minors = T.minors.take (minorIdx + 1) ++
          T.minors.drop (minorIdx + 1) :=
        (List.take_append_drop (minorIdx + 1) T.minors).symm
      _ = (T.minors.take minorIdx ++ [T.minors[minorIdx]]) ++
          T.minors.drop (minorIdx + 1) := by
        rw [List.take_append_getElem hminor]
      _ = T.minors.take minorIdx ++ T.minors[minorIdx] ::
          T.minors.drop (minorIdx + 1) := by
        simp [List.append_assoc]
  have hminorsReverse : T.minors.reverse = later.reverse ++
      T.minors[minorIdx] :: (T.minors.take minorIdx).reverse := by
    simpa [later, List.reverse_append, List.append_assoc] using
      congrArg List.reverse hsplit
  have hcontext : cachedDomains.reverse =
      (fieldDomains.reverse ++ later.reverse) ++
        T.minors[minorIdx] :: older := by
    dsimp only [cachedDomains, older]
    rw [List.reverse_append, List.reverse_append, List.reverse_append,
      hminorsReverse]
    simp [List.append_assoc]
  have hlookup : Lookup
      ((fieldDomains.reverse ++ later.reverse) ++
        T.minors[minorIdx] :: older)
      minorVar
      (T.minors[minorIdx]!.liftN
        (later.length + 1 + fieldDomains.length) 0) := by
    have hselected : T.minors[minorIdx] = T.minors[minorIdx]! := by
      exact (getElem!_pos T.minors minorIdx hminor).symm
    rw [← hselected]
    have Hlookup := Lookup.append_zero
      (fieldDomains.reverse ++ later.reverse)
      (T.minors[minorIdx]'hminor) older
    simpa only [minorVar, List.length_append, List.length_reverse,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hlookup
  have Hminor : H.outVEnv.HasType Us.length cachedDomains.reverse
      (.bvar minorVar)
      (T.minors[minorIdx]!.liftN
        (later.length + 1 + fieldDomains.length) 0) := by
    apply VEnv.HasType.bvar
    rw [hcontext]
    exact hlookup
  exact ⟨T, fieldDomains, lhsBody, typeBody, hfields, HcachedCtx,
    HlhsResidual, Hlhs, HtypeBody, hminor, Hminor⟩

/-- Canonical-domain specialization of `equationWitnessOfBodies`.  The
common prefix is taken from the independently typed recursor telescope and
only the constructor-field suffix remains local to the generated rule. -/
def RecursorPhasesResult.GeneratedRuleAlignment.equationWitnessOfCanonicalBodies
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
    (fieldDomains : List VExpr) (lhsBody rhsBody typeBody : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hlhsResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody)
    (hrhsResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType H.entries[owner].2.uvars))
    (hlhs : H.outVEnv.HasType H.entries[owner].2.uvars
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      lhsBody typeBody)
    (hrhs : H.outVEnv.HasType H.entries[owner].2.uvars
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      rhsBody typeBody) :
    H.GeneratedEquationWitness
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      owner howner i hctor
      (A.abstractEquation
        ((T.params ++ T.motives ++ T.minors) ++ fieldDomains)
        lhsBody rhsBody typeBody) := by
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  exact A.equationWitnessOfBodies
    ((T.params ++ T.motives ++ T.minors) ++ fieldDomains)
    lhsBody rhsBody typeBody hdomains hlhsResidual hrhsResidual hctx
    hlhs hrhs

/-- Cached-parameter specialization of `equationWitnessOfBodies`.  This is
the final equation interface used by the independently checked constructor
and recursor frames: executable parameter domains no longer occur in the
abstract specification equation. -/
def RecursorPhasesResult.GeneratedRuleAlignment.equationWitnessOfCachedBodies
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
    (fieldDomains : List VExpr) (lhsBody rhsBody typeBody : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hlhsResidual :
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains) [])
        (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody)
    (hrhsResidual :
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains) [])
        (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody)
    (hctx :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      OnCtx
        (((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains).reverse) (H.outVEnv.IsType Us.length))
    (hlhs :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      H.outVEnv.HasType Us.length
        (((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains).reverse) lhsBody typeBody)
    (hrhs :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      H.outVEnv.HasType Us.length
        (((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains).reverse) rhsBody typeBody) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    H.GeneratedEquationWitness Us owner howner i hctor
      (A.abstractEquation
        ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains) lhsBody rhsBody typeBody) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let domains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++ fieldDomains
  have hdomains := A.cachedEquationDomains_length T fieldDomains hfields
  have huvars := A.recursorUvars
  apply A.equationWitnessOfBodies domains lhsBody rhsBody typeBody hdomains
      hlhsResidual hrhsResidual
  · simpa only [Us, domains, parameterDecls, huvars] using hctx
  · simpa only [Us, domains, parameterDecls, huvars] using hlhs
  · simpa only [Us, domains, parameterDecls, huvars] using hrhs

/-- Owner-prefix accumulation of reconstructed equations and their typing
proofs.  Keeping the equation traversal independent of the final block lets
this invariant grow in exactly the order used by `declareRecursors`. -/
structure RecursorPhasesResult.GeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name)
    (owner : Nat) (rules : List VDefEq) : Prop where
  equations : H.GeneratedIotaEquationTranslations Us [] owner rules
  rulesWF : ∀ rule ∈ rules, rule.WF H.outVEnv

def RecursorPhasesResult.GeneratedEquationBuild.empty
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name) :
    H.GeneratedEquationBuild Us 0 [] where
  equations := .nil
  rulesWF _ h := by simp at h

theorem RecursorPhasesResult.GeneratedEquationBuild.appendOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {prior : List VDefEq}
    (T : H.GeneratedEquationBuild Us owner prior)
    (howner : owner < H.entries.length)
    (batch : List VDefEq)
    (hlength : batch.length =
      (H.generated.entry owner howner).info.rules.length)
    (Hwitness : ∀ i
      (hctor : i < indTypes[owner]!.ctors.length)
      (hsource : i < (H.generated.entry owner howner).info.rules.length)
      (habstract : i < batch.length),
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor
        batch[i])) :
    H.GeneratedEquationBuild Us (owner + 1) (prior ++ batch) := by
  let E := H.generated.entry owner howner
  have hsourceOwner : owner < indTypes.size := by
    have hrec : owner < H.recInfos.size := by
      simpa [H.generated.length] using howner
    have htypes : H.recInfos.size = indTypes.size := by
      rw [H.cardinality.records]
      simpa using
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
    omega
  have hpriorLength : prior.length = recursorMinorOffset indTypes owner :=
    T.equations.ruleLength
  have hbatchLength : batch.length = indTypes[owner]!.ctors.length := by
    rw [hlength, E.rules.length]
  have hconcreteRoom := recursorMinorOffset_room indTypes owner hsourceOwner
  have hownedLength :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        decl.ownedConstructors.length := by
    simpa [ownedConstructors, List.length_flatMap] using
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
        R.core
  have hroom : batch.length + prior.length ≤
      decl.ownedConstructors.length := by
    rw [hbatchLength, hpriorLength, ← hownedLength]
    omega
  refine { equations := ?_, rulesWF := ?_ }
  · exact .cons T.equations howner batch hlength hroom (by
    intro i hctor hsource habstract _hindex
    rcases Hwitness i hctor hsource habstract with ⟨W⟩
    exact ⟨W.alignment, ⟨W.translation⟩, W.uvars⟩)
  · intro rule hrule
    rcases List.mem_append.mp hrule with hprior | hbatch
    · exact T.rulesWF rule hprior
    · rcases List.mem_iff_getElem.mp hbatch with ⟨i, hi, heq⟩
      have hsource : i <
          (H.generated.entry owner howner).info.rules.length := by
        rw [← hlength]
        exact hi
      have hctor : i < indTypes[owner]!.ctors.length := by
        rw [← E.rules.length]
        exact hsource
      rcases Hwitness i hctor hsource hi with ⟨W⟩
      rw [← heq]
      exact W.wf

/-- Pointwise reconstruction suffices to build the complete flattened rule
list.  The list itself is chosen in the production owner/constructor order;
length, coverage, and well-formedness are accumulated by
`GeneratedEquationBuild`. -/
theorem RecursorPhasesResult.existsGeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name)
    (Hpoint : ∀ owner (howner : owner < H.entries.length)
      i (hctor : i < indTypes[owner]!.ctors.length),
      ∃ rule : VDefEq,
        Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule)) :
    ∃ rules : List VDefEq,
      Nonempty (H.GeneratedEquationBuild Us H.entries.length rules) := by
  classical
  have go : ∀ owner, owner ≤ H.entries.length →
      ∃ rules : List VDefEq,
        Nonempty (H.GeneratedEquationBuild Us owner rules) := by
    intro owner hcovered
    induction owner with
    | zero => exact ⟨[], ⟨.empty H Us⟩⟩
    | succ owner ih =>
      have howner : owner < H.entries.length := by omega
      rcases ih (by omega) with ⟨prior, ⟨T⟩⟩
      let E := H.generated.entry owner howner
      let sourceCtorBound : ∀ j : Fin E.info.rules.length,
          j.1 < indTypes[owner]!.ctors.length := fun j => by
        rw [← E.rules.length]
        exact j.2
      let selected : Fin E.info.rules.length → VDefEq := fun j =>
        Classical.choose (Hpoint owner howner j.1 (sourceCtorBound j))
      let batch : List VDefEq := List.ofFn selected
      have hlength : batch.length = E.info.rules.length := by
        simp [batch]
      have Hwitness : ∀ i
          (hctor : i < indTypes[owner]!.ctors.length)
          (hsource : i < E.info.rules.length)
          (habstract : i < batch.length),
          Nonempty (H.GeneratedEquationWitness Us owner howner i hctor
            batch[i]) := by
        intro i hctor hsource habstract
        let j : Fin E.info.rules.length := ⟨i, hsource⟩
        have Hselected :=
          Classical.choose_spec (Hpoint owner howner j.1
            (sourceCtorBound j))
        simpa [batch, selected, j] using Hselected
      exact ⟨prior ++ batch, ⟨T.appendOwner howner batch hlength
        Hwitness⟩⟩
  exact go H.entries.length (Nat.le_refl _)

/-- Declaration-facing package for the remaining concrete equation
translations of an ordinary recursor run.  Field selection, recursive-call
semantics, recursor presence, and pre-installation freshness are all derived
from `RecursorPhasesResult`; callers retain only post-installation equation
translation plus the opaque projection-preservation boundary. -/
structure OrdinaryRuleTranslationResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) where
  Us : List Name
  Δ : VLCtx
  rules : List VDefEq
  rulesWF : ∀ df ∈ rules, df.WF H.outVEnv
  owner : Nat
  equations : H.GeneratedIotaEquationTranslations Us Δ owner rules
  contextFree : VLCtx.NoIndConsts
    ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) Δ
  projections : ∀ {Delta : VLCtx} {s j e' e''},
    TrProj Delta.toCtx s j e' e'' →
    e'.containsAnyConst
      ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) =
        false →
    e''.containsAnyConst
      ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) =
        false
  complete : owner = H.entries.length

def RecursorPhasesResult.GeneratedEquationBuild.ordinaryResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {rules : List VDefEq}
    (T : H.GeneratedEquationBuild Us owner rules)
    (hcomplete : owner = H.entries.length)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst
        ((H.blockCertificate rules T.rulesWF).block.recursors.map
          (·.name)) = false →
      e''.containsAnyConst
        ((H.blockCertificate rules T.rulesWF).block.recursors.map
          (·.name)) = false) :
    OrdinaryRuleTranslationResult H where
  Us := Us
  Δ := []
  rules := rules
  rulesWF := T.rulesWF
  owner := owner
  equations := T.equations
  contextFree := by
    intro v mapped type hfind
    simp [VLCtx.find?] at hfind
  projections := hproj
  complete := hcomplete

theorem OrdinaryRuleTranslationResult.compilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    (T : OrdinaryRuleTranslationResult H) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate T.rules T.rulesWF).block :=
  H.ordinaryCompilationOfRuleBuild T.rules T.rulesWF
    (T.equations.build T.rules T.rulesWF T.contextFree T.projections)
    (T.equations.completeLength T.complete)

theorem RecursorPhasesResult.addInductOfOrdinaryCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfOrdinaryCompilation
    R.formation R.core hnonempty Hcompile

theorem RecursorPhasesResult.addInductOfNestedCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfNestedCompilation
    R.formation R.core hnonempty Hcompile

/-- Concrete-environment endpoint for an ordinary executable recursor run.
The staged installation, formation, source typing, and compilation proof now
enter `TrEnv'` in one step. -/
theorem RecursorPhasesResult.trEnvOfOrdinaryCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block)
    (htr : TrEnv' c.safety c.env.constants c.env.quotInit sourceEnv)
    (heq : ∀ info, outEnv.constants.find? ``Eq = some (.inductInfo info) →
      (H.outVEnv.addDefEqRules rules).constants ``Eq = some eqConst) :
    TrEnv' c.safety outEnv.constants c.env.quotInit
      (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).trEnvOfOrdinaryCompilation R.formation
    R.core hnonempty Hcompile htr heq

/-- Nested-compilation counterpart of `trEnvOfOrdinaryCompilation`. -/
theorem RecursorPhasesResult.trEnvOfNestedCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block)
    (htr : TrEnv' c.safety c.env.constants c.env.quotInit sourceEnv)
    (heq : ∀ info, outEnv.constants.find? ``Eq = some (.inductInfo info) →
      (H.outVEnv.addDefEqRules rules).constants ``Eq = some eqConst) :
    TrEnv' c.safety outEnv.constants c.env.quotInit
      (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).trEnvOfNestedCompilation R.formation
    R.core hnonempty Hcompile htr heq

/-- Compositional verifier for the complete production computation after
`checkInductiveTypes` has materialized `stats`. This is the first boundary
whose executable side contains every ordinary installation phase. -/
theorem AddInductive.runWithStats.WF
    (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (Hformation :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun ctorEnv => ∃ headerEnv : Environment,
          ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe
            depth sourceEnv indTypes headerEnv,
          ∃ _ : ConstructorPhasesResult Hheaders ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hwhnf : WhnfLParamsCompat)
    (hfieldReplay : RecursorFieldDecisionReplayCompat)
    (hloopUArgsReplay : RecursorLoopUArgsReplayCompat)
    (hrecConsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
          sourceEnv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) := by
  unfold AddInductive.runWithStats
  have Hcombined := Hformation.bind fun ctorEnv Hresult => by
      rcases Hresult with ⟨headerEnv, Hheaders, R, hclosed⟩
      exact (R.recursorPhasesWF hclosed hlparams hwhnf hfieldReplay
        hloopUArgsReplay hrecConsume hlit hproj hnotPartial hnprim).mono
          fun outEnv Hrecursors =>
            show ∃ headerEnv ctorEnv,
              ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
                isUnsafe depth sourceEnv indTypes headerEnv,
              ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
                Nonempty (RecursorPhasesResult R outEnv)
            from ⟨headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

/-- End-to-end post-analysis verifier specialized with the verified
header/constructor formation pipeline.  Generated recursor types are checked
by the executable pipeline itself, leaving only its production freshness and
formation side conditions. -/
theorem AddInductive.runWithStats.closedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlparams : c.lparams.Nodup)
    (hwhnf : WhnfLParamsCompat)
    (hfieldReplay : RecursorFieldDecisionReplayCompat)
    (hloopUArgsReplay : RecursorLoopUArgsReplayCompat)
    (hrecConsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel)
    (hnprimCtors : ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hnotPartial : c.safety ≠ .partial)
    (hnprimRecursors : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats numParams indTypes numNested isUnsafe c).WF
      fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) := by
  apply AddInductive.runWithStats.WF stats numParams indTypes numNested
    isUnsafe c
  · exact AddInductive.formationCore.closedWF Hc Hclosed Hdecl Hmaterialized
      hvisible hnprimTypes Hfresh hconsume hlit hproj hunsafe hbound hnprimCtors
  · exact hlparams
  · exact hwhnf
  · exact hfieldReplay
  · exact hloopUArgsReplay
  · exact hrecConsume
  · exact hlit
  · exact hproj
  · exact hnotPartial
  · exact hnprimRecursors

/-- The production universe-parameter guard succeeds only for a duplicate-free
parameter list. -/
theorem Kernel.Environment.checkDuplicatedUnivParams.WF
    (lparams : List Name) :
    (Kernel.Environment.checkDuplicatedUnivParams lparams).WF
      (fun _ => lparams.Nodup) := by
  induction lparams with
  | nil =>
    intro out hout
    cases hout
    trivial
  | cons param lparams ih =>
    by_cases hmem : param ∈ lparams
    · rw [Kernel.Environment.checkDuplicatedUnivParams]
      simp only [hmem, if_pos, Except.bind]
      exact Except.WF.throw
    · simpa [Kernel.Environment.checkDuplicatedUnivParams, hmem] using
        ih.mono fun _ htail => List.nodup_cons.mpr ⟨hmem, htail⟩

/-- Front-end composition for `AddInductive.run`: the executable header
analysis materializes an independent declaration before the post-analysis
installer is invoked. This theorem deliberately leaves the latter callback
parametric, so environment conservation and formation assumptions are visible
at their exact boundary. -/
theorem AddInductive.run.materialize
    (numNested : Nat) (Q : Environment → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      types.toArray.toList (c.safety != .safe) skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat},
      (Hc' : ContextWF c') →
      TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (c.safety != .safe) decl envTypes →
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth →
      c'.lparams.Nodup →
      (AddInductive.runWithStats stats skeleton.nparams types.toArray
        numNested (c.safety != .safe) c').WF Q) :
    (AddInductive.run skeleton.nparams types numNested c).WF Q := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply Lean4Lean.VerifyInductive.checkInductiveTypes.loopInd.checkInductiveTypes.materialize
      (fun stats => AddInductive.runWithStats stats skeleton.nparams
        types.toArray numNested (c.safety != .safe)) Q Hc Hdecl hctx hnonempty
      hconsume
    intro c' stats decl depth Hc' hlparamsEq Hdecl' Hmaterialized
    apply Hfinish Hc' Hdecl' Hmaterialized
    simpa [hlparamsEq] using hnodup
  simpa [AddInductive.run] using Hcombined

/-- The explicit semantic/freshness inputs needed to verify one set of
statistics materialized by `checkInductiveTypes`. Keeping this bundle indexed
by the materialization prevents any implementation-derived declaration from
being substituted silently. -/
structure RunWithStatsVerificationInputs
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (numParams depth numNested : Nat)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth) : Prop where
  closed : MutualInductivesClosed c.env
  visible : c.safety ≤
    (if isUnsafe then DefinitionSafety.unsafe else .safe)
  freshTypes : ∀ info ∈
    (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
      isUnsafe c.lparams).toList,
    ¬ Kernel.Environment.primitives.contains info.name
  freshConstructors : ∀ targetIdx (htarget : targetIdx < indTypes.size)
    {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
    (hi : i < indTypes[targetIdx].ctors.length) →
    found.contains indTypes[targetIdx].ctors[i].name = false
  consume : ConsumeTypeAnnotationsCompat
  whnfLParams : WhnfLParamsCompat
  recursiveFieldReplay : RecursorFieldDecisionReplayCompat
  loopUArgsReplay : RecursorLoopUArgsReplayCompat
  recursorConsume : RecursorConsumeTypeAnnotationsCompat
  literalDisjoint : checkPositivityStep.LiteralDisjoint stats.indConsts
  projections : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
    e'.containsAnyConst (decl.types.map (·.name)) = false →
    e''.containsAnyConst (decl.types.map (·.name)) = false
  unsafeDecl : isUnsafe = true → decl.isUnsafe = true
  universeBound : ∀ targetIdx (hi : targetIdx < decl.types.length)
    fieldLevel fieldLevel',
    VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
    (stats.resultLevel.isAlwaysZero ||
      stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
    decl.types[targetIdx].resultLevel = .zero ∨
      fieldLevel' ≤ decl.types[targetIdx].resultLevel
  freshConstructorConstants : ∀ owner ∈ indTypes.toList,
    ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name
  notPartial : c.safety ≠ .partial
  freshRecursors : ∀ owner (howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)

theorem RunWithStatsVerificationInputs.verify
    (H : RunWithStatsVerificationInputs c stats decl numParams depth
      numNested indTypes isUnsafe Hc Hdecl Hmaterialized) :
    c.lparams.Nodup →
    (AddInductive.runWithStats stats numParams indTypes numNested isUnsafe
      c).WF fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) :=
  fun hlparams => AddInductive.runWithStats.closedWF Hc H.closed Hdecl
    Hmaterialized H.visible H.freshTypes H.freshConstructors H.consume
    hlparams H.whnfLParams H.recursiveFieldReplay H.loopUArgsReplay
    H.recursorConsume
    H.literalDisjoint H.projections
    H.unsafeDecl H.universeBound H.freshConstructorConstants H.notPartial
    H.freshRecursors

/-- Declaration-facing successful result of the complete ordinary executable
checker, including the independently materialized declaration and the exact
installed recursor phase. -/
def VerifiedInductiveRunResult
    (source : AddInductive.Context) (skeleton : VInductDeclSkeleton)
    (envTypes : VEnv) (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats decl depth,
    ∃ Hc' : ContextWF c',
    ∃ Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
      types.toArray.toList (source.safety != .safe) decl envTypes,
    ∃ Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth,
    ∃ headerEnv ctorEnv,
    ∃ Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
      (source.safety != .safe) depth Hc'.venv types.toArray headerEnv,
    ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
      types.toArray.toList ≠ [] ∧
      Nonempty (RecursorPhasesResult R outEnv)

theorem AddInductive.run.closedWF
    (numNested : Nat)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      types.toArray.toList (c.safety != .safe) skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat}
      (Hc' : ContextWF c')
      (Hdecl' : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (c.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth),
      RunWithStatsVerificationInputs c' stats decl skeleton.nparams depth
        numNested types.toArray (c.safety != .safe) Hc' Hdecl'
        Hmaterialized) :
    (AddInductive.run skeleton.nparams types numNested c).WF
      (VerifiedInductiveRunResult c skeleton envTypes types numNested) := by
  apply AddInductive.run.materialize numNested
    (VerifiedInductiveRunResult c skeleton envTypes types numNested)
    Hc Hdecl hctx hnonempty hconsume
  intro c' stats decl depth Hc' Hdecl' Hmaterialized hlparamsNodup
  exact ((Hinputs Hc' Hdecl' Hmaterialized).verify hlparamsNodup).mono
    fun outEnv Hout => by
      rcases Hout with ⟨headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
      exact ⟨c', stats, decl, depth, Hc', Hdecl', Hmaterialized,
        headerEnv, ctorEnv, Hheaders, R, by
          simpa using List.ne_nil_of_length_pos
            (by simpa using hnonempty : 0 < types.length),
        Hrecursors⟩

/-- Close a successful ordinary declaration run from the exact generated
rule translations retained per mutual-family owner. -/
theorem VerifiedInductiveRunResult.addInductOfRuleTranslations
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hrules : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      Nonempty (OrdinaryRuleTranslationResult Hrecursors)) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hrules c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
      ctorEnv Hheaders R Hrecursors with ⟨T⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules T.rules,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      T.compilation⟩

/-- Close a verified ordinary executable run against the independent
`VEnv.AddInduct` specification once the generated rule batch and compilation
certificate are supplied. -/
theorem VerifiedInductiveRunResult.addInductOfRuleBuild
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hrules : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        IotaBuildCertificate R.declared.venvCtors decl
          (Hrecursors.blockCertificate rules hrules).block rules ∧
        rules.length = decl.ownedConstructors.length) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hrules c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
      ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, HruleBuild, hrulesLength⟩
  have Hcompile := Hrecursors.ordinaryCompilationOfRuleBuild rules hrules
    HruleBuild hrulesLength
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfOrdinaryCompilation rules hrules hnonempty
      Hcompile⟩

theorem VerifiedInductiveRunResult.addInductOfOrdinaryCompilation
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hcompile : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        OrdinaryCompilationCertificate Hc'.venv decl
          (Hrecursors.blockCertificate rules hrules).block) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hcompile c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
    ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, Hcompilation⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfOrdinaryCompilation rules hrules hnonempty
      Hcompilation⟩

/-- Nested counterpart of
`VerifiedInductiveRunResult.addInductOfOrdinaryCompilation`. -/
theorem VerifiedInductiveRunResult.addInductOfNestedCompilation
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hcompile : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        Nonempty (NestedCompilationCertificate Hc'.venv decl
          (Hrecursors.blockCertificate rules hrules).block)) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hcompile c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
    ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, ⟨Hcompilation⟩⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfNestedCompilation rules hrules hnonempty
      Hcompilation⟩

/-- Exact branch certificate for the production post-lowering pipeline. -/
inductive AddInductiveAfterLoweringResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (Installed : Environment → Prop)
    (Restored : Environment → Environment → Prop) :
    Environment → Prop
  | ordinary : res.aux2nested.size = 0 → Installed outEnv →
      AddInductiveAfterLoweringResult res Installed Restored outEnv
  | nested : res.aux2nested.size ≠ 0 → Installed loweredEnv →
      Restored loweredEnv outEnv →
      AddInductiveAfterLoweringResult res Installed Restored outEnv

/-- Compositional verifier for the exact ordinary/nested branch in
`Environment.addInductiveAfterLowering`. -/
theorem Environment.addInductiveAfterLowering.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (Installed : Environment → Prop)
    (Restored : Environment → Environment → Prop)
    (Hrun : (AddInductive.run nparams res.types res.aux2nested.size
      { env, allowPrimitive, lparams, fuel,
        safety := if isUnsafe then .unsafe else .safe }).WF Installed)
    (Hrestore : ∀ loweredEnv, Installed loweredEnv →
      res.aux2nested.size ≠ 0 →
      (Environment.restoreNestedAfterInstall env loweredEnv lparams types
        (if isUnsafe then .unsafe else .safe) allowPrimitive fuel res).WF
          (Restored loweredEnv)) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      allowPrimitive fuel res).WF
        (AddInductiveAfterLoweringResult res Installed Restored) := by
  unfold Environment.addInductiveAfterLowering
  exact Hrun.bind fun loweredEnv Hinstalled => by
    by_cases hzero : res.aux2nested.size = 0
    · simp only [hzero, ↓reduceIte]
      exact Except.WF.pure (.ordinary hzero Hinstalled)
    · simp only [hzero, ↓reduceIte]
      exact (Hrestore loweredEnv Hinstalled hzero).mono fun outEnv Hrestored =>
        .nested hzero Hinstalled Hrestored

/-- Successful nested restoration retains both the exact declaration-fold
trace and the independently specified auxiliary-witness validation. -/
structure RestoredAfterInstallResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) (Validated : Environment → Prop)
    (outEnv : Environment) : Prop where
  restoration : Nonempty (RestoredNestedDeclarationsResult res loweredEnv
    sourceEnv recNameMap allIndNames types auxRecNames ((), outEnv))
  validated : Validated outEnv

/-- Compose the verified declaration-restoration folds with the production
auxiliary validation pass. -/
theorem Environment.restoreNestedAfterInstall.WF
    (env loweredEnv : Environment) (lparams : List Name)
    (types : List InductiveType) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type res.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type res.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs res.nparams)
    (Haux : ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type res.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs res.nparams)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv types).2 (types.map (·.name))
        types (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety
      allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 Validated outEnv := by
  let recNames := (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
  let recNameMap := (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
  let allIndNames := types.map (·.name)
  have Hdeclarations := restoreNestedDeclarations_refines res loweredEnv env
    recNameMap allIndNames allowPrimitive types recNames Htypes (by
      simpa [recNames] using Haux)
  have HrestoredEnv :
      ((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
        recNameMap allIndNames allowPrimitive types recNames env).WF
          fun restoredEnv => Nonempty (RestoredNestedDeclarationsResult res
            loweredEnv env recNameMap allIndNames types recNames
              ((), restoredEnv)) := by
    exact Hdeclarations.map fun restored Hrestored => by
      rcases restored with ⟨unit, restoredEnv⟩
      rcases unit with ⟨⟩
      exact Hrestored
  have Houtput :
      (((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
          recNameMap allIndNames allowPrimitive types recNames env).bind
        fun restoredEnv =>
          (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
            res).bind fun _ => Except.pure restoredEnv).WF
        (RestoredAfterInstallResult res env loweredEnv recNameMap allIndNames
          types recNames Validated) :=
    HrestoredEnv.bind fun restoredEnv Hrestored => by
      exact (Hvalidate restoredEnv (by
        simpa [recNames, recNameMap, allIndNames] using Hrestored)).bind
          fun _ Hvalidated => Except.WF.pure (show
            RestoredAfterInstallResult res env loweredEnv recNameMap
              allIndNames types recNames Validated restoredEnv from
                ⟨Hrestored, Hvalidated⟩)
  simpa [Environment.restoreNestedAfterInstall, recNames, recNameMap,
    allIndNames, StateT.run, bind, Except.bind, pure] using Houtput

/-- Complete outcome specification for an application already recognized as
nested: either an existing cache entry is reused without changing state, or a
certified batch for the entire mutual block is generated. -/
inductive RecognizedNestedReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | cached (auxName : Name) :
      CachedNestedAux state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName →
      RecognizedNestedReplacement env lctx params As targetName levels args
        value state
        (some (mkAppRange (mkAppN (.const auxName state.lvls) As)
          value.numParams args.size args), state)
  | generated :
      MutualInductiveClosure env targetName value →
      GeneratedAuxiliaryBatch env lctx params As targetName levels
        value.numParams args none value.all state out →
      RecognizedNestedReplacement env lctx params As targetName levels args
        value state out

theorem replaceRecognizedNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State)
    (hargs : value.numParams ≤ args.size)
    (hsize : As.size = params.size)
    (hclosure : MutualInductiveClosure env targetName value) :
    (Lean4Lean.ElimNestedInductive.replaceRecognizedNested lctx params As
      (.const targetName levels) args value env state).WF fun out =>
        RecognizedNestedReplacement env lctx params As targetName levels args
          value state out := by
  unfold Lean4Lean.ElimNestedInductive.replaceRecognizedNested
  simp only [hargs, ↓reduceIte]
  refine nestedBind.WF
    (replaceNestedParams_state_refines params
      (mkAppRange (.const targetName levels) 0 value.numParams args) As
      env state hsize) ?_
  intro nested nextState hnested
  cases hnested
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  cases hcache : Lean4Lean.ElimNestedInductive.findCachedAux?
      state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) with
  | some auxName =>
    simp only [pure, ReaderT.pure, StateT.pure]
    exact Except.WF.pure (RecognizedNestedReplacement.cached auxName
      (findCachedAux?_refines state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName hcache))
  | none =>
    exact (generateAuxiliaries_refines env lctx params As targetName levels
      value.numParams args value state hsize hclosure.members
      hclosure.target).mono fun _ Hbatch =>
        RecognizedNestedReplacement.generated hclosure Hbatch

/-- Complete node-level result of nested replacement.  A non-candidate is
left untouched; every accepted candidate carries both the independent
recognition evidence and the cache-or-generation certificate. -/
inductive NestedReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | unrecognized : NoNestedAppCandidate env state e →
      NestedReplacement env lctx params As e state (none, state)
  | recognized :
      NestedAppCandidate env state e value →
      e.getAppFn = .const targetName levels →
      RecognizedNestedReplacement env lctx params As targetName levels
        e.getAppArgs value state out →
      NestedReplacement env lctx params As e state out

theorem replaceIfNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested lctx params As e env state).WF
      fun out => NestedReplacement env lctx params As e state out := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧
      (∀ value, recognized.1 = some value →
        NestedAppCandidate env state e value) ∧
      (recognized.1 = none → NoNestedAppCandidate env state e)) ?_ ?_
  · intro recognized hrecognized
    refine ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized, ?_⟩
    intro hnone info Hcandidate
    have hcomplete := Hcandidate.recognized recognized hrecognized
    change recognized.1 = some info at hcomplete
    rw [hnone] at hcomplete
    cases hcomplete
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate, hnone⟩
    simp only at hstate hcandidate hnone ⊢
    subst nextState
    cases recognized with
    | none =>
      exact Except.WF.pure (.unrecognized (hnone rfl))
    | some value =>
      have Hcandidate := hcandidate value rfl
      rcases Hcandidate.headFound with
        ⟨targetName, levels, hhead, hlookup⟩
      simp only
      rw [Expr.withApp_eq, hhead]
      exact (replaceRecognizedNested_refines env lctx params As targetName
        levels e.getAppArgs value state Hcandidate.parameters.arity hsize
        (hclosures targetName value hlookup)).mono fun _ Hresult =>
          .recognized Hcandidate hhead Hresult

theorem RecognizedNestedReplacement.resultSome
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : out.1.isSome = true := by
  cases H with
  | cached => simp
  | generated _ Hbatch => exact Hbatch.resultSome

theorem NestedReplacement.outcome
    (H : NestedReplacement env lctx params As e state out) :
    out = (none, state) ∨ ∃ output nextState, out = (some output, nextState) := by
  cases H with
  | unrecognized => exact Or.inl rfl
  | recognized Hcandidate hhead Hresult =>
    right
    have hsome := Hresult.resultSome
    cases h : out.1 with
    | none => simp [h] at hsome
    | some output => exact ⟨output, out.2, by cases out; simp_all⟩

theorem NestedReplacement.noCandidate
    (H : NestedReplacement env lctx params As e state (none, state)) :
    NoNestedAppCandidate env state e := by
  cases H with
  | unrecognized Hnone => exact Hnone
  | recognized Hcandidate hhead Hresult =>
    have hsome := Hresult.resultSome
    simp at hsome

/-- Stateful, top-down specification of `Expr.replaceM` for nested lowering.
A successful node replacement stops descent; otherwise children are processed
left-to-right with the exact intermediate states and update combinators used by
Lean's expression traversal. -/
inductive NestedExprReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacement env lctx params As input state
      (some output, nextState) →
      NestedExprReplacement env lctx params As input state (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprReplacement env lctx params As (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprReplacement env lctx params As (.fvar fvarId) state
        (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprReplacement env lctx params As (.mvar mvarId) state
        (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprReplacement env lctx params As (.sort level) state (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) →
      NestedExprReplacement env lctx params As (.const name levels) state
        (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprReplacement env lctx params As (.lit literal) state
        (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprReplacement env lctx params As fn state (fn', fnState) →
      NestedExprReplacement env lctx params As arg fnState (arg', outState) →
      NestedExprReplacement env lctx params As (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) →
      NestedExprReplacement env lctx params As dom state (dom', domState) →
      NestedExprReplacement env lctx params As body domState (body', outState) →
      NestedExprReplacement env lctx params As (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprReplacement env lctx params As dom state (dom', domState) →
      NestedExprReplacement env lctx params As body domState (body', outState) →
      NestedExprReplacement env lctx params As (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprReplacement env lctx params As type state (type', typeState) →
      NestedExprReplacement env lctx params As value typeState (value', valueState) →
      NestedExprReplacement env lctx params As body valueState (body', outState) →
      NestedExprReplacement env lctx params As (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) →
      NestedExprReplacement env lctx params As body state (body', outState) →
      NestedExprReplacement env lctx params As (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) →
      NestedExprReplacement env lctx params As body state (body', outState) →
      NestedExprReplacement env lctx params As (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering only appends to `newTypes` while traversing expressions. -/
def NestedNewTypesLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.newTypes.toList = source.newTypes.toList ++ suffix

/-- Nested-expression traversal also grows the `(nested expression, fresh
family name)` cache append-only. This is the operational source of the final
`aux2nested` map used by restoration. -/
def NestedAuxLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.nestedAux.toList = source.nestedAux.toList ++ suffix

theorem NestedAuxLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedAuxLE state state := ⟨[], by simp⟩

theorem NestedAuxLE.trans
    (H₁ : NestedAuxLE first middle) (H₂ : NestedAuxLE middle last) :
    NestedAuxLE first last := by
  rcases H₁ with ⟨xs, hxs⟩
  rcases H₂ with ⟨ys, hys⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc]⟩

theorem NestedAuxLE.mem
    (H : NestedAuxLE source target)
    (hentry : entry ∈ source.nestedAux) : entry ∈ target.nestedAux := by
  rcases H with ⟨suffix, hsuffix⟩
  have hsource : entry ∈ source.nestedAux.toList := by simpa using hentry
  have htarget : entry ∈ target.nestedAux.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

private theorem nestedAuxFold_find_of_not_mem
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnot : name ∉ entries.map Prod.snd) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = map[name]? := by
  induction entries generalizing map with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.foldl_cons]
    rw [ih _ hnot.2]
    rw [Std.TreeMap.getElem?_insert]
    split
    next heq =>
      have hname : entry.2 = name :=
        Std.LawfulEqCmp.compare_eq_iff_eq.mp heq
      exact False.elim (hnot.1 hname.symm)
    next => rfl

def NestedAuxMapFVarsIn (P : FVarId → Prop)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr),
    map[name]? = some nested → nested.FVarsIn P

/-- Every key in a restoration map belongs to the private namespace used by
the lowering-generated auxiliary families. -/
def NestedAuxMapNamesReserved
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    (`_nested).isPrefixOf name = true

def NestedAuxMapNamesFresh (env : Environment)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    env.contains name = false

theorem NestedAuxMapNamesReserved.insert
    (Hmap : NestedAuxMapNamesReserved map)
    (Hname : (`_nested).isPrefixOf name = true) :
    NestedAuxMapNamesReserved (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapNamesFresh.insert
    (Hmap : NestedAuxMapNamesFresh env map)
    (Hname : env.contains name = false) :
    NestedAuxMapNamesFresh env (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapFVarsIn.insert
    (Hmap : NestedAuxMapFVarsIn P map) (Hnested : nested.FVarsIn P) :
    NestedAuxMapFVarsIn P (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind
    exact Hnested
  · exact Hmap query value hfind

theorem nestedAuxFold_fvarsIn
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, entry.1.FVarsIn P)
    (Hmap : NestedAuxMapFVarsIn P map) :
    NestedAuxMapFVarsIn P
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesReserved
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries,
      (`_nested).isPrefixOf entry.2 = true)
    (Hmap : NestedAuxMapNamesReserved map) :
    NestedAuxMapNamesReserved
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesFresh
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, env.contains entry.2 = false)
    (Hmap : NestedAuxMapNamesFresh env map) :
    NestedAuxMapNamesFresh env
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

/-- Folding a cache with unique generated names retrieves the nested
expression paired with every cache entry. -/
theorem nestedAuxFold_find
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnodup : (entries.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ entries) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = some nested := by
  induction entries generalizing map with
  | nil => simp at hentry
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hentry
    simp only [List.foldl_cons]
    rcases hentry with hhead | htail
    · cases hhead
      rw [nestedAuxFold_find_of_not_mem entries _ hnodup.1]
      simp
    · have htailNodup : (entries.map Prod.snd).Nodup := hnodup.2
      have htailFind := ih (map.insert entry.2 entry.1) htailNodup htail
      simpa using htailFind

/-- A final restoration map faithfully represents every entry retained in a
nested-lowering state. This isolates the map property needed by local
lowering/restoration proofs from the particular fold that builds the map. -/
def NestedAuxMapModels (result : Lean4Lean.ElimNestedInductive.Result)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux →
    result.aux2nested.find? name = some nested

theorem NestedNewTypesLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedNewTypesLE state state := ⟨[], by simp⟩

theorem NestedNewTypesLE.trans
    (H₁ : NestedNewTypesLE first middle)
    (H₂ : NestedNewTypesLE middle last) : NestedNewTypesLE first last := by
  rcases H₁ with ⟨xs, hxs⟩
  rcases H₂ with ⟨ys, hys⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc]⟩

theorem NestedNewTypesLE.mem
    (H : NestedNewTypesLE source target)
    (hentry : entry ∈ source.newTypes) : entry ∈ target.newTypes := by
  rcases H with ⟨suffix, hsuffix⟩
  have hsource : entry ∈ source.newTypes.toList := by simpa using hentry
  have htarget : entry ∈ target.newTypes.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

theorem NestedNewTypesLE.getElem
    (H : NestedNewTypesLE source target) (hi : i < source.newTypes.size) :
    ∃ htarget : i < target.newTypes.size,
      target.newTypes[i] = source.newTypes[i] := by
  rcases H with ⟨suffix, hsuffix⟩
  have htarget : i < target.newTypes.size := by
    have hsizes := congrArg List.length hsuffix
    have hlen : target.newTypes.size =
        source.newTypes.size + suffix.length := by simpa using hsizes
    rw [hlen]
    omega
  refine ⟨htarget, ?_⟩
  have hlist : target.newTypes.toList[i] = source.newTypes.toList[i] := by
    simpa [hsuffix, List.getElem_append, hi]
  simpa using hlist

theorem GeneratedAuxiliary.newTypesLE
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedNewTypesLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[data.type], by simp⟩

theorem GeneratedAuxiliary.nestedAuxLE
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedAuxLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[(data.nested, auxName)], by simp⟩

theorem GeneratedAuxiliary.namesWF
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rcases Hfresh.index with ⟨index, hstart, hname, hnext⟩
  rw [hstate]
  have hnot : auxName ∉ state.nestedAux.toList.map Prod.snd := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨nested, oldName⟩, hold, heq⟩
    change oldName = auxName at heq
    rcases Hstate.indexed nested oldName (by simpa using hold) with
      ⟨oldBase, oldIndex, holdName, holdIndex⟩
    have hsuffix : oldIndex = index := Hindex oldBase
      (`_nested ++ sourceName) oldIndex index (by
        rw [← holdName, ← hname]
        exact heq)
    omega
  constructor
  · simp only [Array.toList_push, List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨Hstate.nodup, by simp, ?_⟩
    intro oldName hold newName hnew
    simp only [List.mem_singleton] at hnew
    subst newName
    intro heq
    subst oldName
    exact hnot hold
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · rcases Hstate.indexed nested name hold with
        ⟨base, oldIndex, holdName, holdIndex⟩
      refine ⟨base, oldIndex, holdName, ?_⟩
      change oldIndex < nextIdx
      rw [hnext]
      omega
    · cases hnew
      refine ⟨`_nested ++ sourceName, index, hname, ?_⟩
      change index < nextIdx
      rw [hnext]
      omega
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · exact Hstate.reserved nested name hold
    · cases hnew
      rw [hname]
      exact nested_isPrefix_appendIndexAfter sourceName index

theorem GeneratedAuxiliary.namesFresh
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rw [hstate]
  intro nested name hentry
  simp only [Array.mem_push] at hentry
  rcases hentry with hold | hnew
  · exact Hstate nested name hold
  · cases hnew
    exact Hfresh.fresh

theorem GeneratedAuxiliaryBatch.newTypesLE
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.newTypesLE.trans ih

theorem GeneratedAuxiliaryBatch.nestedAuxLE
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.nestedAuxLE.trans ih

theorem GeneratedAuxiliaryBatch.namesWF
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesWF Hindex Hstate)

theorem GeneratedAuxiliaryBatch.namesFresh
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesFresh Hstate)

/-- Every source family traversed by the mutual-generation loop has a
concrete auxiliary construction whose paired cache entry and lowered family
both survive in the batch's final state. -/
theorem GeneratedAuxiliaryBatch.generatedFor
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsource : sourceName ∈ sourceNames) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name) (nextIdx : Nat)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      FreshNestedName env (`_nested ++ sourceName) stepState.nextIdx
        auxName nextIdx ∧
      BuiltAuxiliary env lctx params As levels nparams args sourceName auxName
        sourceInfo data ∧
      (data.nested, auxName) ∈ out.2.nestedAux ∧
      data.type ∈ out.2.newTypes := by
  induction H with
  | nil => simp at hsource
  | cons Hstep Htail ih =>
    simp only [List.mem_cons] at hsource
    rcases hsource with rfl | htail
    · rcases Hstep.generated with
        ⟨auxName, nextIdx, data, Hfresh, Hbuilt, _, hstep⟩
      refine ⟨_, _, auxName, nextIdx, data, Hfresh, Hbuilt, ?_, ?_⟩
      · apply Htail.nestedAuxLE.mem
        rw [hstep]
        simp
      · apply Htail.newTypesLE.mem
        rw [hstep]
        simp
    · exact ih htail

/-- If the target family does not occur in the remaining mutual-family
suffix, that suffix cannot replace the accumulated result. -/
theorem GeneratedAuxiliaryBatch.result_eq_of_target_not_mem
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnot : targetName ∉ sourceNames) : out.1 = result := by
  induction H with
  | nil => rfl
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.mem_cons, not_or] at hnot
    rcases Hstep.generated with
      ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
    have hne : sourceName ≠ targetName := Ne.symm hnot.1
    have hstep : step.1 = none := by
      rw [hresult]
      simp [hne]
    have htail := ih hnot.2
    simpa [hstep] using htail

/-- With unique mutual-family names, the batch result is exactly the
auxiliary application generated at the unique target-family step. The same
fresh name remains paired with its source expression in the final cache. -/
theorem GeneratedAuxiliaryBatch.targetResult
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnodup : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name) (nextIdx : Nat)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      FreshNestedName env (`_nested ++ targetName) stepState.nextIdx
        auxName nextIdx ∧
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      (data.nested, auxName) ∈ out.2.nestedAux ∧
      data.type ∈ out.2.newTypes := by
  induction H with
  | nil => simp at htarget
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.nodup_cons] at hnodup
    simp only [List.mem_cons] at htarget
    rcases htarget with hhead | htail
    · subst sourceName
      rcases Hstep.generated with
        ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstepState⟩
      have hstepResult : step.1 = some (mkAppRange
          (mkAppN (.const auxName state.lvls) As) nparams args.size args) := by
        simpa using hresult
      have hfinal := Htail.result_eq_of_target_not_mem hnodup.1
      refine ⟨state, _, auxName, nextIdx, data, Hfresh, Hbuilt, ?_, ?_, ?_⟩
      · simpa [hstepResult] using hfinal
      · apply Htail.nestedAuxLE.mem
        rw [hstepState]
        simp
      · apply Htail.newTypesLE.mem
        rw [hstepState]
        simp
    · exact ih hnodup.2 htail

/-- The exact target result is already reversible by the map obtained from
folding the batch's final cache, provided the separately tracked generated
names are unique. -/
theorem GeneratedAuxiliaryBatch.targetResultLookup
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsourceNames : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames)
    (hauxNames : (out.2.nestedAux.toList.map Prod.snd).Nodup) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      (out.2.nestedAux.toList.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        {})[auxName]? = some data.nested := by
  rcases H.targetResult hsourceNames htarget with
    ⟨stepState, sourceInfo, auxName, _nextIdx, data, _Hfresh, Hbuilt,
      hresult, hentry, _htype⟩
  exact ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult,
    nestedAuxFold_find out.2.nestedAux.toList {} hauxNames
      (by simpa using hentry)⟩

/-- Global map-model evidence turns the unique target step into the exact
`aux2nested` lookup used by restoration, even after later lowering has
appended more cache entries. -/
theorem GeneratedAuxiliaryBatch.targetResultMapped
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsourceNames : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      finalResult.aux2nested.find? auxName = some data.nested := by
  rcases H.targetResult hsourceNames htarget with
    ⟨stepState, sourceInfo, auxName, _nextIdx, data, _Hfresh, Hbuilt,
      hresult, hentry, _htype⟩
  exact ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult,
    Hmap data.nested auxName (Hlater.mem hentry)⟩

/-- Both cache reuse and fresh mutual-family generation expose the same
restoration-facing fact: the returned auxiliary application is keyed in the
final map by the normalized source-family application it replaced. -/
theorem RecognizedNestedReplacement.finalMapping
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ auxName auxLevels nested lowered,
      out.1 = some lowered ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams args.size args ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract
          As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested := by
  cases H with
  | cached auxName Hcached =>
    rcases Hcached.entry with
      ⟨⟨found, foundName⟩, hentry, heq, hname⟩
    change foundName = auxName at hname
    rw [hname] at hentry
    refine ⟨auxName, state.lvls, found, _, rfl, rfl, heq, ?_⟩
    exact Hmap _ auxName (Hlater.mem hentry)
  | generated Hclosure Hbatch =>
    rcases Hbatch.targetResultMapped Hclosure.names Hclosure.target Hlater Hmap
      with ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult, hlookup⟩
    refine ⟨auxName, stepState.lvls, data.nested, _, hresult, rfl, ?_, hlookup⟩
    rw [Hbuilt.nested]
    simp

def NestedReplacementHasFinalMapping
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result) : Prop :=
    ∃ value targetName levels auxName auxLevels nested,
      NestedAppCandidate env state input value ∧
      input.getAppFn = .const targetName levels ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams input.getAppArgs.size input.getAppArgs ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested

/-- A mapped lowering hit introduces only its selected parameter variables;
all trailing arguments are inherited from the source application. -/
theorem NestedReplacementHasFinalMapping.outputFVarsIn
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    lowered.FVarIdsIn (· ∈ Hselection.fvars) := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hnested, hlookup⟩
  have HAs : ∀ arg ∈ As.toList,
      arg.FVarIdsIn (· ∈ Hselection.fvars) := by
    intro arg harg
    rw [Hselection.expressions] at harg
    rcases List.mem_map.mp harg with ⟨fv, hfv, rfl⟩
    simpa [Expr.FVarIdsIn] using hfv
  rw [hlowered]
  rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
  apply Expr.FVarIdsIn.mkAppList.mpr
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    exact Expr.FVarIdsIn.mkAppList.mpr
      ⟨by simp [Expr.FVarIdsIn], HAs⟩
  · intro arg harg
    apply Hinput.getAppArgsList
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop harg

/-- A mapped lowering leaf after reopening its cached source application with
the parameter array chosen by restoration. -/
def NestedReplacementReopens
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) : Prop :=
  ∃ value targetName levels auxName auxLevels nested,
    NestedAppCandidate env state input value ∧
    input.getAppFn = .const targetName levels ∧
    lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
      value.numParams input.getAppArgs.size input.getAppArgs ∧
    finalResult.aux2nested.find? auxName = some nested ∧
    (((nested.abstract finalResult.params).instantiateRev restoreAs) ==
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As).instantiateRev restoreAs) = true

/-- A reopened lowering hit is interpreted by the concrete family branch of
`restoreNestedNode`.  The auxiliary parameter prefix is discarded and the
reopened source-family prefix is reattached to the identically renamed
non-parameter arguments, yielding the renamed original application up to
Lean expression equivalence. -/
theorem NestedReplacementReopens.restoreNode
    (H : NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hresultNParams : finalResult.nparams = As.size) :
    ∃ restored,
      finalResult.restoreNestedNode restoreEnv restoreAs {}
          (Expr.reopenParams lowered As restoreAs) = some restored ∧
      (restored == Expr.reopenParams input As restoreAs) = true := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hlookup, hreopens⟩
  let R : Expr → Expr := fun e => Expr.reopenParams e As restoreAs
  let trailing : List Expr :=
    input.getAppArgsList.drop value.numParams |>.map R
  let paramPrefix : List Expr := As.toList.map R
  have hloweredReopened : R lowered =
      Expr.mkAppList (.const auxName auxLevels) (paramPrefix ++ trailing) := by
    rw [hlowered]
    rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    rw [Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    change Expr.reopenParams _ As restoreAs = _
    rw [Expr.reopenParams_mkAppList Hselection.fvars
      Hselection.expressions]
    rw [Expr.reopenParams_const Hselection.fvars Hselection.expressions]
    simp [R, paramPrefix, trailing, Expr.getAppArgs_toList]
  have hfn : (R lowered).getAppFn = .const auxName auxLevels := by
    rw [hloweredReopened]
    exact Expr.getAppFn_mkAppList_const auxName auxLevels _
  have hargsList : (R lowered).getAppArgsList = paramPrefix ++ trailing := by
    rw [hloweredReopened]
    exact Expr.getAppArgsList_mkAppList_const auxName auxLevels _
  have hargs : (R lowered).getAppArgs = (paramPrefix ++ trailing).toArray := by
    rw [Expr.getAppArgs_eq, hargsList]
  have hprefixLength : paramPrefix.length = finalResult.nparams := by
    simp [paramPrefix, hresultNParams]
  have harity : finalResult.nparams ≤ (R lowered).getAppArgs.size := by
    rw [hargs]
    simp [hprefixLength]
  have hnode := restoreNestedNode_family_general finalResult restoreEnv
    restoreAs {}
    (R lowered) nested auxName auxLevels hfn (by rfl) hlookup harity
  have hrestored :
      mkAppRange ((nested.abstract finalResult.params).instantiateRev restoreAs)
          finalResult.nparams (R lowered).getAppArgs.size
          (R lowered).getAppArgs =
        Expr.mkAppList
          ((nested.abstract finalResult.params).instantiateRev restoreAs)
          trailing := by
    rw [Expr.mkAppRange_to_end _ _ _ harity, hargs]
    simp [hprefixLength]
  refine ⟨Expr.mkAppList
      ((nested.abstract finalResult.params).instantiateRev restoreAs)
      trailing, ?_, ?_⟩
  · rw [hrestored] at hnode
    simpa only [R] using hnode
  · have hprefixSource :
        R (mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs) =
          Expr.mkAppList (.const targetName levels)
            (input.getAppArgsList.take value.numParams |>.map R) := by
      rw [Expr.mkAppRange_from_zero _ _ _ Hcandidate.parameters.arity]
      change Expr.reopenParams _ As restoreAs = _
      rw [Expr.reopenParams_mkAppList Hselection.fvars
        Hselection.expressions]
      rw [Expr.reopenParams_const Hselection.fvars Hselection.expressions]
      simp [R, Expr.getAppArgs_toList]
    change (((nested.abstract finalResult.params).instantiateRev restoreAs) ==
      R (mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs)) = true at hreopens
    have happended := Expr.mkAppList_eqv hreopens trailing
    rw [hprefixSource] at happended
    have hinput : R input =
        Expr.mkAppList (.const targetName levels)
          (input.getAppArgsList.map R) :=
      Expr.reopenParams_of_getAppFn_const Hselection.fvars
        Hselection.expressions hhead
    rw [← Expr.mkAppList_append] at happended
    simp only [trailing] at happended
    rw [List.map_take, List.map_drop, List.take_append_drop] at happended
    simpa [hinput, trailing, R] using happended

/-- The final-map witness retained at a lowering hit is a left inverse for
the abstraction/reopening part of `restoreNestedNode`.  The only local
scoping premise is that abstracting the constructor-opening parameters has
removed all free variables; constructor lowering establishes that fact from
its closed source type. -/
theorem NestedReplacementHasFinalMapping.reopens
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (hclosed : ∀ value targetName levels,
      NestedAppCandidate env state input value →
      input.getAppFn = .const targetName levels →
      FVarsIn (fun _ => False)
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As)) :
    NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hnested, hlookup⟩
  let base := (mkAppRange (.const targetName levels) 0 value.numParams
    input.getAppArgs).abstract As
  have habstract :
      (nested.abstract params) ==
        ((base.instantiateRev params).abstract params) := by
    rw [hparams, Expr.abstract_eq, Expr.abstract_eq]
    apply Expr.abstractList_eqv
    simpa [base, hparams] using hnested
  have heqv :
      ((nested.abstract finalResult.params).instantiateRev restoreAs) ==
        (((base.instantiateRev params).abstract params).instantiateRev
          restoreAs) := by
    rw [hresultParams, Expr.instantiateRev_eq, Expr.instantiate_eq,
      Expr.instantiateRev_eq, Expr.instantiate_eq]
    exact Expr.instantiateList_eqv habstract
  refine ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
    hhead, hlowered, hlookup, ?_⟩
  have hfree : FVarsIn (fun fv => fv ∉ fvars) base :=
    (hclosed value targetName levels Hcandidate hhead).mono
      fun fv hfalse => False.elim hfalse
  have hcancel := hfree.reabstract_instantiateRev_fvarArray
    params restoreAs fvars hparams hnodup
  rw [hcancel] at heqv
  exact heqv

/-- A recognized nested application's source-family prefix becomes closed
once all constructor-opening free variables are abstracted. -/
theorem NestedAppCandidate.abstractedPrefixClosed
    (H : NestedAppCandidate env state input value)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input)
    (hhead : input.getAppFn = .const targetName levels) :
    FVarsIn (fun _ => False)
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As) := by
  apply FVarsIn.abstract_fvarArray_of Hselection.fvars As
    Hselection.expressions
  apply FVarsIn.mkAppRange_zero H.parameters.arity
  · have Hfn := Hinput.getAppFn
    rw [hhead] at Hfn
    exact Hfn
  · intro arg harg
    have harg' : arg ∈ input.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    exact (Hinput.getAppArgsList harg').mono fun fv hfv => Or.inl hfv

/-- Constructor-scoped specialization of `reopens`; the closedness premise
is derived from the source body's free-variable invariant. -/
theorem NestedReplacementHasFinalMapping.reopensOfFVars
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs := by
  apply H.reopens hresultParams fvars hparams hnodup
  intro value targetName levels Hcandidate hhead
  exact Hcandidate.abstractedPrefixClosed Hselection Hinput hhead

/-- Successful node replacement retains both the independent recognition
certificate and the final restoration-map entry for the auxiliary family it
returns. This is the leaf case needed by the structural expression inverse. -/
theorem NestedReplacement.finalMapping
    (H : NestedReplacement env lctx params As input state
      (some lowered, nextState))
    (Hlater : NestedAuxLE nextState finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    NestedReplacementHasFinalMapping env lctx params As input state lowered
      finalResult := by
  cases H with
  | recognized Hcandidate hhead Hrecognized =>
    rcases Hrecognized.finalMapping Hlater Hmap with
      ⟨auxName, auxLevels, nested, replacement, hresult, hreplacement,
        hnested, hlookup⟩
    cases hresult
    exact ⟨_, _, _, auxName, auxLevels, nested,
      Hcandidate, hhead, hreplacement, hnested, hlookup⟩

/-- Structural expression-lowering relation whose successful leaves are
already connected to the final restoration map. Unlike the operational trace,
this relation forgets monadic control flow and retains exactly the semantic
information needed to interpret the lowered expression. -/
inductive NestedExprMapping
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacementHasFinalMapping env lctx params As input state
      output finalResult →
      NestedExprMapping env lctx params As finalResult input state
        (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.bvar i) state
      (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprMapping env lctx params As finalResult
      (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprMapping env lctx params As finalResult
      (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.sort level) state
      (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) → NestedExprMapping env lctx params As finalResult
      (.const name levels) state (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.lit literal) state
      (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprMapping env lctx params As finalResult fn state
      (fn', fnState) →
      NestedExprMapping env lctx params As finalResult arg fnState
        (arg', outState) →
      NestedExprMapping env lctx params As finalResult (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → NestedExprMapping env lctx params As finalResult dom state
      (dom', domState) →
      NestedExprMapping env lctx params As finalResult body domState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult (.lam name dom body bi)
        state (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprMapping env lctx params As finalResult dom state
      (dom', domState) →
      NestedExprMapping env lctx params As finalResult body domState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprMapping env lctx params As finalResult type state
      (type', typeState) →
      NestedExprMapping env lctx params As finalResult value typeState
        (value', valueState) →
      NestedExprMapping env lctx params As finalResult body valueState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) → NestedExprMapping env lctx params As finalResult body state
      (body', outState) →
      NestedExprMapping env lctx params As finalResult (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) → NestedExprMapping env lctx params As finalResult body state
      (body', outState) →
      NestedExprMapping env lctx params As finalResult (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering preserves free-variable-ID scoping. Successful hits use
`outputFVarsIn`; structural misses inherit the property componentwise. -/
theorem NestedExprMapping.outputFVarIdsIn
    (H : NestedExprMapping env lctx params As finalResult input state out)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    out.1.FVarIdsIn (· ∈ Hselection.fvars) := by
  induction H with
  | hit Hnode => exact Hnode.outputFVarsIn Hselection Hinput
  | bvar | fvar | mvar | sort | const | lit => exact Hinput
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateApp!, Expr.FVarIdsIn] using
      And.intro (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLambdaE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateForallE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLet!, Expr.FVarIdsIn] using
      And.intro (ihType Hinput.1)
        (And.intro (ihValue Hinput.2.1) (ihBody Hinput.2.2))
  | mdata Hnode Hbody ihBody =>
    simpa [Expr.updateMData!, Expr.FVarIdsIn] using ihBody Hinput
  | proj Hnode Hbody ihBody =>
    simpa [Expr.updateProj!, Expr.FVarIdsIn] using ihBody Hinput

/-- Structural lowering map with every successful leaf upgraded to its
parameter-reopening certificate. -/
inductive NestedExprReopening
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacementReopens env lctx params As input state output
      finalResult restoreAs →
      NestedExprReopening env lctx params As finalResult restoreAs input state
        (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.sort level) state (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs
      (.const name levels) state (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.lit literal) state (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs fn state
      (fn', fnState) →
      NestedExprReopening env lctx params As finalResult restoreAs arg fnState
        (arg', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs dom state
      (dom', domState) →
      NestedExprReopening env lctx params As finalResult restoreAs body domState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs dom
      state (dom', domState) →
      NestedExprReopening env lctx params As finalResult restoreAs body domState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs type state
      (type', typeState) →
      NestedExprReopening env lctx params As finalResult restoreAs value typeState
        (value', valueState) →
      NestedExprReopening env lctx params As finalResult restoreAs body valueState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs body state
      (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs body state
      (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Lift a complete expression mapping to leafwise reopening.  Source
free-variable scoping is split structurally in exactly the same way as the
lowering traversal. -/
theorem NestedExprMapping.reopens
    (H : NestedExprMapping env lctx params As finalResult input state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NestedExprReopening env lctx params As finalResult restoreAs input state
      out := by
  induction H with
  | hit Hnode =>
    exact .hit (Hnode.reopensOfFVars hresultParams fvars hparams hnodup
      Hselection Hinput)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .app Hnode (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .lam Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .forallE Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .letE Hnode (ihType Hinput.1) (ihValue Hinput.2.1)
      (ihBody Hinput.2.2)
  | mdata Hnode Hbody ihBody =>
    exact .mdata Hnode (ihBody Hinput)
  | proj Hnode Hbody ihBody =>
    exact .proj Hnode (ihBody Hinput)

/-- A structural lowering trace cannot introduce a constant application head
unless the root itself was recognized. In the application case, maximality
rules out a recognized function prefix whenever the parent has a certified
miss. -/
theorem NestedExprReopening.constHead_of_noCandidate
    (H : NestedExprReopening env lctx params As finalResult restoreAs input
      state out)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hhead : out.1.getAppFn = .const name levels) :
    input.getAppFn = .const name levels := by
  induction H with
  | hit Hnode =>
    rcases Hnode with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hhead, hlowered, hlookup, hreopens⟩
    exact False.elim (Hmiss value Hcandidate)
  | bvar | fvar | mvar | sort | const | lit => exact Hhead
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have HfnMiss : NoNestedAppCandidate env state fn := by
      intro info Hcandidate
      exact Hmiss info (Hcandidate.app arg)
    apply ihFn HfnMiss
    simpa [Expr.getAppFn] using Hhead
  | lam => simp [Expr.getAppFn] at Hhead
  | forallE => simp [Expr.getAppFn] at Hhead
  | letE => simp [Expr.getAppFn] at Hhead
  | mdata => simp [Expr.getAppFn] at Hhead
  | proj => simp [Expr.getAppFn] at Hhead

/-- The constant-head reflection theorem remains true after the constructor
parameters have been renamed at an arbitrary binder depth. -/
theorem NestedExprReopening.reopenedConstHead_of_noCandidate
    (H : NestedExprReopening env lctx params As finalResult restoreAs input
      state out)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hhead : (Expr.reopenFVarsAt out.1 fvars restoreFvars k).getAppFn =
      .const name levels) :
    input.getAppFn = .const name levels := by
  apply H.constHead_of_noCandidate Hmiss
  exact Expr.getAppFn_reopenFVarsAt_eq_const hnd hsize out.1 k Hhead

/-- At a structural lowering node, restoration must miss the node itself.
The proof uses recognition maximality for the lowered head and source-map
disjointness for the corresponding original constant. -/
theorem NestedExprReopening.restoreNode_none
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input) (k : Nat) :
    finalResult.restoreNestedNode restoreEnv targetAs {}
      (Expr.reopenFVarsAt out.1 fvars restoreFvars k) = none := by
  generalize ht : Expr.reopenFVarsAt out.1 fvars restoreFvars k = t
  cases t with
  | const name levels =>
    have hsourceHead : input.getAppFn = .const name levels :=
      H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
        rw [ht]
        rfl)
    have hdisjoint := Hsource.getAppFn hsourceHead
    have hrec : ({} : NameMap Name).find? name = none := rfl
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn, hrec, hdisjoint.1, hdisjoint.2]
  | app fn arg =>
    cases hhead : (Expr.app fn arg).getAppFn with
    | const name levels =>
      simp only [Expr.getAppFn] at hhead
      have hsourceHead : input.getAppFn = .const name levels :=
        H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
          rw [ht]
          exact hhead)
      have hdisjoint := Hsource.getAppFn hsourceHead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead, hdisjoint.1, hdisjoint.2]
    | bvar | fvar | mvar | sort | app | lam | forallE | letE | lit | mdata
        | proj =>
      simp only [Expr.getAppFn] at hhead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead]
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn]

/-- Restoring a completely lowered expression is a left inverse, up to Lean
expression equivalence, of the nested-expression traversal. The proof follows
the same top-down stopping rule as `Expr.replace`: hits restore immediately,
while certified misses recurse through the renamed children. -/
theorem NestedExprReopening.restore_eqv
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat) :
    ((Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      Expr.reopenFVarsAt input Hselection.fvars restoreFvars k) = true := by
  induction H generalizing k with
  | @hit hitInput hitState hitOutput nextState Hnode =>
    have hout := Expr.reopenFVarsAt_eq_reopenParams hnd hsize
      Hselection.expressions hrestore hitOutput k
    have hin := Expr.reopenFVarsAt_eq_reopenParams hnd hsize
      Hselection.expressions hrestore hitInput k
    rcases Hnode.restoreNode restoreEnv Hselection hresultNParams with
      ⟨restored, hrestored, heqv⟩
    rw [hout, hin]
    rw [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hrestored]
    exact heqv
  | bvar Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.bvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rw [Expr.reopenFVarsAt_bvar hsize] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | fvar Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.fvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rcases Expr.reopenFVarsAt_fvar_exists hnd hsize _ k with
      ⟨restored, hopen⟩
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @mvar stepState id Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.mvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.mvar id) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @sort level stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.sort Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.sort level) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @const name levels stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.const Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.const name levels) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @lit literal stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.lit Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.lit literal) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @app fn arg stepState fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.app Hnode Hfn Harg) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateApp! (.app fn arg) fn' arg') =
        .app (R fn') (R arg') := by
      simp [R, Expr.reopenFVarsAt]
    have hinput : R (.app fn arg) = .app (R fn) (R arg) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateApp! (.app fn arg) fn' arg')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.app fn arg)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateApp! (.app fn arg) fn' arg')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def]
    rw [hnone]
    have hfn := ihFn Hsource.1 k
    have harg := ihArg Hsource.2 k
    rw [Expr.replace_eq] at hfn harg
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R fn') == R fn) = true) at hfn
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R arg') == R arg) = true) at harg
    exact Expr.app_eqv hfn harg
  | @lam name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.lam Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body') =
        .lam name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.lam name dom body bi) =
        .lam name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.lam name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.lam_eqv hdom hbody
  | @forallE name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.forallE Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body') =
        .forallE name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.forallE name dom body bi) =
        .forallE name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.forallE name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.forallE_eqv hdom hbody
  | @letE name type value body nondep stepState type' typeState value'
      valueState body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.letE Hnode Htype Hvalue Hbody) restoreEnv hnd hsize
        Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep) =
        .letE name (R0 type') (R0 value') (R1 body') nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.letE name type value body nondep) =
        .letE name (R0 type) (R0 value) (R1 body) nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLet! (.letE name type value body nondep)
      type' value' body' nondep)).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      R0 (.letE name type value body nondep)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep)) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have htype := ihType Hsource.1 k
    have hvalue := ihValue Hsource.2.1 k
    have hbody := ihBody Hsource.2.2 (k + 1)
    rw [Expr.replace_eq] at htype hvalue hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 type') == R0 type) = true) at htype
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 value') == R0 value) = true) at hvalue
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.letE_eqv htype hvalue hbody
  | @mdata data body stepState body' outState Hnode Hbody ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.mdata Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateMData! (.mdata data body) body') =
        .mdata data (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.mdata data body) = .mdata data (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateMData! (.mdata data body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.mdata data body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateMData! (.mdata data body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.mdata_eqv data hbody
  | @proj name idx body stepState body' outState Hnode Hbody ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.proj Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateProj! (.proj name idx body) body') =
        .proj name idx (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.proj name idx body) = .proj name idx (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateProj! (.proj name idx body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.proj name idx body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateProj! (.proj name idx body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.proj_eqv hbody

/-- Semantic form of the structural lowering left inverse.  Once the reopened
source expression has a canonical typed translation, restoring its lowered
image has the same translation and type.  This interprets arbitrary nested
applications (including trailing arguments) compositionally, rather than
classifying the concrete `restoreNestedNode` hit at the root. -/
theorem NestedExprReopening.restoredAbstractTypeTranslation
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat)
    (Htyped : Expr.AbstractTypeTranslation venv lparams Δ
      (Expr.reopenFVarsAt input Hselection.fvars restoreFvars k)) :
    Expr.AbstractTypeTranslation venv lparams Δ
      ((Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {})) := by
  rcases Htyped with ⟨target, Htr, Htype⟩
  have Heqv := H.restore_eqv restoreEnv Hselection hnd restoreFvars hrestore
    hsize hresultNParams Hsource k
  exact ⟨target, Htr.eqv (BEq.symm Heqv), Htype⟩

/-- Relational form consumed directly by the restored-telescope fold.  The
`ExprReplacement` certificate identifies its output with the concrete
`Expr.replace` interpreted by `restoredAbstractTypeTranslation`. -/
theorem NestedExprReopening.replacementAbstractTypeTranslation
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat)
    (restored : Expr)
    (Hreplacement : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k) restored)
    (Htyped : Expr.AbstractTypeTranslation venv lparams Δ
      (Expr.reopenFVarsAt input Hselection.fvars restoreFvars k)) :
    Expr.AbstractTypeTranslation venv lparams Δ restored := by
  rw [Hreplacement.eq_replace]
  exact H.restoredAbstractTypeTranslation restoreEnv Hselection hnd
    restoreFvars hrestore hsize hresultNParams Hsource k Htyped

theorem RecognizedNestedReplacement.auxFVarsIn
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (HAs : LocalForallSelection lctx As)
    (hnparams : value.numParams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.auxFVarsIn HAs hnparams Hlevels Hargs Hparams Hstate

theorem NestedReplacement.auxFVarsIn
    (H : NestedReplacement env lctx params As e state out)
    (HAs : LocalForallSelection lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.auxFVarsIn HAs Hcandidate.parameters.arity
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hparams
    · exact Hstate

theorem RecognizedNestedReplacement.pendingNewTypesClosed
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.pendingNewTypesClosed Henv Hclosing Hlevels Hargs Hstate

theorem NestedReplacement.pendingNewTypesClosed
    (H : NestedReplacement env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.pendingNewTypesClosed Henv Hclosing
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hstate

theorem RecognizedNestedReplacement.newTypesLE
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : NestedNewTypesLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.newTypesLE

theorem RecognizedNestedReplacement.nestedAuxLE
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : NestedAuxLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.nestedAuxLE

theorem RecognizedNestedReplacement.namesWF
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesWF Hindex Hstate

theorem RecognizedNestedReplacement.namesFresh
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesFresh Hstate

theorem NestedReplacement.newTypesLE
    (H : NestedReplacement env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.newTypesLE

theorem NestedReplacement.nestedAuxLE
    (H : NestedReplacement env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.nestedAuxLE

theorem NestedReplacement.namesWF
    (H : NestedReplacement env lctx params As e state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesWF Hindex Hstate

theorem NestedReplacement.namesFresh
    (H : NestedReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesFresh Hstate

theorem NestedExprReplacement.newTypesLE
    (H : NestedExprReplacement env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | hit Hnode => exact Hnode.newTypesLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.newTypesLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.newTypesLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.newTypesLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.newTypesLE.trans ihBody

theorem NestedExprReplacement.nestedAuxLE
    (H : NestedExprReplacement env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | hit Hnode => exact Hnode.nestedAuxLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.nestedAuxLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.nestedAuxLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.nestedAuxLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.nestedAuxLE.trans ihBody

theorem NestedExprReplacement.namesWF
    (H : NestedExprReplacement env lctx params As e state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | hit Hnode => exact Hnode.namesWF Hindex Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesWF Hindex Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hindex Hstate))
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hindex Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesWF Hindex Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesWF Hindex Hstate)

theorem NestedExprReplacement.namesFresh
    (H : NestedExprReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | hit Hnode => exact Hnode.namesFresh Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesFresh Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesFresh Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesFresh Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesFresh Hstate)

theorem NestedExprReplacement.pendingNewTypesClosed
    (H : NestedExprReplacement env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | hit Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2
      (ihFn Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2
      (ihDom Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2
      (ihValue Hinput.2.1
        (ihType Hinput.1
          (Hnode.pendingNewTypesClosed Henv Hclosing
            ⟨Hinput.1, Hinput.2.1, Hinput.2.2⟩ Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody Hinput
      (Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate)

theorem NestedExprReplacement.auxFVarsIn
    (H : NestedExprReplacement env lctx params As e state out)
    (HAs : LocalForallSelection lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H generalizing P with
  | hit Hnode => exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2 Hparams
      (ihFn Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2 Hparams
      (ihDom Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2 Hparams
      (ihValue Hinput.2.1 Hparams
        (ihType Hinput.1 Hparams
          (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput Hparams
      (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)

theorem NestedExprReplacement.finalMapping
    (H : NestedExprReplacement env lctx params As input state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    NestedExprMapping env lctx params As finalResult input state out := by
  induction H generalizing finalState with
  | hit Hnode => exact .hit (Hnode.finalMapping Hlater Hmap)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    exact .app Hnode (ihFn (Harg.nestedAuxLE.trans Hlater) Hmap)
      (ihArg Hlater Hmap)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact .lam Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact .forallE Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact .letE Hnode
      (ihType (Hvalue.nestedAuxLE.trans
        (Hbody.nestedAuxLE.trans Hlater)) Hmap)
      (ihValue (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | mdata Hnode Hbody ihBody => exact .mdata Hnode (ihBody Hlater Hmap)
  | proj Hnode Hbody ihBody => exact .proj Hnode (ihBody Hlater Hmap)

theorem replaceAllNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As e env state).WF
      fun out => NestedExprReplacement env lctx params As e state out := by
  induction e generalizing state with
  | bvar i =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.bvar i)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.bvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | fvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.fvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.fvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | mvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.mvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.mvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | sort level =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.sort level)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.sort Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | const name levels =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.const name levels) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.const Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | lit literal =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lit literal) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.lit Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | app fn arg ihFn ihArg =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.app fn arg) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihFn state) ?_
      intro fn' fnState Hfn
      refine nestedBind.WF (ihArg fnState) ?_
      intro arg' outState Harg
      exact Except.WF.pure (.app Hnode Hfn Harg)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | lam name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lam name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.lam Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | forallE name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.forallE name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.forallE Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.letE name type value body nondep) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihType state) ?_
      intro type' typeState Htype
      refine nestedBind.WF (ihValue typeState) ?_
      intro value' valueState Hvalue
      refine nestedBind.WF (ihBody valueState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.letE Hnode Htype Hvalue Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | mdata data body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.mdata data body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.mdata Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | proj name idx body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.proj name idx body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.proj Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)

/-- Any successful replacement is rooted in an occurrence satisfying the
independent recognition contract. This prefix theorem intentionally leaves
cache reuse and fresh auxiliary generation to separate certificates. -/
theorem replaceIfNested_recognized
    (lctx : LocalContext) (params As : Array Expr) (e : Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested
      lctx params As e env state).WF fun out =>
        out.1.isSome → ∃ info, NestedAppCandidate env state e info := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧ ∀ info, recognized.1 = some info →
        NestedAppCandidate env state e info) ?_ ?_
  · intro recognized hrecognized
    exact ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized⟩
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate⟩
    cases hstate
    cases recognized with
    | none =>
      exact Except.WF.pure (by simp)
    | some info =>
      intro out _ hout
      exact ⟨info, hcandidate info rfl⟩

/-- Structural contract for one constructor after nested lowering.  It
records the exact source telescope opened by the executable pass, the arity
check performed before rebuilding it, and the fact that lowering changes
only the constructor type.  The node-level replacement semantics are exposed
separately by `replaceIfNested_recognized`. -/
structure LoweredConstructorShape
    (nparams : Nat) (source target : Constructor) : Prop where
  name : target.name = source.name
  rebuilt : ∃ lctx tail As lowered,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ _ : LocalForallSelection lctx As,
      As.size = nparams ∧ target.type = lctx.mkForall As lowered

theorem LoweredConstructorShape.targetRestoreTelescope
    (H : LoweredConstructorShape nparams source target) :
    RestoreTelescope target.type nparams := by
  rcases H.rebuilt with
    ⟨lctx, tail, As, lowered, Hopening, Hselection, hsize, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

inductive LoweredConstructorShapes (nparams : Nat) :
    List Constructor → List Constructor → Prop
  | nil : LoweredConstructorShapes nparams [] []
  | cons : LoweredConstructorShape nparams source target →
      LoweredConstructorShapes nparams sources targets →
      LoweredConstructorShapes nparams (source :: sources) (target :: targets)

theorem ElimNestedInductive.lowerConstructor.shape
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out => LoweredConstructorShape nparams ctor out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening _Hctx Hselection _hnodup _hnewTypes
    _hnestedAux _hnextIdx
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As tail)
    (P := fun _ => True) ?_ ?_
  · intro _ _
    trivial
  · intro lowered nextState _
    exact Except.WF.pure
      ⟨rfl, lctx, tail, As, lowered, Hopening, Hselection, hsize, rfl⟩

/-- Semantic constructor-lowering certificate.  In addition to the rebuilt
telescope shape, it records the complete stateful nested-expression
translation from the opened source tail to the installed constructor type. -/
structure LoweredConstructorTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  translated : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReplacement env lctx params As tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

theorem LoweredConstructorTranslation.targetRestoreTelescope
    (H : LoweredConstructorTranslation env params nparams source state out) :
    RestoreTelescope out.1.type nparams := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hreplace, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

theorem LoweredConstructorTranslation.newTypesLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, hopenedTypes, _, _,
      _, Hreplace, _⟩
  rcases Hreplace.newTypesLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedTypes] using hsuffix⟩

theorem LoweredConstructorTranslation.nestedAuxLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux, _, _,
      Hreplace, _⟩
  rcases Hreplace.nestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedAux] using hsuffix⟩

theorem LoweredConstructorTranslation.namesWF
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      hopenedNext, _, Hreplace, _⟩
  exact Hreplace.namesWF Hindex
    (Hstate.ofCacheCounterEq hopenedAux hopenedNext)

theorem LoweredConstructorTranslation.namesFresh
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      _, _, Hreplace, _⟩
  exact Hreplace.namesFresh (Hstate.ofCacheEq hopenedAux)

theorem LoweredConstructorTranslation.auxFVarsIn
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, _hopenedTypes, hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hinput : tail.FVarsIn
      (fun fv => fv ∈ Hselection.fvars ∨ P fv) :=
    Htail.mono fun _ hfv => Or.inl hfv
  have Hopened : NestedAuxFVarsIn P openedState := by
    intro nested name hentry
    apply Hstate nested name
    rwa [hopenedAux] at hentry
  exact Hreplace.auxFVarsIn Hselection Hinput Hparams Hopened

/-- Constructor lowering interpreted against the final restoration map. The
opened source telescope and rebuilt target telescope are retained verbatim,
while the body traversal is promoted from operational replacement to the
semantic `NestedExprMapping` relation. -/
structure LoweredConstructorMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  mapped : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprMapping env lctx params As finalResult tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- Constructor lowering with its expression mapping upgraded pointwise to
reopening under a restoration parameter array. -/
structure LoweredConstructorReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  reopened : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReopening env lctx params As finalResult restoreAs tail
        openedState (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- A mapped lowered constructor type contains no free-variable IDs: the
translated body remains scoped by the copied source parameters, and the
rebuilt forall telescope closes exactly those parameters. -/
theorem LoweredConstructorMapping.targetFVarIdsClosed
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    out.1.type.FVarIdsIn fun _ => False := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  have Hlowered : lowered.FVarIdsIn (· ∈ Hselection.fvars) :=
    Hmapping.outputFVarIdsIn Hselection (FVarsIn_to_FVarIdsIn Htail)
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rw [htype]
  exact Hopening.toRestoreParamOpening.root_mkForall_fvarIdsClosed hlctxWF
    Htelescope (FVarsIn_to_FVarIdsIn Hsource) Hselection Hlowered

/-- Source and lowered constructor types have exactly the same retained
forall prefix; lowering changes only the residual constructor body. -/
theorem LoweredConstructorMapping.sourceTargetSameForallPrefix
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    Expr.SameForallPrefix nparams source.type out.1.type := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rcases Hopening.toRestoreParamOpening.forall_rebuilding_data hlctxWF
      Htelescope with
    ⟨decls, _hlctx, hparams, _hlength, _hdeclNodup, _hfind, hrebuild⟩
  have hids : Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions]
      apply Array.toList_inj.mp
      simpa [Function.comp_def] using hparams
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have hsourceFold :
      Hselection.fvars.foldr
          (fun fv result =>
            LocalContext.mkBindingList1 false lctx [] fv
              (result.abstract1 fv)) tail = source.type := by
    have hclosed := FVarsIn_to_FVarIdsIn Hsource
    have havoid : source.type.FVarIdsIn
        (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
      hclosed.mono fun fv hfalse => False.elim hfalse
    simpa [hids] using hrebuild havoid
  have htargetFold : lctx.mkForall As lowered =
      Hselection.fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 false lctx [] fv
            (result.abstract1 fv)) lowered := by
    calc
      lctx.mkForall As lowered =
          lctx.mkForall (Hselection.fvars.map Expr.fvar).toArray lowered :=
        congrArg (fun xs => lctx.mkForall xs lowered) Hselection.expressions
      _ = _ := by
        rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
        apply LocalContext.mkBindingList_eq_fold
        · intro fv hfv
          rcases Hselection.declarations fv hfv with
            ⟨index, name, type, bi, kind, hfind⟩
          exact ⟨.cdecl index fv name type bi kind, hfind⟩
        · exact hnodupAs
  have hsame := LocalContext.sameForallPrefix_fold
    Hselection.declarations tail lowered
  have hlen : Hselection.fvars.length = nparams := by
    have := congrArg Array.size Hselection.expressions
    simpa [hsize] using this.symm
  rw [hlen] at hsame
  rw [hsourceFold, ← htargetFold, ← htype] at hsame
  exact hsame

theorem LoweredConstructorMapping.reopens
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopening env params nparams finalResult restoreAs source
      state out := by
  refine ⟨H.name, ?_⟩
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hmapping.reopens hresultParams fvars hparams hnodup Hselection Htail,
    htype⟩

/-- Opening the lowered constructor with restoration's fresh parameters
produces the lowering body renamed from its original parameter selection to
the concrete restoration array. -/
theorem LoweredConstructorReopening.restoreTail
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs := by
  rcases H.reopened with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype⟩
  have Htelescope := Hselection.forallTelescope lowered
  rw [hsize, ← htype] at Htelescope
  have htail := Hrestore.forallResidual Htelescope
  have habstract : lowered.abstract As =
      lowered.abstractList Hselection.fvars :=
    calc
      lowered.abstract As = lowered.abstract
          (Hselection.fvars.map Expr.fvar).toArray :=
        congrArg lowered.abstract Hselection.expressions
      _ = lowered.abstractList Hselection.fvars :=
        Expr.abstract_eq lowered Hselection.fvars
  refine ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype,
    ?_⟩
  simpa [habstract] using htail

/-- The body exposed by restoration is the original constructor body with
the restoration parameters substituted for lowering's fresh parameters.
This is the constructor-scoped inverse theorem: it combines the exact two
telescope traversals with the structural inverse for nested replacement. -/
theorem LoweredConstructorReopening.restoreTail_inverse
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail)
    (restoreEnv : Environment)
    (htargetAs : targetAs = restoreAs)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs ∧
        ((restoredTail.replace
            (finalResult.restoreNestedNode restoreEnv restoreAs {})) ==
          Expr.reopenParams tail As restoreAs) = true := by
  rcases H.restoreTail restoreLctx restoreAs restoredTail Hrestore with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
      htype, hrestoredTail⟩
  rcases Hrestore.params_fvars_extension with
    ⟨restoreFvars, hrestoreList, hrestoreLength⟩
  have hrestoreArray :
      restoreAs = (restoreFvars.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa using hrestoreList
  have hselectionLength : Hselection.fvars.length = As.size := by
    simpa using (congrArg Array.size Hselection.expressions).symm
  have hrestoreSize :
      restoreFvars.length = Hselection.fvars.length := by
    rw [hrestoreLength, hselectionLength, hsize]
  have hresultSize : finalResult.nparams = As.size := by
    rw [hresultNParams, hsize]
  have HtailSource : RestoreSourceDisjoint finalResult restoreEnv tail :=
    Hopening.tailRestoreSourceDisjoint Hsource
  have hinverse := Hreopening.restore_eqv restoreEnv Hselection hnodupAs
    restoreFvars
    (by simpa [htargetAs] using hrestoreArray) hrestoreSize hresultSize
    HtailSource 0
  have hloweredOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray lowered 0
  have hsourceOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray tail 0
  have hrestoredOpen :
      restoredTail = Expr.reopenParams lowered As restoreAs := by
    simpa [Expr.reopenParams] using hrestoredTail
  rw [htargetAs, hloweredOpen, hsourceOpen, ← hrestoredOpen] at hinverse
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
    htype, hrestoredTail, hinverse⟩

/-- Operational constructor restoration consumes a mapped lowering body and
produces the correspondingly renamed source body.  Unlike
`restoreTail_inverse`, this theorem starts from the mapping certificate
available before restoration chooses its fresh variables and concludes about
the `restoredBody` retained by `NestedRestoration`. -/
theorem LoweredConstructorMapping.restoredBody_inverse
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (restoreEnv : Environment)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
  have Hreopening : LoweredConstructorReopening env params nparams finalResult
      restoreAs source state out :=
    H.reopens hresultParams paramFvars hparams hnodup HsourceClosed
  rcases Hreopening.restoreTail_inverse restoreLctx restoreAs openedBody
      Hrestore restoreEnv rfl hresultNParams Hsource with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, _hopenedTypes, _hopenedAux, _hopenedNext, hsize,
      _Hreopening, _htype, _hopenedBody, hinverse⟩
  have hrestoredInverse :
      (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
    rw [Hbody.eq_replace]
    exact hinverse
  exact ⟨lctx, tail, As, Hopening, Hselection, hnodupAs, hsize,
    hrestoredInverse⟩

theorem LoweredConstructorMapping.restoredBody_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved finalResult restoreEnv)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true :=
  H.restoredBody_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreLctx restoreAs openedBody restoredBody Hrestore
    restoreEnv Hbody hresultNParams
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved)

/-- A whole operational `NestedRestoration` of a lowered constructor, with
its restored body related back to the independently checked source
constructor body.  The outer telescope equations are retained explicitly;
the next abstraction layer can therefore prove alpha-equivalence without
replaying either executable traversal. -/
structure ConstructorRestorationBodyInverse
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (nparams : Nat) (source lowered : Constructor) (restoredType : Expr) where
  restoreLctx : LocalContext
  restoreAs : Array Expr
  openedBody : Expr
  restoredBody : Expr
  loweredOpening : RestoreParamOpening {} #[] lowered.type nparams
    restoreLctx restoreAs openedBody
  restoreLctxWF : restoreLctx.WF
  restoreSelection : LocalForallSelection restoreLctx restoreAs
  restoreNodup : restoreSelection.fvars.Nodup
  bodyRestoration : ExprReplacement
    (result.restoreNestedNode env restoreAs {}) openedBody restoredBody
  output : restoredType = if lowered.type.isForall then
    restoreLctx.mkForall restoreAs restoredBody
    else restoreLctx.mkLambda restoreAs restoredBody
  sourceLctx : LocalContext
  sourceTail : Expr
  sourceAs : Array Expr
  sourceClosed : source.type.FVarsIn fun _ => False
  loweredFVarIdsClosed : lowered.type.FVarIdsIn fun _ => False
  sourceLoweredPrefix :
    Expr.SameForallPrefix nparams source.type lowered.type
  sourceOpening : NestedParamOpening {} #[] source.type nparams sourceLctx
    sourceTail sourceAs
  sourceSelection : LocalForallSelection sourceLctx sourceAs
  sourceNodup : sourceSelection.fvars.Nodup
  sourceArity : sourceAs.size = nparams
  bodyInverse :
    (restoredBody == Expr.reopenParams sourceTail sourceAs restoreAs) = true

/-- Whole-constructor restoration inverse stated at its semantic boundary.
This form does not assume any naming convention for generated auxiliary
constructors; callers may establish source disjointness from typing and
freshness instead. -/
theorem LoweredConstructorMapping.nestedRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  rcases Hrestored with
    ⟨restoreLctx, restoreAs, openedBody, restoredBody, Hopening,
      Hbody, houtput⟩
  rcases Hopening.2 with ⟨hrestoreLctxWF, HrestoreSelection,
    hrestoreNodup⟩
  have Hopening' := Hopening.1
  rw [hresultNParams] at Hopening'
  rcases H.restoredBody_inverse hresultParams paramFvars hparams hnodup
      HsourceClosed restoreLctx restoreAs openedBody restoredBody Hopening'
      restoreEnv Hbody hresultNParams HsourceDisjoint with
    ⟨sourceLctx, sourceTail, sourceAs, HsourceOpening, Hselection,
      hsourceNodup, hsourceArity, hinverse⟩
  exact ⟨{
    restoreLctx := restoreLctx
    restoreAs := restoreAs
    openedBody := openedBody
    restoredBody := restoredBody
    loweredOpening := Hopening'
    restoreLctxWF := hrestoreLctxWF
    restoreSelection := HrestoreSelection
    restoreNodup := hrestoreNodup
    bodyRestoration := Hbody
    output := houtput
    sourceLctx := sourceLctx
    sourceTail := sourceTail
    sourceAs := sourceAs
    sourceClosed := HsourceClosed
    loweredFVarIdsClosed := H.targetFVarIdsClosed HsourceClosed
    sourceLoweredPrefix := H.sourceTargetSameForallPrefix HsourceClosed
    sourceOpening := HsourceOpening
    sourceSelection := Hselection
    sourceNodup := hsourceNodup
    sourceArity := hsourceArity
    bodyInverse := hinverse }⟩

theorem LoweredConstructorMapping.nestedRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  exact H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored

/-- Eliminate the source-opening free variables from the body inverse.  The
restored body is the ordinary residual of the original constructor telescope,
instantiated only with restoration's fresh parameter array. -/
theorem ConstructorRestorationBodyInverse.restoredBody_residual
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    ∃ residual,
      Expr.ForallTelescope source.type nparams residual ∧
      (H.restoredBody == residual.instantiateRev H.restoreAs) = true := by
  rcases H.sourceOpening.forallTelescope with ⟨residual, Htelescope⟩
  have htail : H.sourceTail = residual.instantiateRev H.sourceAs :=
    H.sourceOpening.toRestoreParamOpening.forallResidual Htelescope
  have hfree : residual.FVarsIn
      (fun fv => fv ∉ H.sourceSelection.fvars) :=
    (Htelescope.resultFVarsIn H.sourceClosed).mono fun fv hfalse =>
      False.elim hfalse
  have hcancel := hfree.reabstract_instantiateRev_fvarArray H.sourceAs
    H.restoreAs H.sourceSelection.fvars H.sourceSelection.expressions
    H.sourceNodup
  have hopen : Expr.reopenParams H.sourceTail H.sourceAs H.restoreAs =
      residual.instantiateRev H.restoreAs := by
    rw [htail]
    simpa [Expr.reopenParams] using hcancel
  have hinverse := H.bodyInverse
  rw [hopen] at hinverse
  exact ⟨residual, Htelescope, hinverse⟩

/-- Whole-constructor inverse: rebuilding the restored body under the copied
parameter telescope yields a constructor type equivalent to the independent
source constructor type. -/
theorem ConstructorRestorationBodyInverse.restoredType_eqv_source
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    (restoredType == source.type) = true := by
  rcases H.sourceLoweredPrefix.transferRestoreOpening H.loweredOpening with
    ⟨sourceOpened, HsourceRestore⟩
  rcases H.restoredBody_residual with
    ⟨residual, Htelescope, hbodyResidual⟩
  have hsourceOpened :
      sourceOpened = residual.instantiateRev H.restoreAs :=
    HsourceRestore.forallResidual Htelescope
  have hbodyOpened : (H.restoredBody == sourceOpened) = true := by
    rw [hsourceOpened]
    exact hbodyResidual
  have hclosedSource : source.type.FVarIdsIn fun _ => False :=
    FVarsIn_to_FVarIdsIn H.sourceClosed
  have hsourceRebuild :
      H.restoreLctx.mkForall H.restoreAs sourceOpened = source.type :=
    HsourceRestore.root_mkForall_tail H.restoreLctxWF Htelescope hclosedSource
  have hwrapped := H.restoreSelection.mkForall_eqv H.restoreNodup hbodyOpened
  rw [hsourceRebuild] at hwrapped
  have houtput : restoredType =
      H.restoreLctx.mkForall H.restoreAs H.restoredBody := by
    refine H.output.trans ?_
    by_cases hzero : nparams = 0
    · have hsize : H.restoreAs.size = 0 :=
        H.loweredOpening.initial_size.trans hzero
      have hempty : H.restoreAs = #[] :=
        Array.eq_empty_of_size_eq_zero hsize
      rw [hempty]
      split
      · rfl
      · rw [LocalContext.mkForall, LocalContext.mkLambda]
        rw [show (#[] : Array Expr) =
            (([] : List FVarId).map Expr.fvar).toArray from rfl,
          LocalContext.mkBinding_eq, LocalContext.mkBinding_eq]
        simp only [LocalContext.mkBindingList_nil]
    · have hpos : 0 < nparams := Nat.pos_of_ne_zero hzero
      have hisForall :=
        H.sourceLoweredPrefix.target_isForall_of_pos hpos
      simp [hisForall]
  rw [houtput]
  exact hwrapped

/-- Metadata-facing form of the constructor inverse.  Installation exposes a
`ConstructorVal`, while lowering is indexed by the corresponding
`Constructor`; the explicit type equality is the only alignment fact needed
to connect the two verified traces. -/
theorem LoweredConstructorMapping.constructorRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    HsourceClosed restoreEnv HsourceDisjoint hresultNParams
  simpa [htype] using Hrestored.type

theorem LoweredConstructorMapping.constructorRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverseOfSyntax hresultParams paramFvars hparams
    hnodup Hsyntax restoreEnv Hreserved hresultNParams
  simpa [htype] using Hrestored.type

/-- Transport source translation across constructor restoration using exact
semantic disjointness, without imposing a namespace convention on generated
constructor names. -/
theorem LoweredConstructorMapping.restoredType_translation
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed restoreEnv HsourceDisjoint hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  apply Hsource.eqv
  simpa [beq_comm] using Hinverse.restoredType_eqv_source

/-- Transport a source constructor's abstract translation across lowering and
restoration.  This is the semantic premise needed by constructor installation;
unlike translation of the lowered constructor, it is obtained from the
independent pre-lowering source type. -/
theorem LoweredConstructorMapping.restoredType_translationOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  exact H.restoredType_translation hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored htype Hsource

/-- Install a restored constructor from its independent source translation
and exact semantic disjointness from the generated auxiliary declarations. -/
theorem RestoredConstructorStep.installationOfDisjoint
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid constructor Hsafety Huvars Hname
  · exact Hmapping.restoredType_translation hresultParams paramFvars
      hparams hnodup HsourceClosed loweredEnv HsourceDisjoint hresultNParams
      Hstep.restored.restoration htype Hsource
  · exact Hwf

/-- Source-declaration specialization of `installationOfDisjoint`.  A single
`TrSourceConst` supplies the abstract constructor used both by the source
`TrInductDeclCore` and by the exact restored installation trace. -/
theorem RestoredConstructorStep.installationOfSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup HsourceClosed HsourceDisjoint hresultNParams htype Hvalid
    constructor Hsafety
  · rw [hlevels]
    exact Hsource.uvars.symm
  · exact hname.trans Hsource.name.symm
  · simpa [hlevels] using Hsource.type
  · exact Hsource.wf

/-- Preferred source-syntax installation endpoint. Auxiliary family names are
reserved by the lowering cache, while auxiliary constructor names need only
be fresh in the abstract source environment; no constructor namespace
convention is assumed. -/
theorem RestoredConstructorStep.installationOfFresh
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact Huvars
  · exact Hname
  · exact Hsource
  · exact Hwf

/-- Preferred end-to-end constructor endpoint.  Fresh-cache lowering gives
the semantic restoration disjointness, while the independent source
translation is reused unchanged by declaration formation and installation. -/
theorem RestoredConstructorStep.installationOfFreshSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfSource Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.type.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact hlevels
  · exact hname
  · exact Hsource

/-- Namespace-based convenience specialization of
`installationOfDisjoint`.  The semantic endpoint above is the preferred path
for arbitrary kernel constructor names. -/
theorem RestoredConstructorStep.installationOfSyntax
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hreserved : RestoreNamesReserved result loweredEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv
      (.ctorInfo Hstep.oldInfo) constructor)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams htype
    Hvalid constructor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hold.2
  · exact Hsource
  · exact Hwf

theorem LoweredConstructorTranslation.finalMapping
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMapping env params nparams finalResult source state out := by
  refine ⟨H.name, ?_⟩
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreplace, htype⟩
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hreplace.finalMapping Hlater Hmap, htype⟩

theorem ElimNestedInductive.lowerConstructor.translation
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening Hctx Hselection hnodup hopenedTypes
    hopenedAux hopenedNext
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  exact Except.WF.pure
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening, Hctx.wf, Hselection,
      hnodup, hopenedTypes, hopenedAux, hopenedNext, hsize, Hlowered, rfl⟩

theorem ElimNestedInductive.lowerConstructor.translationPending
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctor : ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesClosing (Htype := Hctor)
  intro lctx tail As openedState Hopening Hclosing Htail hopenedTypes
    hopenedAux hopenedNext
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  have HopenedPending : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  exact Except.WF.pure ⟨
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening,
      Hclosing.binding.wf, Hclosing.selection, Hclosing.nodup,
      hopenedTypes, hopenedAux, hopenedNext, hsize,
      Hlowered, rfl⟩,
    Hlowered.pendingNewTypesClosed Henv Hclosing Htail HopenedPending⟩

/-- Stateful positional correspondence for an entire constructor list. -/
inductive LoweredConstructorTranslations
    (env : Environment) (params : Array Expr) (nparams : Nat) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorTranslations env params nparams [] state ([], state)
  | cons : LoweredConstructorTranslation env params nparams source state step →
      LoweredConstructorTranslations env params nparams sources step.2 out →
      LoweredConstructorTranslations env params nparams (source :: sources)
        state (step.1 :: out.1, out.2)

theorem LoweredConstructorTranslations.newTypesLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.newTypesLE.trans ih

theorem LoweredConstructorTranslations.nestedAuxLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.nestedAuxLE.trans ih

theorem LoweredConstructorTranslations.namesWF
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesWF Hindex Hstate)

theorem LoweredConstructorTranslations.namesFresh
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesFresh Hstate)

theorem LoweredConstructorTranslations.auxFVarsIn
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    apply ih
    · intro source hsource
      exact Hsources source (by simp [hsource])
    · exact Hhead.auxFVarsIn (Hsources _ (by simp)) Hparams Hstate

inductive LoweredConstructorMappings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorMappings env params nparams finalResult [] state
      ([], state)
  | cons : LoweredConstructorMapping env params nparams finalResult source
      state step →
      LoweredConstructorMappings env params nparams finalResult sources step.2
        out →
      LoweredConstructorMappings env params nparams finalResult
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.length
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) : out.1.length = sources.length := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [ih]

/-- Positional projection of the state-threaded constructor mapping.  Both
the source and target list lookups are retained, so subsequent restoration
folds can align their metadata without a name-based uniqueness assumption. -/
theorem LoweredConstructorMappings.mappingAt
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) (i : Nat) (hi : i < sources.length) :
    ∃ source target before after,
      sources[i]? = some source ∧
      out.1[i]? = some target ∧
      LoweredConstructorMapping env params nparams finalResult source before
        (target, after) := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons source state step sources out Hhead Htail ih =>
    cases i with
    | zero => exact ⟨source, step.1, state, step.2, by simp, by simp, Hhead⟩
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rcases ih i hi with
        ⟨tailSource, tailTarget, before, after, hsource, htarget, Hmapping⟩
      exact ⟨tailSource, tailTarget, before, after, by simpa, by simpa,
        Hmapping⟩

/-- Lockstep alignment of the state-threaded constructor lowering relation
with the exact operational restoration fold.  The production lookup theorem
has already identified the `oldInfo.type` read at every step with that step's
positionally corresponding lowered constructor type. -/
inductive RestoredConstructorMappingTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams [] state [] state sourceProdEnv sourceProdEnv
  | cons
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hrest : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams sources nextState targets finalState
          middleProdEnv targetProdEnv) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
        safety lparams (source :: sources) state (target :: targets) finalState
          sourceProdEnv targetProdEnv

/-- Build the lockstep constructor trace from verified lowered installation.
The only list premise is that all mapped targets belong to the installed
owner; in the family specialization this is immediate because `targets` is
that owner's constructor list. -/
theorem RestoredConstructorMappingTrace.ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hprod : RecursorPhasesResult R loweredEnv)
    (howner : owner ∈ indTypes.toList)
    (Hmapping : LoweredConstructorMappings mappingEnv params nparams result
      sources state (targets, finalState))
    (Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv)
    (Htargets : ∀ target ∈ targets, target ∈ owner.ctors) :
    RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
      c.safety c.lparams sources state targets finalState sourceProdEnv
        targetProdEnv := by
  cases Hmapping with
  | nil =>
    cases Htrace
    exact .nil _ _
  | cons Hhead Htail =>
    cases Htrace with
    | cons Hstep Hsteps =>
      have Hmetadata := Hstep.metadataOfInstalled Hprod howner
        (Htargets _ (by simp)) rfl
      apply RestoredConstructorMappingTrace.cons Hhead Hstep
      · exact Hmetadata.1
      · exact Hmetadata.2.1
      · exact Hmetadata.2.2
      · exact Hstep.oldType_eq_ofInstalled Hprod howner
          (Htargets _ (by simp)) rfl
      · apply RestoredConstructorMappingTrace.ofInstalled Hprod howner
          Htail Hsteps
        intro target htarget
        exact Htargets target (by simp [htarget])

/-- Interpret the proof-independent lowering/restoration trace against the
independently translated source constructors.  This is the constructor-list
implementation/specification bridge: every executable restoration step is
shown to translate the same abstract constructor that appears in the source
inductive specification. -/
theorem RestoredConstructorMappingTrace.sourceSemantics
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    RestoredSourceConstructorTrace lparams safety canonicalEnv
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv
        sources constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i vctor vconstructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type vctor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type vctor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) vctor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredSourceConstructorTrace.cons Hstep
          { constructor := vctor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

inductive LoweredConstructorReopenings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorReopenings env params nparams finalResult restoreAs
      [] state ([], state)
  | cons : LoweredConstructorReopening env params nparams finalResult restoreAs
      source state step →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        sources step.2 out →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.reopens
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopenings env params nparams finalResult restoreAs
      sources state out := by
  induction H with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    apply LoweredConstructorReopenings.cons
    · exact Hhead.reopens hresultParams fvars hparams hnodup
        (Hsources _ (by simp))
    · apply ih
      intro source hsource
      exact Hsources source (by simp [hsource])

theorem LoweredConstructorTranslations.finalMapping
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMappings env params nparams finalResult sources state out := by
  induction H generalizing finalState with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    exact .cons
      (Hhead.finalMapping (Htail.nestedAuxLE.trans Hlater) Hmap)
      (ih Hlater Hmap)

theorem LoweredConstructorTranslations.targetsRestoreTelescope
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    ∀ ctor ∈ out.1, RestoreTelescope ctor.type nparams := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.targetRestoreTelescope
    · exact ih ctor htail

theorem ElimNestedInductive.lowerConstructors.translations
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translation params nparams ctor
        env state hparams hclosures) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

theorem ElimNestedInductive.lowerConstructors.translationsPending
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctors : ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out ∧
        PendingNewTypesClosed cursor out.2 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure ⟨.nil, Hstate⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translationPending params nparams
        ctor env state hparams hclosures Henv (Hctors ctor (by simp)) Hstate) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState
      (fun tail htail => Hctors tail (by simp [htail])) Hlowered.2) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure ⟨.cons Hlowered.1 Htail.1, Htail.2⟩

theorem ElimNestedInductive.lowerConstructors.shapes
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (ctors.mapM
      (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorShapes nparams ctors out.1 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.shape
        params nparams ctor env state) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

/-- Family-level lowering preserves the family header verbatim and changes
only its positionally corresponding constructor types. -/
structure LoweredInductiveShape
    (nparams : Nat) (source target : InductiveType) : Prop where
  name : target.name = source.name
  type : target.type = source.type
  constructors : LoweredConstructorShapes nparams source.ctors target.ctors

theorem ElimNestedInductive.lowerInductive.shape
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out => LoweredInductiveShape nparams indType out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.shapes
      params nparams indType.ctors env state) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

/-- Family-level semantic lowering: headers are preserved and the constructor
list carries the full state-threaded nested-expression translation. -/
structure LoweredInductiveTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorTranslations env params nparams source.ctors
    state (out.1.ctors, out.2)

structure LoweredInductiveMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorMappings env params nparams finalResult
    source.ctors state (out.1.ctors, out.2)

structure LoweredInductiveReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorReopenings env params nparams finalResult
    restoreAs source.ctors state (out.1.ctors, out.2)

theorem LoweredInductiveMapping.reopens
    (H : LoweredInductiveMapping env params nparams finalResult source state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False) :
    LoweredInductiveReopening env params nparams finalResult restoreAs source
      state out :=
  ⟨H.name, H.type,
    H.constructors.reopens hresultParams fvars hparams hnodup Hsource⟩

theorem LoweredInductiveTranslation.newTypesLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := H.constructors.newTypesLE

theorem LoweredInductiveTranslation.nestedAuxLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := H.constructors.nestedAuxLE

theorem LoweredInductiveTranslation.namesWF
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 :=
  H.constructors.namesWF Hindex Hstate

theorem LoweredInductiveTranslation.namesFresh
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 :=
  H.constructors.namesFresh Hstate

theorem LoweredInductiveTranslation.auxFVarsIn
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 :=
  H.constructors.auxFVarsIn Hsource Hparams Hstate

theorem LoweredInductiveTranslation.finalMapping
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredInductiveMapping env params nparams finalResult source state out :=
  ⟨H.name, H.type, H.constructors.finalMapping Hlater Hmap⟩

theorem LoweredInductiveTranslation.targetRestoreTelescope
    (H : LoweredInductiveTranslation env params nparams source state out) :
    ∀ ctor ∈ out.1.ctors, RestoreTelescope ctor.type nparams :=
  H.constructors.targetsRestoreTelescope

def RestorableInductiveType (nparams : Nat) (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, RestoreTelescope ctor.type nparams

def RestorableNewTypesPrefix (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, j < i → (hj : j < state.newTypes.size) →
    RestorableInductiveType nparams state.newTypes[j]

theorem RestorableNewTypesPrefix.zero
    (state : Lean4Lean.ElimNestedInductive.State) :
    RestorableNewTypesPrefix nparams 0 state := by
  intro j hj
  omega

def NewTypeNamePresent (state : Lean4Lean.ElimNestedInductive.State)
    (name : Name) : Prop :=
  ∃ type ∈ state.newTypes.toList, type.name = name

theorem ElimNestedInductive.lowerInductive.translation
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translations params nparams
      indType.ctors env state hparams hclosures) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

theorem ElimNestedInductive.lowerInductive.translationPending
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed indType)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translationsPending params nparams
      indType.ctors env state hparams hclosures Henv Hsource Hstate) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨⟨rfl, rfl, Hctors.1⟩, Hctors.2⟩

/-- Semantic state transition for a dynamic lowering-queue iteration. -/
inductive LowerNextTranslation
    (env : Environment) (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType × Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextTranslation env params nparams i state (none, state)
  | step (hidx : i < state.newTypes.size)
      (Hlowered : LoweredInductiveTranslation env params nparams
        state.newTypes[i] state (target, loweredState)) :
      LowerNextTranslation env params nparams i state
        (some state.newTypes[i], { loweredState with
          newTypes := loweredState.newTypes.set! i target })

theorem LowerNextTranslation.restorablePrefix
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    RestorableNewTypesPrefix nparams (i + 1) nextState := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hidx).choose
    intro j hj hjNext
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hjNext
    by_cases hji : j = i
    · subst j
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[i]
      simpa [Array.getElem_setIfInBounds, hiLowered,
        RestorableInductiveType] using Hlowered.targetRestoreTelescope
    · have hjlt : j < i := by omega
      rcases Hle.getElem (show j < state.newTypes.size by omega) with
        ⟨hjInLowered, hsame⟩
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
          loweredState.newTypes[j] by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjInLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget]
      rw [hsame]
      exact Hprefix j hjlt _

theorem LowerNextTranslation.nestedAuxLE
    (H : LowerNextTranslation env params nparams i state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | done => exact .refl _
  | step _ Hlowered => exact Hlowered.nestedAuxLE

theorem LowerNextTranslation.namesWF
    (H : LowerNextTranslation env params nparams i state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered =>
    exact (Hlowered.namesWF Hindex Hstate).ofCacheCounterEq rfl rfl

theorem LowerNextTranslation.namesFresh
    (H : LowerNextTranslation env params nparams i state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered => exact (Hlowered.namesFresh Hstate).ofCacheEq rfl

theorem LowerNextTranslation.preservesTypeName
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hname : NewTypeNamePresent state name) :
    NewTypeNamePresent nextState name := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    rcases Hname with ⟨type, htype, hname⟩
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, htypeEq⟩
    have hjState : j < state.newTypes.size := by simpa using hj
    rcases Hlowered.newTypesLE.getElem hjState with
      ⟨hjLowered, hpreserved⟩
    have hjNext : j < (loweredState.newTypes.set! i target).size := by
      simpa [Array.size_set!] using hjLowered
    let finalType := (loweredState.newTypes.set! i target)[j]
    refine ⟨finalType, by
      exact List.getElem_mem hjNext, ?_⟩
    by_cases hji : j = i
    · subst j
      have hset : finalType = target := by
        simp [finalType, Array.getElem_setIfInBounds, hjLowered]
      rw [hset, Hlowered.name]
      have hsource : state.newTypes[i] = type := by
        simpa using htypeEq
      rw [hsource]
      exact hname
    · have hset : finalType = loweredState.newTypes[j] := by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget
      rw [hset, hpreserved]
      have : state.newTypes[j] = type := by simpa using htypeEq
      rw [this]
      exact hname

/-- A queue step changes only its selected slot. Auxiliary discovery may
append new families before that slot is overwritten, but every distinct
pre-existing index retains its exact family record. -/
theorem LowerNextTranslation.getElem_ne
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (hj : j < state.newTypes.size) (hne : j ≠ i) :
    ∃ hjNext : j < nextState.newTypes.size,
      nextState.newTypes[j] = state.newTypes[j] := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    rcases Hlowered.newTypesLE.getElem hj with
      ⟨hjLowered, hsame⟩
    have hjNext : j <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hjLowered
    refine ⟨hjNext, ?_⟩
    change (loweredState.newTypes.set! i target)[j] = state.newTypes[j]
    have hget := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun h : i = j => hne h.symm)] at hget
    simpa [Array.set!] using hget.trans hsame

/-- The selected queue slot contains the just-lowered target after the step,
even when lowering appended auxiliary families along the way. -/
theorem LowerNextTranslation.getElem_selected
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState)) (hi : i < state.newTypes.size) :
    ∃ target loweredState,
      LoweredInductiveTranslation env params nparams
        state.newTypes[i] state
        (target, loweredState) ∧
      nextState.nestedAux = loweredState.nestedAux ∧
      ∃ hiNext : i < nextState.newTypes.size,
        nextState.newTypes[i] = target := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have hiLowered := Hlowered.newTypesLE.getElem hi |>.choose
    have hiNext : i <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hiLowered
    refine ⟨target, loweredState, Hlowered, rfl, hiNext, ?_⟩
    change (loweredState.newTypes.set! i target)[i] = target
    simp [Array.getElem_setIfInBounds, hiLowered]

theorem ElimNestedInductive.lowerNext.translation
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextTranslation env params nparams i state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translation params nparams
        state.newTypes[i] env state hparams hclosures) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    exact Except.WF.pure (.step hidx Htarget)
  · rw [dif_neg hidx]
    exact Except.WF.pure (.done (Nat.le_of_not_gt hidx))

theorem ElimNestedInductive.lowerNext.translationPending
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hstate : PendingNewTypesClosed i state) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out =>
        LowerNextTranslation env params nparams i state out ∧
        PendingNewTypesClosed (i + 1) out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translationPending params nparams
        state.newTypes[i] env state hparams hclosures Henv
        (Hstate i (Nat.le_refl _) hidx) Hstate) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    have HnextPending : PendingNewTypesClosed (i + 1)
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } := by
      intro j hcursor hj
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hj
      have hne : j ≠ i := by omega
      have hvalue := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
      change InductiveConstructorsClosed
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
        loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
      exact Htarget.2 j (by omega) hjLowered
    exact Except.WF.pure ⟨.step hidx Htarget.1, HnextPending⟩
  · rw [dif_neg hidx]
    exact Except.WF.pure ⟨.done (Nat.le_of_not_gt hidx),
      fun j hcursor hj => Hstate j (by omega) hj⟩

/-- Complete semantic trace of the dynamically growing lowering queue.  The
queue stops only once the index reaches the then-current array size; each
preceding step contains the semantic family translation, including any new
auxiliary families appended while processing it. -/
inductive LoweringQueueTrace
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) : Nat → Nat →
      Lean4Lean.ElimNestedInductive.State →
      Lean4Lean.ElimNestedInductive.Result ×
        Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state
        ({ state with
          nparams := params.size
          lctx
          params
          aux2nested := state.nestedAux.foldl
            (fun map (nested, name) => map.insert name nested) {}
          types := state.newTypes.toList }, state)
  | step :
      LowerNextTranslation env params nparams i state (some source, nextState) →
      LoweringQueueTrace env params nparams lctx (i + 1) fuel nextState out →
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state out

theorem LoweringQueueTrace.resultContext
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.lctx = lctx ∧ out.1.params = params := by
  induction H with
  | done => exact ⟨rfl, rfl⟩
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNParams
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.nparams = params.size := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultAuxMap
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNestedAuxLE
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | done => exact .refl _
  | step Hnext _ ih => exact Hnext.nestedAuxLE.trans ih

theorem LoweringQueueTrace.resultNamesWF
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesWF Hindex Hstate)

theorem LoweringQueueTrace.resultNamesFresh
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesFresh Hstate)

/-- Once an index lies strictly behind the queue cursor, later lowering
steps preserve the exact family stored there through to the final result. -/
theorem LoweringQueueTrace.getElem_before
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hj : j < i) (hbound : j < state.newTypes.size) :
    out.1.types[j]? = some state.newTypes[j] := by
  induction H with
  | done =>
    simp only
    rw [List.getElem?_eq_getElem (by simpa using hbound)]
    rfl
  | step Hnext Htail ih =>
    rcases Hnext.getElem_ne hbound (by omega) with
      ⟨hnextBound, hsame⟩
    simpa [hsame] using ih (by omega) hnextBound

/-- Every not-yet-processed family within the current queue has a unique
future lowering step. The theorem retains that exact semantic translation
and identifies its target at the same index in the final result list. -/
theorem LoweringQueueTrace.translationAt
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hij : i ≤ j) (hj : j < state.newTypes.size) :
    ∃ stepState target loweredState,
      LoweredInductiveTranslation env params nparams state.newTypes[j]
        stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  revert j
  induction H with
  | done hdone =>
    intro j hij hj
    omega
  | @step iStep stateStep sourceStep nextStateStep fuelStep outStep
      Hnext Htail ih =>
    intro j hij hj
    by_cases hji : j = iStep
    · subst j
      rcases Hnext.getElem_selected hj with
        ⟨target, loweredState, Htranslated, hnextAux, hiNext, htarget⟩
      refine ⟨stateStep, target, loweredState, Htranslated, ?_, ?_⟩
      have hfinal := Htail.getElem_before (j := iStep) (by omega) hiNext
      simpa [htarget] using hfinal
      rcases Htail.resultNestedAuxLE with ⟨suffix, hsuffix⟩
      exact ⟨suffix, by simpa [hnextAux] using hsuffix⟩
    · have hij' : iStep + 1 ≤ j := by omega
      rcases Hnext.getElem_ne hj hji with ⟨hjNext, hsame⟩
      rcases ih hij' hjNext with
        ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩
      rw [hsame] at Htranslated
      exact ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩

theorem LoweringQueueTrace.resultRestorable
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    intro type htype
    simp only at htype
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, rfl⟩
    apply Hprefix j
    · have hjSize : j < stateDone.newTypes.size := by simpa using hj
      omega
  | step Hnext Htail ih =>
    exact ih (Hnext.restorablePrefix Hprefix)

theorem LoweringQueueTrace.preservesTypeName
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hname : NewTypeNamePresent state name) :
    ∃ type ∈ out.1.types, type.name = name := by
  induction H with
  | done => simpa [NewTypeNamePresent] using Hname
  | step Hnext Htail ih => exact ih (Hnext.preservesTypeName Hname)

private theorem loweringQueueLoop_refines
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translation params nparams i env state
        hparams hclosures) ?_
    intro next nextState Hnext
    cases Hnext with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure (.done hbound)
    | step hidx Hlowered =>
      exact (ih (i := i + 1) (state := _)).mono fun _ Htail =>
        LoweringQueueTrace.step (LowerNextTranslation.step hidx Hlowered) Htail

/-- The dynamic queue invariant used by auxiliary validation. Every pending
family has closed constructor types, so processing it preserves the cache
free-variable invariant and proves every newly appended family closed before
the cursor can reach it. -/
private theorem loweringQueueLoop_refinesClosed
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hpending : PendingNewTypesClosed i state)
    (Hcache : NestedAuxFVarsIn P state) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out ∧
        NestedAuxFVarsIn P out.2 := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translationPending params nparams i env
        state hparams hclosures Henv Hpending) ?_
    intro next nextState Hnext
    rcases Hnext with ⟨Htranslation, HpendingNext⟩
    cases Htranslation with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure ⟨.done hbound, Hcache⟩
    | step hidx Hlowered =>
      rename_i target loweredState
      have HcacheNext : NestedAuxFVarsIn P
          { loweredState with
            newTypes := loweredState.newTypes.set! i target } := by
        have HcacheLower := Hlowered.auxFVarsIn
          (Hpending i (Nat.le_refl _) hidx) Hparams Hcache
        intro nested name hentry
        exact HcacheLower nested name hentry
      exact (ih (i := i + 1)
        (state := { loweredState with
          newTypes := loweredState.newTypes.set! i target })
        HpendingNext HcacheNext).mono fun _ Htail =>
          ⟨LoweringQueueTrace.step (.step hidx Hlowered) Htail.1,
            Htail.2⟩

/-- End-to-end semantic certificate for nested lowering from the source
parameter telescope through the complete dynamic family queue. -/
structure NestedLoweringRun
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (out : Lean4Lean.ElimNestedInductive.Result ×
      Lean4Lean.ElimNestedInductive.State) : Prop where
  source : ∃ first rest tail paramsState lctx params,
    types = first :: rest ∧
    NestedParamOpening {} #[] first.type nparams
      lctx tail params ∧
    paramsState.newTypes = initialState.newTypes ∧
    paramsState.nestedAux = initialState.nestedAux ∧
    paramsState.nextIdx = initialState.nextIdx ∧
    NestedBindingContextWF lctx paramsState.ngen ∧
    Nonempty (LocalForallSelection lctx params) ∧
    LoweringQueueTrace env params nparams lctx 0 fuel
      paramsState out

theorem NestedLoweringRun.resultRestorable
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultRestorable (.zero paramsState)

theorem NestedLoweringRun.resultNParams
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.nparams = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultNParams.trans Hopening.initial_size

theorem NestedLoweringRun.resultParamsSize
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.size = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, Hqueue⟩
  rw [Hqueue.resultContext.2]
  exact Hopening.initial_size

/-- The final restoration context is exactly the source parameter selection
opened before the dynamic lowering queue starts. -/
theorem NestedLoweringRun.resultContextSelection
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    Nonempty (LocalForallSelection out.1.lctx out.1.params) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _,
      _Hctx, Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hselection

theorem NestedLoweringRun.resultContextWF
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.lctx.WF := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.wf

/-- Lowering stores common parameters in source binder order, whereas its
local context (and therefore every `MLCtx.vlctx`) stores free variables in
most-recent-first order. -/
theorem NestedLoweringRun.resultParams_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.toList.reverse = out.1.lctx.fvars.map Expr.fvar := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hopening.toRestoreParamOpening.root_params_reverse_fvars

/-- Any retained selection of the final parameter array lists exactly the
same free variables as the returned local context, in binder order rather
than the context's most-recent-first order. -/
theorem NestedLoweringRun.resultSelection_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (selection : LocalForallSelection out.1.lctx out.1.params) :
    selection.fvars.reverse = out.1.lctx.fvars := by
  have hparams := H.resultParams_reverse_fvars
  have hselected : out.1.params.toList =
      selection.fvars.map Expr.fvar := by
    calc
      out.1.params.toList =
          (selection.fvars.map Expr.fvar).toArray.toList :=
        congrArg Array.toList selection.expressions
      _ = selection.fvars.map Expr.fvar := by simp
  rw [hselected, ← List.map_reverse] at hparams
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hparams

/-- The executable auxiliary checks can be closed over lowering's retained
parameter telescope.  This removes the concrete free-variable names from the
semantic certificate before restoration reopens the same telescope with its
own fresh names. -/
theorem NestedLoweringRun.closeValidatedNestedAuxiliaries
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ClosedValidatedNestedAuxiliaries venv lparams res := by
  have hfull : mlctx.fvarRevList mlctx.length (Nat.le_refl _) =
      mlctx.vlctx.fvars := mlctx.fvarRevList_all
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [hfull, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  intro name e hfind
  rcases Hvalidated name e hfind with
    ⟨ty, e', ty', ⟨_hfvars, Hexpr, _Htype, _Htyping⟩, HisType⟩
  have Hclosed := hmlctx.mkForall_trS henv Hexpr HisType
    mlctx.length (Nat.le_refl _)
  rw [mlctx.dropN_all] at Hclosed
  have hconcrete : res.lctx.mkForall res.params e =
      mlctx.mkForall mlctx.length (Nat.le_refl _) e := by
    rw [← hlctx]
    exact hmlctx.mkForall_eq mlctx.length (Nat.le_refl _) hparams
  refine ⟨mlctx.mkForall' mlctx.length (Nat.le_refl _) e', ?_⟩
  rw [hconcrete]
  exact Hclosed

/-- Fully name-independent auxiliary semantics retained after validation:
the lowering-selected production variables are abstracted into the canonical
de-Bruijn parameter context before restoration is inspected. -/
theorem NestedLoweringRun.validatedAuxiliaryResidualTranslations
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ∃ selection : LocalForallSelection res.lctx res.params,
      ClosedNestedAuxiliaryTranslations venv lparams res selection := by
  rcases H.resultContextSelection with ⟨selection⟩
  exact ⟨selection,
    (H.closeValidatedNestedAuxiliaries henv mlctx hmlctx hlctx Hvalidated
      ).residualTranslations henv selection⟩

theorem NestedLoweringRun.resultParamsFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ e ∈ out.1.params, e.FVarsIn (· ∈ out.1.lctx.fvars) := by
  rcases H.resultContextSelection with ⟨Hselection⟩
  exact Hselection.fvarsIn H.resultContextWF

theorem NestedLoweringRun.resultAuxMap
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultAuxMap

theorem NestedLoweringRun.resultAuxFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hcache : NestedAuxFVarsIn P out.2) :
    NestedAuxMapFVarsIn P
      (show Std.TreeMap Name Expr Name.quickCmp from out.1.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapFVarsIn P
    (out.2.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_fvarsIn out.2.nestedAux.toList
  · intro entry hentry
    exact Hcache entry.1 entry.2 (by simpa using hentry)
  · unfold NestedAuxMapFVarsIn
    intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesReserved
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesWF finalState) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesReserved
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesReserved finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames.reserved entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesFresh env finalState) :
    NestedAuxMapNamesFresh env
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesFresh env
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesFresh finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.validateNestedAuxiliariesWF
    (H : NestedLoweringRun sourceEnv loweringFuel nparams sourceTypes
      initialState (res, finalState))
    (hvalid : CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (Hcache : NestedAuxFVarsIn (· ∈ mlctx.vlctx.fvars) finalState) :
    (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
      res).WF fun _ =>
        ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  apply validateNestedAuxiliaries.WF hvalid mlctx hmlctx hlctx hfresh
  intro name nested hfind
  exact H.resultAuxFVarsIn Hcache name nested hfind

/-- Under the separately stated fresh-name invariant, every final cache entry
is retrieved exactly by the production `aux2nested` map. -/
theorem NestedLoweringRun.resultAuxLookup
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ finalState.nestedAux) :
    result.aux2nested.find? name = some nested := by
  rw [H.resultAuxMap]
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[name]? = some nested
  rw [← Array.foldl_toList]
  exact nestedAuxFold_find finalState.nestedAux.toList {} hnodup
    (by simpa using hentry)

theorem NestedLoweringRun.resultAuxMapModels
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup) :
    NestedAuxMapModels result finalState := by
  intro nested name hentry
  exact H.resultAuxLookup hnodup hentry

theorem NestedLoweringRun.resultNestedAuxLE
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    NestedAuxLE initialState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _hnewTypes,
      hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultNestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hinitialAux] using hsuffix⟩

theorem NestedLoweringRun.resultNamesWF
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF initialState) : NestedAuxNamesWF out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      hinitialNext, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesWF Hindex
    (Hstate.ofCacheCounterEq hinitialAux hinitialNext)

theorem NestedLoweringRun.resultNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesFresh env initialState) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesFresh (Hstate.ofCacheEq hinitialAux)

theorem NestedLoweringRun.resultFamilyNamesFreshOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hwf : env.constants.WF)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxFamiliesFresh result env := by
  have Hnames := H.resultNamesFresh
    (NestedAuxNamesFresh.empty env initialState hempty)
  have Hmap := H.resultAuxNamesFresh Hnames
  intro name nested hfind
  exact find?_none_of_contains_false hwf (Hmap name nested hfind)

/-- End-to-end freshness bridge for restoration: lowering proves auxiliary
families fresh in the production source, and lockstep installation turns that
into abstract freshness for every constructor recognized through those
families. -/
theorem NestedLoweringRun.restoreAuxConstructorsFreshOfInstallation
    (H : NestedLoweringRun sourceProdEnv fuel nparams types initialState
      (result, finalState))
    (Hinstall : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv :=
  Hinstall.restoreAuxConstructorsFresh hwf Howners
    (H.resultFamilyNamesFreshOfEmpty hwf hempty)

theorem NestedLoweringRun.resultNamesNodupOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    (out.2.nestedAux.toList.map Prod.snd).Nodup :=
  (H.resultNamesWF Hindex (NestedAuxNamesWF.empty initialState hempty)).nodup

theorem NestedLoweringRun.resultFamilyNamesReservedOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultAuxNamesReserved
    (H.resultNamesWF Hindex (NestedAuxNamesWF.empty initialState hempty))

theorem NestedLoweringRun.resultFamilyNamesReservedFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultFamilyNamesReservedOfEmpty appendIndexAfterIndexFaithful hempty

theorem NestedLoweringRun.resultAuxMapModelsOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModels (H.resultNamesNodupOfEmpty Hindex hempty)

theorem NestedLoweringRun.resultAuxMapModelsFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModelsOfEmpty appendIndexAfterIndexFaithful hempty

/-- Positional lowering witness for any family present in the initial queue.
Unlike name preservation, this exposes the complete constructor-expression
translation performed at that family's actual dynamic queue step. -/
theorem NestedLoweringRun.translationAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveTranslation env params nparams
        initialState.newTypes[j] stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Haux⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hopening.initial_size, Htranslated, htarget, Haux⟩

/-- Once final cache-name uniqueness is supplied, every initially declared
family has a positional lowering certificate whose constructor bodies are
all interpreted by the actual final restoration map. -/
theorem NestedLoweringRun.finalMappingAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.translationAtInitial hj with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Hlater⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

/-- Parameter-aligned form of `finalMappingAtInitial`.  The expression
mapping for each source family is performed with exactly the parameter array
stored in the final restoration record, rather than merely with an array of
the same size.  This identity is what later lets restoration cancel the
abstraction performed when a nested application was cached. -/
theorem NestedLoweringRun.finalMappingAtInitialAligned
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Hlater⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hqueue.resultContext.2, Hopening.initial_size,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

theorem NestedLoweringRun.preservesInitialTypeName
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hname : NewTypeNamePresent initialState name) :
    ∃ type ∈ out.1.types, type.name = name := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, hnewTypes,
      _hnewAux, _hnextIdx, _Hctx, _Hselection, Hqueue⟩
  apply Hqueue.preservesTypeName
  unfold NewTypeNamePresent at Hname ⊢
  rwa [hnewTypes]

theorem ElimNestedInductive.run.translation
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => NestedLoweringRun env fuel nparams types state out := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesSelected
    intro lctx tail params paramsState Hopening Hctx Hselection _hnodup hnewTypes
      hnestedAux hnextIdx
    have hparams : params.size = nparams := Hopening.initial_size
    exact (loweringQueueLoop_refines env params nparams lctx 0 fuel paramsState
      hparams hclosures).mono fun _ Hqueue =>
        ⟨⟨first, rest, tail, paramsState, lctx, params,
          rfl, Hopening, hnewTypes, hnestedAux, hnextIdx, Hctx,
          ⟨Hselection⟩, Hqueue⟩⟩

/-- The final restoration parameter array is an ordered array of distinct
free variables. -/
def NestedResultParamsNodup
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ fvars : List FVarId,
    result.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup

/-- End-to-end queue safety from the executable source checks.  This closes
the dynamic-generation loop: source constructors are closed, every generated
auxiliary constructor is re-closed over the verified parameter context, and
therefore every final cache witness is open only over the retained result
context. -/
theorem ElimNestedInductive.run.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out =>
        NestedLoweringRun env fuel nparams types state out ∧
        NestedAuxFVarsIn (· ∈ out.1.lctx.fvars) out.2 ∧
        NestedResultParamsNodup out.1 := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesClosing
      (Htype := Hsources.typeClosed (by simp))
    intro lctx tail params paramsState Hopening Hclosing Htail hnewTypes
      hnestedAux hnextIdx
    have hparams : params.size = nparams := Hopening.initial_size
    have Hparams : ∀ param ∈ params,
        param.FVarsIn (· ∈ lctx.fvars) :=
      Hclosing.selection.fvarsIn Hclosing.binding.wf
    have Hpending : PendingNewTypesClosed 0 paramsState := by
      intro j _hj hj
      have hjState : j < state.newTypes.size := by
        simpa [hnewTypes] using hj
      have hvalue : paramsState.newTypes[j] = state.newTypes[j] := by
        have heq := congrArg
          (fun xs : Array InductiveType => xs[j]!) hnewTypes
        simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
      rw [hvalue]
      have hmember : state.newTypes[j] ∈ first :: rest := by
        have hmemState : state.newTypes[j] ∈ state.newTypes :=
          Array.getElem_mem hjState
        simpa [hinitial] using hmemState
      exact Hsources.constructorsClosed hmember
    have Hcache : NestedAuxFVarsIn (· ∈ lctx.fvars) paramsState := by
      intro nested name hentry
      rw [hnestedAux, hempty] at hentry
      simp at hentry
    exact (loweringQueueLoop_refinesClosed env params nparams lctx 0 fuel
      paramsState hparams hclosures Henv Hparams Hpending Hcache).mono
        fun _ Hqueue => by
          refine ⟨⟨⟨first, rest, tail, paramsState, lctx, params,
            rfl, Hopening, hnewTypes, hnestedAux, hnextIdx,
            Hclosing.binding, ⟨Hclosing.selection⟩, Hqueue.1⟩⟩, ?_, ?_⟩
          · rw [Hqueue.1.resultContext.1]
            exact Hqueue.2
          · exact ⟨Hclosing.selection.fvars,
              Hqueue.1.resultContext.2.trans Hclosing.selection.expressions,
              Hclosing.nodup⟩

/-- Exact state transition for one iteration of the dynamic lowering queue.
The successful case retains the source family selected before lowering, while
allowing `lowerInductive` to append freshly discovered auxiliary families
before the selected slot is overwritten. -/
inductive LowerNextResult (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType → Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextResult params nparams i state none state
  | step {target : InductiveType}
      {loweredState : Lean4Lean.ElimNestedInductive.State}
      (hidx : i < state.newTypes.size)
      (shape : LoweredInductiveShape nparams state.newTypes[i] target) :
      LowerNextResult params nparams i state (some state.newTypes[i])
        { loweredState with
          newTypes := loweredState.newTypes.set! i target }

theorem ElimNestedInductive.lowerNext.refines
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextResult params nparams i state out.1 out.2 := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.lowerNext at hout
  simp only [get, bind, StateT.bind, ReaderT.bind, pure] at hout
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M
        Lean4Lean.ElimNestedInductive.State) env state) =
      Except.ok (state, state) := rfl
  rw [hget] at hout
  simp only [Except.bind] at hout
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx] at hout
    change ((Lean4Lean.ElimNestedInductive.lowerInductive
      params nparams state.newTypes[i] env state).bind fun lowered =>
        Except.ok (some state.newTypes[i],
          { lowered.2 with
            newTypes := lowered.2.newTypes.set! i lowered.1 })) =
      Except.ok out at hout
    cases hlower : Lean4Lean.ElimNestedInductive.lowerInductive
        params nparams state.newTypes[i] env state with
    | error err =>
      rw [hlower] at hout
      contradiction
    | ok lowered =>
      rw [hlower] at hout
      simp at hout
      cases hout
      exact .step hidx
        (ElimNestedInductive.lowerInductive.shape
          params nparams state.newTypes[i] env state lowered hlower)
  · rw [dif_neg hidx] at hout
    cases hout
    exact .done (Nat.le_of_not_gt hidx)

/-- The first branch of nested lowering rejects an empty source block. This
is the operational origin of the nonemptiness premise later used to recover
`SourceWF` from `TrInductDeclCore`. -/
theorem ElimNestedInductive.run.source_nonempty
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun _ => types ≠ [] := by
  intro out hout
  cases types with
  | nil =>
    change Except.error _ = Except.ok out at hout
    contradiction
  | cons type types =>
    simp

/-- A successful lowering run carries the exact common-parameter opening of
the first source header into the restoration data returned in `Result`. -/
theorem ElimNestedInductive.run.parameterOpening
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => ∃ first rest tail,
        types = first :: rest ∧
        NestedParamOpening {} #[] first.type nparams
          out.1.lctx tail out.1.params ∧
        out.1.nparams = nparams := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refines
    intro lctx tail params outState Hopening
    have loopWF : ∀ remaining i currentState,
        (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i
          remaining env currentState).WF fun out => ∃ first' rest' tail',
            first :: rest = first' :: rest' ∧
            NestedParamOpening {} #[] first'.type nparams
              out.1.lctx tail' out.1.params ∧
            out.1.nparams = nparams := by
      intro remaining
      induction remaining with
      | zero => intro i currentState; exact Except.WF.throw
      | succ remaining ih =>
        intro i currentState
        simp only [Lean4Lean.ElimNestedInductive.run.loop]
        exact (ElimNestedInductive.lowerNext.refines
          params nparams i env currentState).bind fun next Hnext => by
            rcases next with ⟨next, nextState⟩
            cases Hnext with
            | done hbound =>
              exact Except.WF.pure ⟨first, rest, tail, rfl, Hopening,
                Hopening.initial_size⟩
            | step hidx Hshape =>
              exact ih (i + 1) _
    exact loopWF fuel 0 outState

/-- Projection of the complete lowering trace through the `StateT.run'` used
by `Environment.addInductive`. -/
def NestedLoweringResult
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState, NestedLoweringRun env fuel nparams types initialState
    (result, finalState)

/-- Lowering result with the dynamic-queue closure argument discharged.  The
final cache predicate is stated against the exact local context returned in
the executable restoration record. -/
def NestedLoweringResultClosed
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState,
    NestedLoweringRun env fuel nparams types initialState
      (result, finalState) ∧
    NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState ∧
    NestedResultParamsNodup result

/-- Closed lowering scopes every auxiliary witness by any retained
binder-order selection of the result parameters. -/
theorem NestedLoweringResultClosed.auxFVarsInSelection
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params) :
    ∀ name e, result.aux2nested.find? name = some e →
      e.FVarsIn (· ∈ selection.fvars) := by
  rcases H with ⟨finalState, Hrun, Hcache, _Hparams⟩
  have Hmap := Hrun.resultAuxFVarsIn Hcache
  have hcontext := Hrun.resultSelection_reverse_fvars selection
  intro name e hfind
  exact (Hmap name e hfind).mono fun fv hfv => by
    rw [← hcontext] at hfv
    exact List.mem_reverse.mp hfv

/-- Canonical semantic interpretation of the head expression inserted by an
auxiliary-family restoration hit, after restoration's fresh parameters are
closed again.  Both its parameter arity and its translation follow from the
validated auxiliary certificate; no concrete free-variable identity remains. -/
theorem NestedLoweringResultClosed.auxiliaryRestorationHeadTranslation
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection)
    (name : Name) (e : Expr)
    (hfind : result.aux2nested.find? name = some e)
    (restoreSelection : LocalForallSelection restoreLctx restoreAs)
    (hrestoreNodup : restoreSelection.fvars.Nodup) :
    ∃ domains target,
      domains.length = result.params.size ∧
      TrExprS venv lparams (abstractForallContext domains [])
        (((e.abstract result.params).instantiateRev restoreAs).abstract
          restoreAs) target ∧
      venv.IsType lparams.length
        (abstractForallContext domains []).toCtx target := by
  rcases Htranslations name e hfind with ⟨Haux⟩
  have Hscope := H.auxFVarsInSelection selection name e hfind
  have halpha := Haux.restorationAlpha Hscope restoreSelection hrestoreNodup
  refine ⟨Haux.domains, Haux.residualTarget, Haux.arity, ?_,
    Haux.residualType⟩
  rw [halpha]
  exact Haux.residual

theorem NestedLoweringResultClosed.toResult
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    NestedLoweringResult env fuel nparams types initialState result := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact ⟨finalState, Hrun⟩

theorem NestedLoweringResultClosed.resultParamsNodup
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    NestedResultParamsNodup result := by
  rcases H with ⟨_finalState, _Hrun, _Hcache, Hparams⟩
  exact Hparams

theorem NestedLoweringResultClosed.selectionNodup
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params) :
    selection.fvars.Nodup := by
  rcases H.resultParamsNodup with ⟨fvars, hparams, hnodup⟩
  have harrays : (selection.fvars.map Expr.fvar).toArray =
      (fvars.map Expr.fvar).toArray := by
    rw [← selection.expressions, ← hparams]
  have hlists : selection.fvars.map Expr.fvar =
      fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harrays
  have heq : selection.fvars = fvars :=
    (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  rw [heq]
  exact hnodup

theorem NestedLoweringResultClosed.resultParamsSize
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    result.params.size = result.nparams := by
  rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.resultParamsSize.trans Hrun.resultNParams.symm

/-- Actual operational restoration openings satisfy the arbitrary-depth
alpha law for every validated auxiliary hit. -/
theorem NestedRestorationOpening.auxiliaryAlphaAt
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (k : Nat) :
    ((e.abstract result.params).instantiateRev Hopen.params).abstractList
        Hopen.selection.fvars k =
      e.abstractList selection.fvars k := by
  have Hscope := Hlower.auxFVarsInSelection selection name e hfind
  have hsize : Hopen.selection.fvars.length = selection.fvars.length := by
    rw [Hopen.selectionLength, ← selection.size]
  exact Haux.restorationAlphaAt Hscope (Hlower.selectionNodup selection)
    Hopen.selection Hopen.selectionNodup hsize k

/-- A concrete family head inserted by operational restoration has the
validated auxiliary translation in the abstract context extended by the
recursor binders beneath which the hit occurs. -/
theorem NestedRestorationOpening.auxiliaryTranslationUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
      (abstractForallContext suffixDomains
        (abstractForallContext Haux.domains []))
      (((e.abstract result.params).instantiateRev Hopen.params).abstractList
        Hopen.selection.fvars suffixDomains.length)
      (Haux.residualTarget.liftN suffixDomains.length 0) := by
  rw [Hopen.auxiliaryAlphaAt Hlower selection Haux name hfind
    suffixDomains.length]
  exact Haux.residualUnder henv (Hlower.selectionNodup selection)
    suffixDomains

/-- Typed form of `auxiliaryTranslationUnder`, packaging the translation and
the abstract domain-type proof needed by the enclosing restored telescope. -/
theorem NestedRestorationOpening.auxiliaryTypedUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains []))
        (((e.abstract result.params).instantiateRev Hopen.params).abstractList
          Hopen.selection.fvars suffixDomains.length)
        (Haux.residualTarget.liftN suffixDomains.length 0) ∧
      venv.IsType lparams.length
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains [])).toCtx
        (Haux.residualTarget.liftN suffixDomains.length 0) := by
  exact ⟨Hopen.auxiliaryTranslationUnder Hlower selection Haux henv name
    hfind suffixDomains, Haux.residualTypeUnder henv suffixDomains⟩

/-- Interpret a complete restoration hit on an auxiliary-family application
which has exactly the common-parameter arguments.  The executable output is
identified with the validated reopened witness, then translated and typed in
the exact current suffix context. -/
theorem NestedRestorationOpening.exactFamilyHitTypedUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains []))
        (restored.abstractList Hopen.selection.fvars suffixDomains.length)
        (Haux.residualTarget.liftN suffixDomains.length 0) ∧
      venv.IsType lparams.length
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains [])).toCtx
        (Haux.residualTarget.liftN suffixDomains.length 0) := by
  have Hexact := restoreNestedNode_family_exactParams result prodEnv
    Hopen.params auxRec t e family levels hhead hrec hfind hargs
  have hrestored : restored =
      (e.abstract result.params).instantiateRev Hopen.params :=
    Option.some.inj (Hhit.symm.trans Hexact)
  subst restored
  exact Hopen.auxiliaryTypedUnder Hlower selection Haux henv family hfind
    suffixDomains

theorem NestedRestorationOpening.exactFamilyHitAbstractTypeTranslation
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext suffixDomains
        (abstractForallContext Haux.domains []))
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  rcases Hopen.exactFamilyHitTypedUnder Hlower selection Haux henv family
      levels hfind hrec t restored hhead hargs Hhit suffixDomains with
    ⟨Htr, Htype⟩
  exact ⟨_, Htr, Htype⟩

/-- Context-normalized form of the exact-family interpreter.  The semantic
common-parameter domains are the initial prefix of the restored recursor;
`suffixDomains` are precisely the binders already traversed by the suffix
telescope fold. -/
theorem NestedRestorationOpening.exactFamilyHitAbstractTypeTranslationAtPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext (Haux.domains ++ suffixDomains) [])
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  simpa only [abstractForallContext_append] using
    Hopen.exactFamilyHitAbstractTypeTranslation Hlower selection Haux henv
      family levels hfind hrec t restored hhead hargs Hhit suffixDomains

/-- Lookup-driven form used by a recursor-domain callback.  Validation of all
cached auxiliaries supplies the particular closed translation selected by the
same `aux2nested` lookup that triggered the executable restoration hit. -/
theorem NestedRestorationOpening.exactFamilyHitOfTranslationsAtPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level) (e : Expr)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    ∃ parameterDomains,
      parameterDomains.length = result.params.size ∧
      Expr.AbstractTypeTranslation venv lparams
        (abstractForallContext (parameterDomains ++ suffixDomains) [])
        (restored.abstractList Hopen.selection.fvars
          suffixDomains.length) := by
  rcases Htranslations family e hfind with ⟨Haux⟩
  exact ⟨Haux.domains, Haux.arity,
    Hopen.exactFamilyHitAbstractTypeTranslationAtPrefix Hlower selection Haux
      henv family levels hfind hrec t restored hhead hargs Hhit
      suffixDomains⟩

theorem NestedLoweringResultClosed.validateNestedAuxiliariesWF
    (H : NestedLoweringResultClosed sourceEnv loweringFuel nparams sourceTypes
      initialState res)
    (hvalid : CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
      res).WF fun _ =>
        ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  rcases H with ⟨finalState, Hrun, Hcache, _Hparams⟩
  apply Hrun.validateNestedAuxiliariesWF hvalid mlctx hmlctx hlctx hfresh
  have hfvars : res.lctx.fvars = mlctx.vlctx.fvars := by
    rw [← hlctx, hmlctx.tr.fvars_eq]
  intro nested name hentry
  simpa [hfvars] using Hcache nested name hentry

theorem NestedLoweringResult.resultRestorable
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∀ type ∈ result.types, RestorableInductiveType nparams type := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultRestorable

theorem NestedLoweringResult.resultNParams
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    result.nparams = nparams := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultNParams

theorem NestedLoweringResult.resultAuxMap
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      result.aux2nested = finalState.nestedAux.foldl
        (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H with ⟨finalState, Hrun⟩
  exact ⟨finalState, Hrun, Hrun.resultAuxMap⟩

theorem NestedLoweringResult.resultNestedAuxLE
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      NestedAuxLE initialState finalState := by
  rcases H with ⟨finalState, Hrun⟩
  exact ⟨finalState, Hrun, Hrun.resultNestedAuxLE⟩

theorem NestedLoweringResult.sourceTranslationAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveTranslation env params nparams sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target ∧
      ∃ finalState,
        NestedLoweringRun env fuel nparams sourceTypes
          { initialState with newTypes := sourceTypes.toArray }
          (result, finalState) ∧
        NestedAuxLE loweredState finalState := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.translationAtInitial hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Haux⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Htranslated, htarget, finalState, Hrun, Haux⟩

/-- End-to-end source-family mapping, with the one still-unproved production
fresh-name obligation exposed at the final cache boundary rather than hidden
inside the semantic certificate. -/
theorem NestedLoweringResult.sourceFinalMappingAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ((finalState.nestedAux.toList.map Prod.snd).Nodup →
        ∃ params stepState target loweredState,
          params.size = nparams ∧
          LoweredInductiveMapping env params nparams result sourceTypes[j]
            stepState (target, loweredState) ∧
          result.types[j]? = some target) := by
  rcases H with ⟨finalState, Hrun⟩
  refine ⟨finalState, Hrun, ?_⟩
  intro hauxNames
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.finalMappingAtInitial hauxNames hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Hmapped, htarget⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Hmapped, htarget⟩

/-- The source-family mapping with cache uniqueness discharged from the empty
production cache and the isolated suffix-index primitive law. -/
theorem NestedLoweringResult.sourceFinalMappingAtOfIndexFaithful
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.sourceFinalMappingAt hj with ⟨finalState, Hrun, Hmapped⟩
  apply Hmapped
  apply Hrun.resultNamesNodupOfEmpty Hindex
  simpa using hempty

theorem NestedLoweringResult.sourceFinalMappingAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target :=
  H.sourceFinalMappingAtOfIndexFaithful appendIndexAfterIndexFaithful hempty hj

/-- Fresh-cache source mapping with the lowering parameters identified with
the parameters retained by the production restoration record. -/
theorem NestedLoweringResult.sourceFinalMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  apply Hrun.finalMappingAtInitialAligned _ hjInitial
  apply Hrun.resultNamesNodupOfEmpty appendIndexAfterIndexFaithful
  simpa using hempty

/-- Every original family retains its positional slot in the expanded
lowering result, so the original mutual block is no longer than that result. -/
theorem NestedLoweringResult.sourceTypes_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    sourceTypes.length ≤ result.types.length := by
  by_contra hle
  have hj : result.types.length < sourceTypes.length := Nat.lt_of_not_ge hle
  rcases H.sourceTranslationAt (j := result.types.length) hj with
    ⟨_params, _stepState, _target, _loweredState, _hparams, _Htranslation,
      htarget, _finalState, _Hrun, _Haux⟩
  exact (Nat.lt_irrefl result.types.length)
    (_root_.getElem?_eq_some_iff.mp htarget).1

/-- Lowering preserves the constructor count of every original family and
only appends auxiliary families.  Consequently the source constructor batch
is a cardinality prefix of the expanded lowered batch. -/
theorem NestedLoweringResult.sourceOwnedConstructors_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[]) :
    (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length ≤
      (Lean4Lean.VerifyInductive.ownedConstructors result.types).length := by
  have htypes := H.sourceTypes_length_le
  have hprefix :
      (result.types.take sourceTypes.length).map
          (fun type => type.ctors.length) =
        sourceTypes.map (fun type => type.ctors.length) := by
    apply List.ext_getElem
    · simp [List.length_take, htypes]
    · intro i hresult hsource
      rw [List.getElem_map, List.getElem_take, List.getElem_map]
      rcases H.sourceFinalMappingAtFresh hempty (j := i) (by simpa using hsource)
          with ⟨_params, _stepState, target, _loweredState, _hparams,
            Hmapping, htarget⟩
      obtain ⟨hiResult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
      rw [htargetEq]
      exact Hmapping.constructors.length
  have hsplit := congrArg
    (fun types : List InductiveType =>
      (types.map (fun type => type.ctors.length)).sum)
    (List.take_append_drop sourceTypes.length result.types)
  simp only [List.map_append, List.sum_append] at hsplit
  rw [hprefix] at hsplit
  simp only [Lean4Lean.VerifyInductive.ownedConstructors,
    List.length_flatMap, List.length_map]
  omega

/-- Transport an installed lowered recursor shape to its original source
family.  Lowering and the two declaration translations discharge owner/name,
universe, parameter, and prefix-cardinality compatibility; only equality of
the independently recovered source/lowered index counts remains explicit. -/
theorem VInductDecl.NestedRecursorShape.toSourceOfLowering
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Hexpanded : TrInductDeclCore expandedVEnv lparams nparams result.types
      isUnsafe loweredDecl expandedEnvTypes expandedEnvCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hsourceDecl : familyIdx < sourceDecl.types.length)
    (hloweredDecl : familyIdx < loweredDecl.types.length)
    {recursor : VConstVal}
    (Hshape : loweredDecl.NestedRecursorShape
      (loweredDecl.types[familyIdx]'hloweredDecl) recursor)
    (hindices : (sourceDecl.types[familyIdx]'hsourceDecl).numIndices =
      (loweredDecl.types[familyIdx]'hloweredDecl).numIndices) :
    Nonempty (sourceDecl.NestedRecursorShape
      (sourceDecl.types[familyIdx]'hsourceDecl) recursor) := by
  rcases Hlower.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_params, _stepState, target, _loweredState, _hparams, Hmapping,
      htarget⟩
  obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HexpandedType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hexpanded familyIdx hresult hloweredDecl
  have hloweredOwnerName :
      (loweredDecl.types[familyIdx]'hloweredDecl).name =
        sourceTypes[familyIdx].name := by
    exact HexpandedType.header.name.trans <| by
      simpa [htargetEq] using Hmapping.name
  have hsourceOwnerName :
      (sourceDecl.types[familyIdx]'hsourceDecl).name =
        sourceTypes[familyIdx].name := HsourceType.header.name
  have hshapeIdx : Hshape.ownerIdx = familyIdx := by
    exact Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
      Hshape familyIdx hloweredDecl Hshape.name
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup Hexpanded)
  refine ⟨Hshape.ofCompatible ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [hshapeIdx] using hsourceDecl
  · simpa [hshapeIdx]
  · rw [Hshape.name]
    simp only [VInductDecl.recursorName_eq_mkRecName]
    exact congrArg Lean.mkRecName (hloweredOwnerName.trans hsourceOwnerName.symm)
  · have huvars := Hshape.uvars
    rw [Hexpanded.uvars] at huvars
    rw [Hsource.uvars]
    exact huvars
  · exact Hsource.nparams.trans Hexpanded.nparams.symm
  · calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlower.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hexpanded
      _ ≤ Hshape.motives.length := Hshape.source_motives
  · calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        Hlower.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hexpanded
      _ ≤ Hshape.minors.length := Hshape.source_minors
  · exact hindices

/-- Closed-lowering specialization of the aligned source mapping.  It
exposes the exact duplicate-free free-variable presentation of the final
parameter array needed by abstraction/instantiation cancellation. -/
theorem NestedLoweringResultClosed.sourceFinalMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      LoweredInductiveMapping env result.params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.resultParamsNodup with ⟨fvars, hresultParams, hnodup⟩
  rcases H.toResult.sourceFinalMappingAtFreshAligned hempty hj with
    ⟨params, stepState, target, loweredState, hparams, hsize,
      Hmapping, htarget⟩
  rw [← hparams] at Hmapping
  exact ⟨fvars, stepState, target, loweredState, hresultParams, hnodup,
    by simpa [hparams] using hsize, Hmapping, htarget⟩

/-- Original family headers need no semantic restoration: lowering preserves
them verbatim, so the positional translation proved for the lowered block is
already the independently checked translation of the corresponding source
header.  This theorem deliberately uses the list position fixed by the
lowering trace, rather than recovering the owner by name. -/
theorem NestedLoweringResultClosed.sourceHeaderTranslationAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hcore : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe decl envTypes envCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hdecl : familyIdx < decl.types.length,
      TrSourceConst sourceVEnv lparams sourceTypes[familyIdx].name
        sourceTypes[familyIdx].type
        (decl.types[familyIdx]'hdecl).toVConstVal := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hsourceCore, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hdecl : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hcore]
    exact hsourceCore
  have Hheader :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hcore familyIdx
      hsourceCore hdecl).header
  refine ⟨hdecl, ?_⟩
  rw [← Hmapping.name, ← Hmapping.type]
  simpa [htargetEq] using Hheader

/-- End-to-end positional constructor mapping for an original source family.
This is the alignment consumed by restoration: it identifies the exact
lowered constructor at the same family and constructor indices while retaining
the final parameter presentation needed by the expression inverse. -/
theorem NestedLoweringResultClosed.sourceConstructorMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx ctorIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hctor : ctorIdx < sourceTypes[familyIdx].ctors.length) :
    ∃ fvars : List FVarId, ∃ target sourceCtor targetCtor before after,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      SourceConstructorSyntax sourceTypes[familyIdx].ctors[ctorIdx] ∧
      sourceTypes[familyIdx].ctors[ctorIdx]? = some sourceCtor ∧
      target.ctors[ctorIdx]? = some targetCtor ∧
      LoweredConstructorMapping env result.params nparams result sourceCtor
        before (targetCtor, after) ∧
      result.types[familyIdx]? = some target := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      Hmapping, htarget⟩
  rcases Hmapping.constructors.mappingAt ctorIdx hctor with
    ⟨sourceCtor, targetCtor, before, after, hsourceCtor, htargetCtor,
      HctorMapping⟩
  exact ⟨fvars, target, sourceCtor, targetCtor, before, after, hparams,
    hnodup, hsize,
    (Hsources.getElem familyIdx hfamily).constructors.getElem ctorIdx hctor,
    hsourceCtor, htargetCtor, HctorMapping, htarget⟩

/-- End-to-end alignment of one original source family's lowering with the
exact constructor-restoration fold selected by production.  All concrete
`oldInfo.type = lowered.type` facts are consequences of the verified lowered
installation; the returned certificate retains only the genuinely semantic
source-to-abstract constructor work for the next layer. -/
theorem NestedLoweringResultClosed.sourceConstructorRestorationTraceAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      result.types[familyIdx]? = some target ∧
      Hstep.oldInfo.ctors = target.ctors.map (fun ctor => ctor.name) ∧
      ∃ Hmappings : LoweredConstructorMappings loweredSourceEnv result.params
          nparams result sourceTypes[familyIdx].ctors stepState
            (target.ctors, loweredState),
        ∃ Htrace : StateForMTrace
          (RestoredConstructorStep result loweredEnv)
          (target.ctors.map (fun ctor => ctor.name))
          Hstep.restored.headerEnv Hstep.restored.constructorEnv,
          RestoredConstructorMappingTrace result loweredSourceEnv loweredEnv
            result.params nparams c.safety c.lparams
              sourceTypes[familyIdx].ctors stepState target.ctors loweredState
              Hstep.restored.headerEnv Hstep.restored.constructorEnv := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      Hmapping, htarget⟩
  have htargetMem : target ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? htarget
  have hctorNames : Hstep.oldInfo.ctors =
      target.ctors.map (fun ctor => ctor.name) :=
    Hstep.oldConstructors_eq_ofInstalled Hc Hprod htargetMem
      Hmapping.name.symm
  have Htrace : StateForMTrace
      (RestoredConstructorStep result loweredEnv)
      (target.ctors.map (fun ctor => ctor.name)) Hstep.restored.headerEnv
        Hstep.restored.constructorEnv := by
    rw [← hctorNames]
    exact Hstep.restored.constructors
  have Haligned := RestoredConstructorMappingTrace.ofInstalled Hprod
    htargetMem Hmapping.constructors Htrace (by
      intro targetCtor htargetCtor
      exact htargetCtor)
  exact ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
    htarget, hctorNames, Hmapping.constructors, Htrace, Haligned⟩

/-- Production restoration never renames the primary recursor of an
original mutual-family member.  Original families occupy positions strictly
before the auxiliary suffix from which `mkAuxRecNameMap` is built, and the
installed mutual-family metadata proves that these positions are distinct. -/
theorem NestedLoweringResultClosed.sourceRecursorUnmappedAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name) = none := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, hinitialAux, hinitialNext, Hctx, Hselection, Hqueue⟩
  subst sourceTypes
  have Hclosed : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hclosed.sourceFinalMappingAtFreshAligned hempty (j := 0) (by simp) with
    ⟨_mainFVars, _mainState, mainTarget, _mainLoweredState, _mainParams,
      _mainNodup, _mainSize, Hmain, hmainTarget⟩
  have hmainMem : mainTarget ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? hmainTarget
  rcases Hprod.findSourceHeader Hc hmainMem with
    ⟨mainInfo, hmainFind, _hmainCtors, hall⟩
  have hmainFind' :
      loweredEnv.find? main.name = some (.inductInfo mainInfo) := by
    have hmainName : mainTarget.name = main.name := by
      simpa using Hmain.name
    rw [← hmainName]
    exact hmainFind
  apply mkAuxRecNameMap_recMap_find_none main rest loweredEnv mainInfo
    hmainFind'
  intro hquery
  rcases List.mem_map.mp hquery with ⟨suffixName, hsuffix, hrecName⟩
  have hsuffixName : suffixName = (main :: rest)[familyIdx].name :=
    mkRecName_injective (hrecName.trans rfl)
  rcases List.mem_drop_iff_getElem.mp hsuffix with
    ⟨suffixIdx, hsuffixBound, hsuffixGet⟩
  rcases Hclosed.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_familyFVars, _familyState, familyTarget, _familyLoweredState,
      _familyParams, _familyNodup, _familySize, Hfamily, hfamilyTarget⟩
  have hfamilyInfo : mainInfo.all[familyIdx]? =
      some (main :: rest)[familyIdx].name := by
    rw [hall]
    rw [List.getElem?_map, hfamilyTarget]
    simp only [Option.map_some, Option.some.injEq]
    exact Hfamily.name
  have hsuffixInfo :
      mainInfo.all[(main :: rest).length + suffixIdx]? =
        some (main :: rest)[familyIdx].name := by
    exact _root_.getElem?_eq_some_iff.mpr
      ⟨by omega, hsuffixGet.trans hsuffixName⟩
  have hfamilyResultBound : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp hfamilyTarget).1
  have hindexEq : familyIdx = (main :: rest).length + suffixIdx :=
    (List.getElem?_inj (l := mainInfo.all)
      (i := familyIdx) (j := (main :: rest).length + suffixIdx)
      (by simpa [hall] using hfamilyResultBound)
      (Hprod.closed main.name mainInfo hmainFind').names).mp
      (hfamilyInfo.trans hsuffixInfo.symm)
  omega

/-- Interpret one source family's exact constructor-restoration fold using
the independently checked source constructor translations.  Fresh generated
names turn the syntactic no-auxiliary condition into the semantic
disjointness required by the lowering/restoration inverse. -/
theorem NestedLoweringResultClosed.sourceConstructorSemanticsAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hfamily : familyIdx < sourceTypes.length)
    (Htranslations : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors constructors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv canonicalEnv)
    (hempty : initialState.nestedAux = #[])
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    RestoredSourceConstructorTrace c.lparams c.safety canonicalEnv
      Hstep.oldInfo.ctors Hstep.restored.headerEnv
        Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors
          constructors := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, _hsize,
      htarget, hctorNames, Hmappings, Htrace, Haligned⟩
  have Hsyntax := (Hsources.getElem familyIdx hfamily).constructors
  have Hsemantic := Haligned.sourceSemantics Htranslations Hsyntax (by
    intro source hsource
    have HsourceTranslation :=
      Lean4Lean.List.Forall₂.forall_exists_l Htranslations source hsource
    rcases HsourceTranslation with ⟨constructor, _hconstructor, Hsource⟩
    exact (Hsyntax.of_mem hsource).noNestedAux
      |>.restoreSourceDisjointOfFresh Hsource.type.constantsDefined Hfamilies
        Hconstructors) rfl fvars hparams hnodup H.toResult.resultNParams
  simpa [hctorNames] using Hsemantic

/-- Realize one restored primary recursor from the one irreducibly semantic
fact about it: translation of its restored concrete type in the canonical
source environment. Source translation, shared metadata materialization,
lowering, and the generated recursor certificate determine every remaining
name, universe, and telescope-cardinality premise. -/
theorem NestedLoweringResultClosed.sourcePrimaryRecursorRealizationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : TrExprS envCtors Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
      recursor) := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by
    simpa using hresultIdx
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    simpa [Hprod.cardinality.records] using hrecInfo
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hindices : (sourceDecl.types[familyIdx]'hdecl).numIndices =
      Hprod.recInfos[familyIdx]!.indices.size := by
    exact (Hmetadata.numIndices hdeclLength familyIdx hdecl hloweredDecl).trans
      (Hprod.cardinality.indices familyIdx hrecInfo).symm
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [Array.getElem!_eq_getD, Array.getD, howner, hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name :=
    congrArg Lean.mkRecName hsourceName.symm
  let recursor : VConstVal := {
    name := sourceDecl.recursorName (sourceDecl.types[familyIdx]'hdecl)
    uvars := Hstep.restored.recursor.oldInfo.levelParams.length
    type := targetType }
  have huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1 := by
    exact Hprod.restoredPrimaryRecursorUvars familyIdx hentry
      Hstep.restored.recursor holdRecName sourceDecl Hsource.uvars
  have hmotives : sourceDecl.types.length ≤
      (Hprod.recInfos.map (·.motive)).size := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = Hprod.recInfos.size := Hprod.cardinality.records.symm
      _ = (Hprod.recInfos.map (·.motive)).size := by simp
  have hminors : sourceDecl.ownedConstructors.length ≤
      (Hprod.recInfos.flatMap (·.minors)).size := by
    calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        H.toResult.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          R.core
      _ = (Hprod.recInfos.flatMap (·.minors)).size :=
        Hprod.cardinality.minors.symm
  refine ⟨recursor, ⟨Hprod.restoredSourcePrimaryRecursorRealization
    familyIdx hentry Hstep.restored.recursor holdRecName sourceDecl hdecl
    recursor envCtors rfl huvars rfl H.toResult.resultNParams
    (Hsource.nparams.trans H.toResult.resultNParams.symm) hmotives hminors
    hindices ?_⟩⟩
  simpa [recursor] using Htype

/-- Binder-explicit form of `sourcePrimaryRecursorRealizationAtFresh`.
This is the preferred boundary for the pending nested-restoration transport:
the caller must provide the exact typed restored telescope, rather than an
opaque translation of the whole expression. -/
theorem NestedLoweringResultClosed.sourcePrimaryRecursorRealizationAtFreshOfTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
      recursor) :=
  H.sourcePrimaryRecursorRealizationAtFresh Hprod Hsource Hmetadata hempty
    familyIdx hfamily hdecl hentry Hstep targetType Htype.translation

/-- Package one original family into the payload consumed by whole-mutual
semantic-trace assembly.  Header and constructor semantics come from the
independent source translation. The source-recursion payload is explicitly
indexed by the original declaration, while the installed expanded declaration
is used only to recover production safety metadata and name preservation. -/
theorem NestedLoweringResultClosed.sourceInductiveSemanticsAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hsource : TrInductiveType sourceVEnv envTypes c.lparams
      sourceTypes[familyIdx] (sourceDecl.types[familyIdx]'hdecl))
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (HsourceRec : SourcePrimaryRecursorSemantics sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) envCtors)
    (Hrefine : RestoredPrimaryRecursorRefinement Hstep.restored.recursor
      envCtors HsourceRec.recursor) :
    Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams c.safety
      sourceVEnv envTypes envCtors Hstep) := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by simpa using hresultIdx
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [Array.getElem!_eq_getD, Array.getD, howner, hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have HctorSemantics := H.sourceConstructorSemanticsAtFresh Hc Hprod
    Hsources hfamily Hsource.ctors Hfamilies Hconstructors hempty Hstep
  have hrestoredName : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName sourceTypes[familyIdx].name := by
    have hunmapped := H.sourceRecursorUnmappedAtFresh Hc Hprod hempty
      familyIdx hfamily
    rw [Hstep.restored.recursor.restored.mappedName]
    apply Std.TreeMap.getD_eq_fallback_of_contains_eq_false
    change Std.TreeMap.contains
      (show Std.TreeMap Name Name Name.quickCmp from
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
        (Lean.mkRecName sourceTypes[familyIdx].name) = false
    rw [Std.TreeMap.contains_eq_isSome_getElem?]
    change ((Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name)).isSome = false
    rw [hunmapped]
    rfl
  have Hmetadata := Hprod.restoredPrimaryRecursorMetadata familyIdx hentry
    Hstep.restored.recursor (congrArg Lean.mkRecName hsourceName.symm)
  have hownerName : (sourceDecl.types[familyIdx]'hdecl).name =
      sourceTypes[familyIdx].name := by
    simpa using Hsource.header.name
  have HrecName : HsourceRec.recursor.name =
      Hstep.restored.recursor.restored.newRecName := by
    exact HsourceRec.name.trans <| by
      simpa only [VInductDecl.recursorName_eq_mkRecName] using
        (congrArg Lean.mkRecName hownerName).trans hrestoredName.symm
  have HrecWF : HsourceRec.recursor.toVConstant.WF envCtors := by
    exact HsourceRec.isType
  have HrecSemantics : RestoredPrimaryRecursorSemantics sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) c.safety
      Hstep.restored.recursor envCtors := {
    recursor := HsourceRec.recursor
    safety_le := Hmetadata.1
    uvars := Hrefine.uvars
    type := Hrefine.type
    name := HrecName
    wf := HrecWF
    shape := HsourceRec.shape }
  exact ⟨{
    owner := sourceDecl.types[familyIdx]'hdecl
    header := Hsource.header
    constructors := HctorSemantics
    recursor := HrecSemantics }⟩

/-- Assemble the independent source declaration semantics over the exact
production mutual-restoration trace. The lowered and source declarations are
separate indices, which is essential when nested lowering appends auxiliary
families. The two per-family inputs expose the precise verification boundary:
independent source-recursion semantics and executable-to-source refinement.
Headers, constructors, production metadata, and all list/state ordering are
derived here. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HsourceRecursors : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (_hentry : familyIdx < Hprod.entries.length),
      Nonempty (SourcePrimaryRecursorSemantics sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) envCtors))
    (HrecursorRefinements : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget)
      (HsourceRec : SourcePrimaryRecursorSemantics sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) envCtors),
      RestoredPrimaryRecursorRefinement Hstep.restored.recursor envCtors
        HsourceRec.recursor) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety sourceVEnv
        envTypes envCtors Hrestored.inductives owners recursors := by
  apply Hrestored.inductives.sourceInductiveSemanticTrace
  intro indType stepSource stepTarget Hstep hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases HsourceRecursors familyIdx hfamily hdecl hentry with
    ⟨HsourceRec⟩
  exact H.sourceInductiveSemanticsAtFresh Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hdecl) Hfamilies Hconstructors Hstep
    HsourceRec
    (HrecursorRefinements familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep HsourceRec)

/-- Joint recursor-realization form of `sourceSemanticTraceAtFresh`.  This is
the preferred executable/specification boundary: each operational restoration
step must produce one source semantic witness together with a refinement of
that very same recursor, rather than satisfying two independently quantified
callbacks. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfRealizations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (Hrealizations : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
        recursor)) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply Hrestored.inductives.sourceInductiveSemanticTrace
  intro indType stepSource stepTarget Hstep hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases Hrealizations familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨recursor, ⟨Hrealization⟩⟩
  have Hrefinement := Hrealization.refinement
  rw [← Hrealization.recursor_eq] at Hrefinement
  exact H.sourceInductiveSemanticsAtFresh Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hdecl) Hfamilies Hconstructors Hstep
    Hrealization.source Hrefinement

/-- Whole-mutual source semantics with the callback surface reduced to the
canonical translation of each restored concrete primary-recursor type.
Source/lowered index arities are derived once from their shared materialized
metadata prefix; every other realization field follows from the verified
lowering and recursor phases. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfTranslatedTypes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtranslatedTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType,
        TrExprS envCtors Hstep.restored.recursor.oldInfo.levelParams []
          Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply H.sourceSemanticTraceAtFreshOfRealizations Hc Hprod Hsources Hsource
    Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  rcases HtranslatedTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htype⟩
  exact H.sourcePrimaryRecursorRealizationAtFresh Hprod Hsource Hmetadata
    hempty familyIdx hfamily hdecl hentry Hstep targetType Htype

/-- Preferred whole-mutual boundary for canonical restored recursor typing.
The remaining family-wise obligation is decomposed at every forall binder and
already includes typehood of every domain and the final result. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtelescopeTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
        Hstep.restored.recursor.oldInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.type
        (result.nparams + (Hprod.recInfos.map (·.motive)).size +
          (Hprod.recInfos.flatMap (·.minors)).size +
          Hprod.recInfos[familyIdx]!.indices.size + 1)
        targetType) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply H.sourceSemanticTraceAtFreshOfRealizations Hc Hprod Hsources Hsource
    Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  rcases HtelescopeTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htype⟩
  exact H.sourcePrimaryRecursorRealizationAtFreshOfTelescope Hprod Hsource
    Hmetadata hempty familyIdx hfamily hdecl hentry Hstep targetType Htype

theorem NestedLoweringResult.sourceTypeName
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams types
      { initialState with newTypes := types.toArray } result)
    (hsource : source ∈ types) :
    ∃ lowered ∈ result.types, lowered.name = source.name := by
  rcases H with ⟨finalState, Hrun⟩
  apply Hrun.preservesInitialTypeName
  exact ⟨source, by simpa using hsource, rfl⟩

/-- Specialize `restorationSources` from the installed lowered family list
back to each original source family, using the lowering trace for name
preservation and target constructor telescopes. -/
theorem RecursorPhasesResult.restorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (Hlower : NestedLoweringResult prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ owner, owner ∈ sourceTypes →
      ∃ oldInfo : InductiveVal,
        outEnv.find? owner.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            outEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type nparams) ∧
        ∃ recInfo : RecursorVal,
          outEnv.find? (Lean.mkRecName owner.name) = some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs nparams := by
  have Hlowered := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hlower.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  intro owner howner
  rcases Hlower.sourceTypeName howner with
    ⟨lowered, hlowered, hname⟩
  simpa [hname] using Hlowered lowered (by simpa using hlowered)

/-- Every auxiliary recursor selected by the production restoration map is
the installed recursor of one of the dynamically generated lowered families.
Consequently its type and every rule RHS satisfy the telescope discipline
required by restoration. -/
theorem RecursorPhasesResult.auxRestorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (Hlower : NestedLoweringResult prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap outEnv sourceTypes).1 →
      ∃ oldInfo : RecursorVal,
        outEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs nparams := by
  rcases Hlower with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  subst sourceTypes
  have Hrestorable := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hrun.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  have hmainPresent :
      NewTypeNamePresent
        { initialState with newTypes := (main :: rest).toArray } main.name :=
    ⟨main, by simp, rfl⟩
  rcases Hrun.preservesInitialTypeName hmainPresent with
    ⟨loweredMain, hloweredMain, hmainName⟩
  rcases H.findSourceHeader Hc (by simpa using hloweredMain) with
    ⟨mainInfo, hmainFind, _hctors, hall⟩
  have hmainFind' :
      outEnv.find? main.name = some (.inductInfo mainInfo) := by
    simpa [hmainName] using hmainFind
  have hall' :
      mainInfo.all = res.types.map (fun type => type.name) := by
    simpa using hall
  intro recName hrecName
  rcases mkAuxRecNameMap_recNames_mem main rest outEnv mainInfo hmainFind'
      hrecName with ⟨familyName, hfamilyName, rfl⟩
  rw [hall'] at hfamilyName
  rcases List.mem_map.mp hfamilyName with
    ⟨family, hfamily, rfl⟩
  rcases Hrestorable family (by simpa using hfamily) with
    ⟨_oldIndInfo, _hindFind, _hctors, recInfo, hrecFind, hrecType,
      hrecRules⟩
  exact ⟨recInfo, hrecFind, hrecType, hrecRules⟩

/-- End-to-end verifier for production nested restoration after a verified
lowered installation. Both declaration-source arguments are now consequences
of lowering and installation; only the subsequent auxiliary type-checking
pass remains parameterized by its own semantic postcondition. -/
theorem Environment.restoreNestedAfterInstall.ofLoweringWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
    (Hlower : NestedLoweringResult sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          Validated outEnv := by
  have hnparams : res.nparams = nparams := Hlower.resultNParams
  apply Environment.restoreNestedAfterInstall.WF sourceProdEnv loweredEnv
    lparams sourceTypes safety allowPrimitive fuel res
  · intro owner howner
    simpa [hnparams] using
      H.restorationSourcesOfLowering Hc Hlower owner howner
  · intro recName hrecName
    simpa [hnparams] using
      H.auxRestorationSourcesOfLowering Hc Hlower recName hrecName
  · exact Hvalidate

/-- Closed-lowering specialization of `ofLoweringWF`.  The final auxiliary
validation pass is no longer a semantic callback: every witness in the
production `aux2nested` map is known to be scoped by the exact local context
returned by lowering, so the ordinary type-checker soundness theorem applies
directly in the restored environment. -/
theorem Environment.restoreNestedAfterInstall.ofLoweringClosedWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
    (Hlower : NestedLoweringResultClosed sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (venv : VEnv)
    (hvalid : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          (fun _ =>
            ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
            ∃ selection : LocalForallSelection res.lctx res.params,
              ClosedNestedAuxiliaryTranslations venv lparams res selection)
          outEnv := by
  apply Environment.restoreNestedAfterInstall.ofLoweringWF Hc H
    Hlower.toResult lparams safety allowPrimitive fuel
    (fun _ =>
      ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
      ∃ selection : LocalForallSelection res.lctx res.params,
        ClosedNestedAuxiliaryTranslations venv lparams res selection)
  intro restoredEnv Hrestoration
  have Hvalid := hvalid restoredEnv Hrestoration
  refine (Hlower.validateNestedAuxiliariesWF Hvalid mlctx hmlctx hlctx
    hfresh).mono fun _ Hvalidated => ⟨Hvalidated, ?_⟩
  rcases Hlower with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.validatedAuxiliaryResidualTranslations Hvalid.tr.wf
    mlctx hmlctx hlctx Hvalidated

theorem ElimNestedInductive.run'.translation
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env) :
    ((Lean4Lean.ElimNestedInductive.run fuel nparams types env).run'
      state).WF (NestedLoweringResult env fuel nparams types state) := by
  have Hrun := ElimNestedInductive.run.translation fuel nparams types env state
    hclosures
  have Hprojected := Hrun.map fun out Hout =>
    show NestedLoweringResult env fuel nparams types state out.1 from
      ⟨out.2, Hout⟩
  simpa [StateT.run'] using Hprojected

theorem ElimNestedInductive.run'.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    ((Lean4Lean.ElimNestedInductive.run fuel nparams types env).run'
      state).WF (NestedLoweringResultClosed env fuel nparams types state) := by
  have Hrun := ElimNestedInductive.run.translationClosed fuel nparams types env
    state hclosures Henv Hsources hinitial hempty
  have Hprojected := Hrun.map fun out Hout =>
    show NestedLoweringResultClosed env fuel nparams types state out.1 from
      ⟨out.2, Hout.1, Hout.2.1, Hout.2.2⟩
  simpa [StateT.run'] using Hprojected

/-- Exact outer composition for `Environment.addInductive`, retaining both
the source-syntax checks and the complete lowering trace for the continuation.
These are independent inputs to the later source-WF and nested-compilation
proofs, so neither is intentionally discarded here. -/
theorem Environment.addInductive.checkedLoweringWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResult env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.translation fuel.inductiveFuel
    nparams types env
    { lvls := lparams.map .param, newTypes := types.toArray } hclosures
  have Hcombined := Hsources.bind fun _ Hsource =>
    Hlowering.bind fun res Hres => Hfinish res Hsource Hres
  simpa [Environment.addInductive] using Hcombined

/-- Strengthened outer composition used by the soundness proof.  Unlike the
compatibility theorem above, this result discharges dynamic auxiliary-family
closedness and the final cache scoping invariant from the source checks and
the verified production environment. -/
theorem Environment.addInductive.checkedLoweringClosedWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResultClosed env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hcombined := Hsources.bind fun _ Hsource =>
    (ElimNestedInductive.run'.translationClosed fuel.inductiveFuel nparams
      types env { lvls := lparams.map .param, newTypes := types.toArray }
      hclosures Henv Hsource rfl rfl).bind fun res Hres =>
        Hfinish res Hsource Hres
  simpa [Environment.addInductive] using Hcombined

/-- Compatibility projection of `checkedLoweringWF` for clients whose final
postcondition does not depend on the retained source-syntax certificate. -/
theorem Environment.addInductive.loweringWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      NestedLoweringResult env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  apply Environment.addInductive.checkedLoweringWF env lparams nparams types
    isUnsafe allowPrimitive fuel hclosures Q
  intro res _Hsource Hlower
  exact Hfinish res Hlower

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
