import Lean4Lean.Verify.Inductive.CompletedEquationRecursiveCall

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Cached call-argument frame for one recursive result.  Semantic indices
and the eta-expanded constructor field are narrowed and then closed through
the same replayed front, so their targets cannot come from unrelated
existential telescope choices. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.cachedSemanticCallArgumentFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (B : A.NarrowFieldRuntimeFrame :=
      Classical.choice A.narrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices narrowMajor
                narrowExposed,
              Hscope.frontSourceDomains = fieldDomains ++ localDomains ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us B.fieldScope
                (F.semantic.generated.current.lctx.mkForall
                  F.semantic.generated.localArgs (.sort .zero))
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              H.outVEnv.IsType Us.length B.fieldScope.toCtx
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              OnCtx
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext (fieldDomains ++ localDomains)
                    parameterDecls))
                (sourceIndices.map fun index =>
                  (index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size)
                narrowIndices ∧
              TrExprS H.outVEnv Us
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls)
                (F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars) narrowMajor ∧
              TrExprS H.outVEnv Us
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls)
                ((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size) narrowExposed ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls).toCtx narrowMajor narrowExposed ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.narrowSemanticIndices (B := B) with
    ⟨binding, evidence, scope, Hscope, hscopeFVars, hscopeBase,
      localDomains, hlocal, hfront, HforallReplay,
      narrowIndices, hlength, HnarrowIndices, HindexEq⟩
  rcases F.narrowSemanticAppliedMajor scope Hscope hscopeFVars with
    ⟨narrowMajor, HnarrowMajor, HmajorEq⟩
  rcases F.narrowSemanticAppliedMajorTypingFor scope Hscope hscopeFVars
      HnarrowMajor with
    ⟨narrowExposed, HnarrowExposed, HnarrowTyping⟩
  rcases F.narrowRuntimeFrontAlignment scope Hscope hscopeFVars hscopeBase with
    ⟨hfrontFVars, _hfrontLength, HfrontCtx⟩
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hzero : TrExprS H.outVEnv Us scope
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have HzeroType : H.outVEnv.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  rcases HforallReplay Hzero HzeroType with
    ⟨HlocalTemplate, HlocalTemplateType⟩
  have hprefixNodup :
      (VLCtx.fvars
        (scope.take Hscope.frontSourceDomains.length)).Nodup :=
    (VLCtx.fvars_take_sublist scope
      Hscope.frontSourceDomains.length).nodup
        (Hscope.scopeWF H.outVEnvWF).fvars_nodup
  have hclosedFVarsNodup :
      (A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars).Nodup := by
    rw [← hfrontFVars]
    exact List.nodup_reverse.mpr hprefixNodup
  have hsourceShape : ∀ source : Expr,
      source.abstractList
          (VLCtx.fvars
            (scope.take Hscope.frontSourceDomains.length)).reverse =
        (source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size := by
    intro source
    have habstract := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.all_args_bound.fvars)
      (inner := F.semantic.generated.arguments_bound.fvars) (k := 0)
      hclosedFVarsNodup
    have hlocalLength :
        F.semantic.generated.arguments_bound.fvars.length =
          F.semantic.generated.localArgs.size :=
      F.semantic.generated.arguments_bound.length_fvars
    rw [hlocalLength] at habstract
    simpa [hfrontFVars] using habstract.symm
  have HclosedIndices : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext Hscope.frontSourceDomains parameterDecls))
      (sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size)
      narrowIndices := by
    have close : ∀ {sources targets},
        List.Forall₂ (TrExprS H.outVEnv Us scope) sources targets →
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext Hscope.frontSourceDomains
              parameterDecls))
          (sources.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                F.semantic.generated.localArgs.size)
          targets := by
      intro sources targets Hsources
      induction Hsources with
      | nil => exact .nil
      | @cons source target sources targets Hsource _ ih =>
        have HsourceClosed := Hscope.abstractFront
          H.outVEnvWF hscopeBase Hsource
        rw [hsourceShape source] at HsourceClosed
        exact .cons HsourceClosed ih
    exact close HnarrowIndices
  let sourceMajor := mkAppN A.rule.recursiveArgs[j]
    F.semantic.generated.localArgs
  have hlocalAbstract :
      F.semantic.generated.localArgs.map (fun arg => arg.abstractList
        F.semantic.generated.arguments_bound.fvars) =
      (List.ofFn (fun index :
          Fin F.semantic.generated.arguments_bound.fvars.length =>
        Expr.bvar
          (F.semantic.generated.arguments_bound.fvars.length - 1 - index)
        )).toArray := by
    calc
      F.semantic.generated.localArgs.map (fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars) =
          ((F.semantic.generated.arguments_bound.fvars.map Expr.fvar).toArray.map
            fun arg => arg.abstractList
              F.semantic.generated.arguments_bound.fvars) := by
        exact congrArg (Array.map fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars)
            F.semantic.generated.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          F.semantic.generated.arguments_bound.fvars 0
          F.semantic.generated.arguments_bound.nodup
  have hmajorLocal : sourceMajor.abstractList
      F.semantic.generated.arguments_bound.fvars =
      F.semantic.generated.abstractedMajor := by
    unfold sourceMajor BoundGeneratedRecursiveCall.abstractedMajor
    rw [Expr.abstractList_mkAppN, hlocalAbstract]
  have HclosedMajor := Hscope.abstractFront
    H.outVEnvWF hscopeBase HnarrowMajor
  rw [hsourceShape sourceMajor, hmajorLocal] at HclosedMajor
  have HclosedMajor' : TrExprS H.outVEnv Us
      (abstractForallContext Hscope.frontSourceDomains parameterDecls)
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars) narrowMajor := by
    simpa [BoundGeneratedRecursiveCall.outerAbstractedMajor] using
      HclosedMajor
  have HclosedExposed := Hscope.abstractFront
    H.outVEnvWF hscopeBase HnarrowExposed
  rw [hsourceShape F.semantic.generated.exposedType] at HclosedExposed
  have HclosedTyping : H.outVEnv.HasType Us.length
      (abstractForallContext Hscope.frontSourceDomains parameterDecls).toCtx
      narrowMajor narrowExposed := by
    have hcontext :
        (abstractForallContext Hscope.frontSourceDomains parameterDecls).toCtx =
          scope.toCtx := by
      rw [Hscope.front.sourceContext, hscopeBase]
      simp [parameterDecls]
    rw [hcontext]
    exact HnarrowTyping
  let fieldDomains := B.fieldDomains
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    exact B.fieldDomains_length
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    narrowIndices, narrowMajor, narrowExposed, hfront, hfields, rfl, hlocal,
    HlocalTemplate, HlocalTemplateType,
    by simpa [hfront] using HfrontCtx, hlength,
    by simpa [hfront] using HclosedIndices,
    by simpa [hfront] using HclosedMajor',
    by simpa [hfront] using HclosedExposed,
    by simpa [hfront] using HclosedTyping, HindexEq, HmajorEq⟩

/-- Close the replayed constructor-field and higher-order-argument front of
every narrowed recursive index.  The resulting translations live directly
over the cached parameter declarations and use the same nested abstraction
shape as the generated equation RHS. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.closedNarrowSemanticIndices
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ narrowIndices,
              Hscope.frontSourceDomains.length =
                A.rule.allArgs.size +
                  F.semantic.generated.localArgs.size ∧
              OnCtx
                (abstractForallContext Hscope.frontSourceDomains
                  parameterDecls).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext Hscope.frontSourceDomains
                    parameterDecls))
                (sourceIndices.map fun index =>
                  (index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size)
                narrowIndices ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.narrowSemanticIndices with
    ⟨binding, evidence, scope, Hscope, hscopeFVars, hscopeBase,
      _localDomains, _hlocal, _hfront, _HforallReplay,
      narrowIndices, hlength, HnarrowIndices, HindexEq⟩
  have hfrontRev :
      VLCtx.fvars (scope.take Hscope.frontSourceDomains.length) =
        F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse := by
    have hsplit := Hscope.frontFVars hscopeBase
    have happend :
        VLCtx.fvars (scope.take Hscope.frontSourceDomains.length) ++
            parameterDecls.fvars =
          (F.semantic.recent.fvars.reverse ++
            A.semantics.fieldsRecent.fvars.reverse) ++
              parameterDecls.fvars := by
      rw [← hsplit, hscopeFVars]
    exact List.append_cancel_right happend
  have hlocalFVars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have hfieldFVars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have hfrontFVars :
      (VLCtx.fvars
        (scope.take Hscope.frontSourceDomains.length)).reverse =
          A.rule.all_args_bound.fvars ++
            F.semantic.generated.arguments_bound.fvars := by
    rw [hfrontRev, List.reverse_append, List.reverse_reverse,
      List.reverse_reverse, hlocalFVars, hfieldFVars]
  have hprefixNodup :
      (VLCtx.fvars
        (scope.take Hscope.frontSourceDomains.length)).Nodup :=
    (VLCtx.fvars_take_sublist scope
      Hscope.frontSourceDomains.length).nodup
        (Hscope.scopeWF H.outVEnvWF).fvars_nodup
  have hclosedFVarsNodup :
      (A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars).Nodup := by
    rw [← hfrontFVars]
    exact List.nodup_reverse.mpr hprefixNodup
  have hsourceShape : ∀ source : Expr,
      source.abstractList
          (VLCtx.fvars
            (scope.take Hscope.frontSourceDomains.length)).reverse =
        (source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size := by
    intro source
    have habstract := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.all_args_bound.fvars)
      (inner := F.semantic.generated.arguments_bound.fvars) (k := 0)
      hclosedFVarsNodup
    have hlocalLength :
        F.semantic.generated.arguments_bound.fvars.length =
          F.semantic.generated.localArgs.size :=
      F.semantic.generated.arguments_bound.length_fvars
    rw [hlocalLength] at habstract
    simpa [hfrontFVars] using habstract.symm
  have Hclosed : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext Hscope.frontSourceDomains parameterDecls))
      (sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size)
      narrowIndices := by
    have close : ∀ {sources : List Expr} {narrows : List VExpr},
        List.Forall₂ (TrExprS H.outVEnv Us scope) sources narrows →
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext Hscope.frontSourceDomains
              parameterDecls))
          (sources.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                F.semantic.generated.localArgs.size)
          narrows := by
      intro sources narrows Hsources
      induction Hsources with
      | nil => exact .nil
      | @cons source narrow sources narrows Hsource _ ih =>
        have HsourceClosed := Hscope.abstractFront
          H.outVEnvWF hscopeBase Hsource
        rw [hsourceShape source] at HsourceClosed
        exact .cons HsourceClosed ih
    exact close HnarrowIndices
  have hfrontLength : Hscope.frontSourceDomains.length =
      A.rule.allArgs.size + F.semantic.generated.localArgs.size := by
    have hlengthNames := congrArg List.length hfrontFVars
    have hlengthNames' :
        (VLCtx.fvars
          (scope.take Hscope.frontSourceDomains.length)).length =
        (A.rule.all_args_bound.fvars ++
          F.semantic.generated.arguments_bound.fvars).length := by
      simpa using hlengthNames
    calc
      Hscope.frontSourceDomains.length =
          (scope.take Hscope.frontSourceDomains.length).length :=
        (List.length_take_of_le
          Hscope.front.sourceLengthLEScope).symm
      _ = (VLCtx.fvars
          (scope.take Hscope.frontSourceDomains.length)).length :=
        (Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          Hscope.front.sourceDeclarations).symm
      _ = (A.rule.all_args_bound.fvars ++
          F.semantic.generated.arguments_bound.fvars).length :=
        hlengthNames'
      _ = A.rule.allArgs.size +
          F.semantic.generated.localArgs.size := by
        simp [A.rule.all_args_bound.length_fvars,
          F.semantic.generated.arguments_bound.length_fvars]
  exact ⟨binding, evidence, scope, Hscope, narrowIndices,
    hfrontLength, Hscope.abstractFrontWF H.outVEnvWF hscopeBase,
    hlength, Hclosed, HindexEq⟩

/-- Split the closed narrow index frame at the rule-field boundary.  The
outer part is now a candidate equation telescope, while the inner part is
exactly the higher-order argument telescope of this recursive call. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.cachedSemanticIndexFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices,
              Hscope.frontSourceDomains = fieldDomains ++ localDomains ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              OnCtx
                (abstractForallContext fieldDomains parameterDecls).toCtx
                (H.outVEnv.IsType Us.length) ∧
              OnCtx
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext (fieldDomains ++ localDomains)
                    parameterDecls))
                (sourceIndices.map fun index =>
                  (index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size)
                narrowIndices ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.closedNarrowSemanticIndices with
    ⟨binding, evidence, scope, Hscope, narrowIndices,
      hfrontLength, HfrontCtx, hlength, Hindices, HindexEq⟩
  let fieldDomains := Hscope.frontSourceDomains.take A.rule.allArgs.size
  let localDomains := Hscope.frontSourceDomains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤
      Hscope.frontSourceDomains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hlocal : localDomains.length =
      F.semantic.generated.localArgs.size := by
    simp [localDomains, List.length_drop, hfrontLength]
  have hfront : Hscope.frontSourceDomains =
      fieldDomains ++ localDomains := by
    exact (List.take_append_drop A.rule.allArgs.size
      Hscope.frontSourceDomains).symm
  have HfullCtx : OnCtx
      (abstractForallContext (fieldDomains ++ localDomains)
        parameterDecls).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [hfront] using HfrontCtx
  have HfieldCtx : OnCtx
      (abstractForallContext fieldDomains parameterDecls).toCtx
      (H.outVEnv.IsType Us.length) := by
    have Hdropped := HfullCtx.drop localDomains.length
    simpa [List.reverse_append, hlocal, List.drop_append,
      List.length_reverse] using Hdropped
  have Hindices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ localDomains)
          parameterDecls))
      (sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size)
      narrowIndices := by
    simpa [hfront] using Hindices
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    narrowIndices, hfront, hfields, hlocal, HfieldCtx, HfullCtx,
    hlength, Hindices', HindexEq⟩

/-- Close the cached parameter variables outside the split field/local
telescope.  At this point every concrete recursive index is free-variable
closed; motives and minors are the only equation binders still to insert. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.parameterClosedSemanticIndexFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices,
              Hscope.frontSourceDomains = fieldDomains ++ localDomains ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              OnCtx
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) []).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext
                    (parameterDecls.toCtx.reverse ++ fieldDomains ++
                      localDomains) []))
                (sourceIndices.map fun index =>
                  ((index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size).abstractList
                        A.rule.params_bound.fvars
                        (F.semantic.generated.localArgs.size +
                          A.rule.allArgs.size))
                narrowIndices ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.cachedSemanticIndexFrame with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      narrowIndices, hfront, hfields, hlocal, _HfieldCtx, HfullCtx,
      hlength, Hindices, HindexEq⟩
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have closeParameters : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ localDomains)
            parameterDecls)) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains)
            []))
        (sources.map fun source => source.abstractList
          A.rule.params_bound.fvars
          (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
        targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | @cons source target sources targets Hsource _ ih =>
      have Hclosed := H.parameterSuffix.abstractParameters
        A.rule.params_bound hparamsNodup Hsource
      have hdomains : (fieldDomains ++ localDomains).length =
          F.semantic.generated.localArgs.size + A.rule.allArgs.size := by
        simp [hfields, hlocal, Nat.add_comm]
      rw [hdomains] at Hclosed
      have Hclosed' : TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains)
            [])
          (source.abstractList A.rule.params_bound.fvars
            (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
          target := by
        simpa [parameterDecls, List.append_assoc] using Hclosed
      exact List.Forall₂.cons Hclosed' ih
  have Hclosed := closeParameters Hindices
  have HclosedCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains)
        []).toCtx (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using HfullCtx
  have Hclosed' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains)
          []))
      (sourceIndices.map fun index =>
        ((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars
              (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
      narrowIndices := by
    simpa [List.map_map, Function.comp_def] using Hclosed
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    narrowIndices, hfront, hfields, hlocal, HclosedCtx, hlength,
    Hclosed', HindexEq⟩

/-- Close cached parameters for the shared index/major frame.  Both argument
groups remain paired with the same narrowed targets, and the resulting
sources are ready for insertion of the generated motive/minor block. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.parameterClosedSemanticCallArgumentFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (B : A.NarrowFieldRuntimeFrame :=
      Classical.choice A.narrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices narrowMajor
                narrowExposed,
              Hscope.frontSourceDomains = fieldDomains ++ localDomains ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains) [])
                (((F.semantic.generated.current.lctx.mkForall
                    F.semantic.generated.localArgs (.sort .zero)).abstractList
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars A.rule.allArgs.size)
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              H.outVEnv.IsType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains) []).toCtx
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              OnCtx
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) []).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext
                    (parameterDecls.toCtx.reverse ++ fieldDomains ++
                      localDomains) []))
                (sourceIndices.map fun index =>
                  (((index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size).abstractList
                        A.rule.params_bound.fvars cutoff))
                narrowIndices ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) [])
                ((F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars cutoff) narrowMajor ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) [])
                (((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size).abstractList
                      A.rule.params_bound.fvars cutoff) narrowExposed ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) []).toCtx narrowMajor narrowExposed ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  rcases F.cachedSemanticCallArgumentFrame (B := B) with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      narrowIndices, narrowMajor, narrowExposed, hfront, hfields, hfieldEq,
      hlocal, HlocalTemplate, HlocalTemplateType,
      Hctx, hlength, Hindices, Hmajor, Hexposed, Htyping,
      HindexEq, HmajorEq⟩
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have closeSource : ∀ {source target},
      TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ localDomains)
          parameterDecls) source target →
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) [])
        (source.abstractList A.rule.params_bound.fvars cutoff) target := by
    intro source target Hsource
    have Hclosed := H.parameterSuffix.abstractParameters
      A.rule.params_bound hparamsNodup Hsource
    have hdomains : (fieldDomains ++ localDomains).length = cutoff := by
      simp [cutoff, hfields, hlocal, Nat.add_comm]
    rw [hdomains] at Hclosed
    simpa [parameterDecls, List.append_assoc] using Hclosed
  have closeSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ localDomains)
            parameterDecls)) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
        (sources.map fun source =>
          source.abstractList A.rule.params_bound.fvars cutoff) targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hsource _ ih => exact .cons (closeSource Hsource) ih
  have HclosedIndices := closeSources Hindices
  have HclosedIndices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
      (sourceIndices.map fun index =>
        (((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff))
      narrowIndices := by
    simpa [List.map_map, Function.comp_def] using HclosedIndices
  have HclosedMajor := closeSource Hmajor
  have HclosedExposed := closeSource Hexposed
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let HfieldRuntime := B.runtime.mono hbase
  have HfieldTemplate := HfieldRuntime.abstractFront
    H.outVEnvWF B.scope_base HlocalTemplate
  have hfieldFVars :
      (VLCtx.fvars
        (B.fieldScope.take HfieldRuntime.frontSourceDomains.length)).reverse =
          A.rule.all_args_bound.fvars := by
    simpa [HfieldRuntime,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using
      B.frontFVars
  rw [hfieldFVars] at HfieldTemplate
  have hfieldFront : HfieldRuntime.frontSourceDomains = B.fieldDomains := by
    simpa [HfieldRuntime,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using B.front
  have HparameterTemplate := H.parameterSuffix.abstractParameters
    A.rule.params_bound hparamsNodup HfieldTemplate
  rw [hfieldFront] at HparameterTemplate
  have HparameterTemplate' : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) [])
      (((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size)
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    rw [hfieldEq]
    simpa [parameterDecls, B.fieldDomains_length] using HparameterTemplate
  have HparameterTemplateType : H.outVEnv.IsType Us.length
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) []).toCtx
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    have Htype := HlocalTemplateType
    rw [B.fieldScope_eq] at Htype
    rw [hfieldEq]
    simpa [parameterDecls, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using Htype
  have HclosedCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using Hctx
  have HclosedTyping : H.outVEnv.HasType Us.length
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      narrowMajor narrowExposed := by
    have hcontext :
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx =
        (abstractForallContext (fieldDomains ++ localDomains)
          parameterDecls).toCtx := by
      simp [parameterDecls, List.reverse_append, List.append_assoc,
        VLCtx.toCtx]
    rw [hcontext]
    exact Htyping
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    narrowIndices, narrowMajor, narrowExposed, hfront, hfields, hfieldEq,
    hlocal, HparameterTemplate', HparameterTemplateType,
    HclosedCtx, hlength, HclosedIndices', HclosedMajor, HclosedExposed,
    HclosedTyping, HindexEq, HmajorEq⟩

/-- Insert the generated motive/minor block beneath the parameter-closed
field/local telescope.  Both the dependent domains and recursive-index
targets are lifted at the field/local cutoff, yielding the precise anonymous
context in which the full recursive recursor application will be assembled. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.insertedSemanticIndexFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    let inserted := T.motives ++ T.minors
    ∃ (fieldDomains localDomains liftedFront : List VExpr)
        (narrowIndices : List VExpr),
      let closedSource := fun index : Expr =>
        ((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars
              (F.semantic.generated.localArgs.size + A.rule.allArgs.size)
      liftedFront =
          (liftContextPrefix inserted.length
            (fieldDomains ++ localDomains).reverse).reverse ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        OnCtx
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
          (sourceIndices.map fun index =>
            (closedSource index).liftLooseBVars'
              (fieldDomains ++ localDomains).length inserted.length)
          (narrowIndices.map fun target =>
            target.liftN inserted.length
              (fieldDomains ++ localDomains).length) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let inserted := T.motives ++ T.minors
  rcases F.parameterClosedSemanticIndexFrame with
    ⟨_binding, _evidence, _scope, _Hscope, fieldDomains, localDomains,
      narrowIndices, _hfront, hfields, hlocal, HclosedCtx, _hlength,
      Hindices, _HindexEq⟩
  let liftedFront :=
    (liftContextPrefix inserted.length
      (fieldDomains ++ localDomains).reverse).reverse
  rcases A.finalRecursorParameterContext with ⟨T₀, hparams⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparamsT] at hparams
  have HprefixCanonical := T.prefixContext H.outVEnvWF.ordered
  have HprefixCanonical' : OnCtx
      (inserted.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [inserted, Us, List.reverse_append, List.append_assoc] using
      HprefixCanonical
  have HprefixEq :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      hparams HprefixCanonical'
  have Hinserted : OnCtx (inserted.reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    have := (HprefixEq.symm H.outVEnvWF.ordered).isType
    simpa [inserted, parameterDecls, H.parameterDecls, Us,
      List.reverse_append,
      List.append_assoc] using this
  have Hrecent : OnCtx
      ((fieldDomains ++ localDomains).reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append,
      List.append_assoc, VLCtx.toCtx] using HclosedCtx
  have HliftedCtx := Lean4Lean.OnCtx.insertAfterPrefix
    H.outVEnvWF.ordered Hrecent Hinserted
  have HequationCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [liftedFront, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using HliftedCtx
  have liftSources : ∀ {sources targets : List _},
      List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              (parameterDecls.toCtx.reverse ++ fieldDomains ++
                localDomains) []))
          sources targets →
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
          (sources.map fun source => source.liftLooseBVars'
            (fieldDomains ++ localDomains).length inserted.length)
          (targets.map fun target => target.liftN inserted.length
            (fieldDomains ++ localDomains).length) := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | @cons source target sources targets Hsource _ ih =>
      have Hsource' : TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++
              (fieldDomains ++ localDomains)) []) source target := by
        simpa only [List.append_assoc] using Hsource
      have Hlifted :=
        Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
          (outer := parameterDecls.toCtx.reverse)
          (inner := fieldDomains ++ localDomains)
          H.outVEnvWF.ordered Hsource' inserted
      simpa [liftedFront, List.append_assoc] using
        List.Forall₂.cons Hlifted ih
  have HliftedIndices := liftSources Hindices
  refine ⟨fieldDomains, localDomains, liftedFront, narrowIndices,
    rfl, hfields, hlocal, HequationCtx, ?_⟩
  simpa [inserted, List.map_map, Function.comp_def] using HliftedIndices

/-- Insert motives and minors into the shared recursive-call argument frame.
The narrowed indices and major are lifted at one common field/local cutoff,
ready to be consumed as a single generated-recursor suffix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.insertedSemanticCallArgumentFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
    (B : A.NarrowFieldRuntimeFrame :=
      Classical.choice A.narrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    let inserted := T.motives ++ T.minors
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ (fieldDomains localDomains liftedFront : List VExpr)
                (narrowIndices : List VExpr) (narrowMajor narrowExposed : VExpr),
              Hscope.frontSourceDomains = fieldDomains ++ localDomains ∧
              liftedFront =
                (liftContextPrefix inserted.length
                  (fieldDomains ++ localDomains).reverse).reverse ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++
                    (liftContextPrefix inserted.length
                      fieldDomains.reverse).reverse) [])
                (((((F.semantic.generated.current.lctx.mkForall
                    F.semantic.generated.localArgs (.sort .zero)).abstractList
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars A.rule.allArgs.size
                  ).liftLooseBVars' fieldDomains.length inserted.length))
                (VExpr.wrapForalls
                  ((liftContextPrefixAt inserted.length fieldDomains.length
                    localDomains.reverse).reverse) (.sort .zero)) ∧
              OnCtx
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                  []).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext
                    (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                    []))
                (sourceIndices.map fun index =>
                  ((((index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size).abstractList
                        A.rule.params_bound.fvars cutoff).liftLooseBVars'
                          cutoff inserted.length))
                (narrowIndices.map fun target =>
                  target.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                (((F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars cutoff).liftLooseBVars'
                      cutoff inserted.length)
                (narrowMajor.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                (((((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size).abstractList
                      A.rule.params_bound.fvars cutoff).liftLooseBVars'
                        cutoff inserted.length))
                (narrowExposed.liftN inserted.length cutoff) ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                  []).toCtx
                (narrowMajor.liftN inserted.length cutoff)
                (narrowExposed.liftN inserted.length cutoff) ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  let inserted := T.motives ++ T.minors
  rcases F.parameterClosedSemanticCallArgumentFrame (B := B) with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      narrowIndices, narrowMajor, narrowExposed, hfront, hfields, hfieldEq,
      hlocal, HparameterTemplate, _HparameterTemplateType,
      HclosedCtx, hlength, Hindices, Hmajor, Hexposed, Htyping,
      HindexEq, HmajorEq⟩
  let liftedFront :=
    (liftContextPrefix inserted.length
      (fieldDomains ++ localDomains).reverse).reverse
  rcases A.finalRecursorParameterContext with ⟨T₀, hparams⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparamsT] at hparams
  have HprefixCanonical := T.prefixContext H.outVEnvWF.ordered
  have HprefixCanonical' : OnCtx
      (inserted.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [inserted, Us, List.reverse_append, List.append_assoc] using
      HprefixCanonical
  have HprefixEq :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      hparams HprefixCanonical'
  have Hinserted : OnCtx
      (inserted.reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    have := (HprefixEq.symm H.outVEnvWF.ordered).isType
    simpa [inserted, parameterDecls, H.parameterDecls, Us,
      List.reverse_append, List.append_assoc] using this
  have Hrecent : OnCtx
      ((fieldDomains ++ localDomains).reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append,
      List.append_assoc, VLCtx.toCtx] using HclosedCtx
  have HliftedCtx := Lean4Lean.OnCtx.insertAfterPrefix
    H.outVEnvWF.ordered Hrecent Hinserted
  have HequationCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [liftedFront, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using HliftedCtx
  have hcutoff : (fieldDomains ++ localDomains).length = cutoff := by
    simp [cutoff, hfields, hlocal, Nat.add_comm]
  have HinsertedTemplate₀ :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := parameterDecls.toCtx.reverse)
      (inner := fieldDomains)
      H.outVEnvWF.ordered HparameterTemplate inserted
  have HinsertedTemplate : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++
          (liftContextPrefix inserted.length fieldDomains.reverse).reverse) [])
      (((((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size
        ).liftLooseBVars' fieldDomains.length inserted.length))
      (VExpr.wrapForalls
        ((liftContextPrefixAt inserted.length fieldDomains.length
          localDomains.reverse).reverse) (.sort .zero)) := by
    simpa [VExpr.liftN_wrapForalls, VExpr.liftN,
      List.append_assoc] using HinsertedTemplate₀
  have liftSource : ∀ {source target},
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) [])
        source target →
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
        (source.liftLooseBVars' cutoff inserted.length)
        (target.liftN inserted.length cutoff) := by
    intro source target Hsource
    have Hsource' : TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++
            (fieldDomains ++ localDomains)) []) source target := by
      simpa only [List.append_assoc] using Hsource
    have Hlifted :=
      Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
        (outer := parameterDecls.toCtx.reverse)
        (inner := fieldDomains ++ localDomains)
        H.outVEnvWF.ordered Hsource' inserted
    simpa [liftedFront, hcutoff, List.append_assoc] using Hlifted
  have liftSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
        sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
        (sources.map fun source =>
          source.liftLooseBVars' cutoff inserted.length)
        (targets.map fun target => target.liftN inserted.length cutoff) := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hsource _ ih => exact .cons (liftSource Hsource) ih
  have HliftedIndices := liftSources Hindices
  have HliftedExposed := liftSource Hexposed
  have HliftedIndices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
      (sourceIndices.map fun index =>
        ((((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff).liftLooseBVars'
                cutoff inserted.length))
      (narrowIndices.map fun target =>
        target.liftN inserted.length cutoff) := by
    simpa [List.map_map, Function.comp_def] using HliftedIndices
  have W : Ctx.LiftN inserted.length cutoff
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx := by
    rw [← hcutoff]
    have W' := Ctx.LiftN.insertAfterPrefix
      (fieldDomains ++ localDomains).reverse inserted.reverse
      parameterDecls.toCtx
    simpa [liftedFront, Nat.add_comm, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using W'
  have HliftedTyping := Htyping.weakN H.outVEnvWF.ordered W
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    liftedFront, narrowIndices, narrowMajor, narrowExposed, hfront, rfl,
    hfields, hfieldEq, hlocal, HinsertedTemplate, HequationCtx,
    hlength, HliftedIndices',
    liftSource Hmajor,
    HliftedExposed, HliftedTyping, HindexEq, HmajorEq⟩

/-- The production recursor level-parameter list and any installed abstract
recursor selected from the completed mutual batch have the same arity. -/
theorem CompletedRecursorPhasesResult.recursorUvarsAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
      H.entries[owner].2.uvars := by
  let E := H.generated.entry owner howner
  have htranslated : E.info.levelParams.length =
      H.entries[owner].2.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal, E] using
      E.translated.1.2.1
  simpa [E.levels, H.localExtends.lparams_eq] using htranslated

/-- Rule-local specialization of `recursorUvarsAt`. -/
theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.recursorUvars
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
      H.entries[owner].2.uvars := by
  exact H.recursorUvarsAt owner howner

/-- Context-polymorphic translation of any installed mutual recursor head at
its identity universe instantiation.  The owner index is supplied directly,
so recursive calls may select a family different from the equation owner. -/
theorem CompletedRecursorPhasesResult.finalRecursorHeadTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    TrExprS H.outVEnv Us Delta
      (.const (Lean.mkRecName indTypes[owner]!.name)
        (AddInductive.getRecLevels H.elimLevel stats.levels))
      (.const recursor.name (VLevel.params Us.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let E := H.generated.entry owner howner
  have hmem : recursor ∈ H.entries.map Prod.snd := by
    exact List.mem_map.mpr
      ⟨H.entries[owner], List.getElem_mem howner, rfl⟩
  have hlookup : H.outVEnv.constants recursor.name =
      some recursor.toVConstant := by
    apply VEnv.addConstVals_get H.installed.abstract
    exact hmem
  have hnameInfo : E.info.name = recursor.name := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, E, recursor] using
      E.translated.2
  have hname : Lean.mkRecName indTypes[owner]!.name = recursor.name :=
    E.name.symm.trans hnameInfo
  have hlevels := R.materializedFinal.recursorLevelsTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlength :
      (AddInductive.getRecLevels H.elimLevel stats.levels).length =
        recursor.uvars := by
    calc
      _ = (VLevel.params Us.length).length :=
        checkPositivityStep.List.mapM_some_length hlevels
      _ = Us.length := VLevel.params_length
      _ = recursor.uvars := H.recursorUvarsAt owner howner
  rw [hname]
  exact TrExprS.const hlookup hlevels hlength

/-- The concrete recursor constant at the head of the generated equation
translates directly to the installed owner recursor at its identity universe
instantiation.  This is context-polymorphic because constants do not inspect
the local telescope. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorHeadTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    TrExprS H.outVEnv Us Delta
      (.const (Lean.mkRecName indTypes[owner]!.name)
        (AddInductive.getRecLevels H.elimLevel stats.levels))
      (.const recursor.name (VLevel.params Us.length)) := by
  exact H.finalRecursorHeadTranslationAt owner howner Delta

/-- The recursor head selected by a validated recursive call translates to
the installed recursor for that call's target family.  In a mutual block this
family need not be the owner of the equation currently being generated. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.headTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    TrExprS H.outVEnv Us Delta
      (.const F.semantic.generated.recursorName
        (AddInductive.getRecLevels H.elimLevel stats.levels))
      (.const recursor.name (VLevel.params Us.length)) := by
  rw [F.semantic.generated.recursorName_eq_owner]
  exact H.finalRecursorHeadTranslationAt
    F.semantic.generated.ownerIdx F.entry_lt Delta

/-- The selected recursive recursor, canonically applied to the common
parameter/motive/minor prefix of its retained telescope, is well typed and
leaves precisely its target-family index/major suffix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.prefixTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    H.outVEnv.HasType Us.length
      (F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors).reverse
      (VExpr.mkApps
        ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).length 0)
        (recursorCanonicalVars
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).length))
      (VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  have huvars := H.recursorUvarsAt selectedOwner F.entry_lt
  change Us.length = recursor.uvars at huvars
  have hrec := F.typing
  change H.outVEnv.HasType recursor.uvars []
    (.const recursor.name (VLevel.params recursor.uvars)) recursor.type at hrec
  rw [← huvars] at hrec
  exact F.telescope.prefixTyping H.outVEnvWF.ordered hrec

/-- Transport the selected mutual recursor's common-prefix application into
the current equation owner's canonical common prefix, then weaken it under
the constructor fields.  This is the typing premise required to translate a
cross-family recursive-call prefix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.prefixTypingInEquationContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
    (fieldDomains : List VExpr)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    H.outVEnv.HasType Us.length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          ((VExpr.const recursor.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let ownerOuter := T.params ++ T.motives ++ T.minors
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have Hcommon := H.finalRecursorCommonPrefixContextAt
    owner howner selectedOwner F.entry_lt T F.telescope
  have HownerCtx : OnCtx (fieldDomains.reverse ++ ownerOuter.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [ownerOuter, List.reverse_append, List.append_assoc] using Hctx
  have Hfull :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hcommon HownerCtx
  have Hselected := F.prefixTyping
  have HselectedWeak := Hselected.weakN H.outVEnvWF.ordered
    (Ctx.LiftN.zero fieldDomains.reverse)
  have Htransported := HselectedWeak.defeqDFC H.outVEnvWF.ordered
    (Hfull.symm H.outVEnvWF.ordered)
  have hparamsLength : F.telescope.params.length = T.params.length := by
    rw [F.telescope.params_length, T.params_length]
  have hmotivesLength : F.telescope.motives.length = T.motives.length := by
    rw [F.telescope.motives_length, T.motives_length]
  have hminorsLength : F.telescope.minors.length = T.minors.length := by
    rw [F.telescope.minors_length, T.minors_length]
  have houterLength :
      (F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors).length =
      (T.params ++ T.motives ++ T.minors).length := by
    simp only [List.length_append, hparamsLength, hmotivesLength,
      hminorsLength]
  rw [houterLength] at Htransported
  simpa [selectedOuter, ownerOuter, List.reverse_append,
    List.append_assoc] using Htransported

/-- The parameter group of the call-selected generated recursor is
definitionally equal to the independently replayed canonical parameter
group for that same mutual family. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.canonicalParameterAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv Us stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        F.telescope.params.reverse C.params.reverse := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.finalRecursorParameterContextAt selectedOwner F.entry_lt with
    ⟨T, hgenerated⟩
  rcases T.groupsResult_eq F.telescope with
    ⟨hparams, _hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams] at hgenerated
  rcases H.finalCanonicalMotiveTelescopeAt selectedOwner F.entry_lt with
    ⟨C, hcanonical⟩
  exact ⟨C,
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
      hgenerated (hcanonical.symm H.outVEnvWF.ordered)⟩

/-- Exact generated owner-motive domain for the recursive call's selected
family, stated against the particular telescope retained in this frame. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.ownerMotiveDomainTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          F.telescope.params.reverse S.canonical.params.reverse ∧
      TrExprS H.outVEnv Us
        (abstractForallContext
          (F.telescope.params ++
            F.telescope.motives.take selectedOwner) [])
        ((H.localContext.lctx.mkForall
          H.recInfos[selectedOwner]!.indices
          (H.localContext.lctx.mkForall
            #[H.recInfos[selectedOwner]!.major]
            (.sort H.elimLevel))).abstractList
              (H.params.fvars ++
                H.bindings.motives.fvars.take selectedOwner))
        F.telescope.motives[selectedOwner]! ∧
      H.outVEnv.IsType Us.length
        (abstractForallContext
          (F.telescope.params ++
            F.telescope.motives.take selectedOwner) []).toCtx
        F.telescope.motives[selectedOwner]! := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.finalOwnerMotiveDomainTranslationAt selectedOwner F.entry_lt with
    ⟨T, S, hparameters, Hdomain, HdomainType⟩
  rcases T.groupsResult_eq F.telescope with
    ⟨hparams, hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams] at hparameters
  rw [hparams, hmotives] at Hdomain HdomainType
  exact ⟨S, hparameters, Hdomain, HdomainType⟩

/-- The motive binder selected by a recursive call is definitionally equal
to the independently reconstructed canonical motive type for that call's
mutual-family owner.  This is stated against the frame's fixed generated
telescope, so the subsequent index/major application cannot silently switch
to another structural decomposition of the recursor type. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.canonicalOwnerMotiveDomain
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          F.telescope.params.reverse S.motiveSourceScope.toCtx ∧
      H.outVEnv.IsDefEqU Us.length
        (abstractForallContext
          (F.telescope.params ++
            F.telescope.motives.take selectedOwner) []).toCtx
        F.telescope.motives[selectedOwner]!
        (S.canonical.motiveType.liftN
          (F.telescope.motives.take selectedOwner).length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.finalOwnerCanonicalMotiveDomainAt selectedOwner F.entry_lt with
    ⟨T, S, hparameters, Hdomain⟩
  rcases T.groupsResult_eq F.telescope with
    ⟨hparams, hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams] at hparameters
  rw [hparams, hmotives] at Hdomain
  exact ⟨S, hparameters, Hdomain⟩

/-- Complete dependent alignment between the selected recursor's generated
index/major suffix and the domains exposed by its selected motive binder.
Unlike the equation-owner specialization, this follows the owner recorded
by the validated recursive call and is fixed to `F.telescope`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.ownerMotiveSuffixContextAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          F.telescope.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
        F.telescope.motives[selectedOwner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors
        let suffix := F.telescope.indices ++ F.telescope.major
        let later := F.telescope.motives.drop (selectedOwner + 1) ++
          F.telescope.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (suffix.reverse ++ outer.reverse)
          (expected.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.finalOwnerMotiveTelescopeShapeForAt selectedOwner F.entry_lt
      F.telescope with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hownerMotive :
      selectedOwner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have Hsuffix := F.telescope.ownerMotiveSuffixContext H.outVEnvWF
    hownerMotive motiveDomains resultLevel hmotive hdomainLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Hsuffix⟩

/-- Insert an arbitrary well-formed inner front beneath the suffix alignment
selected by a recursive call.  This is the mutual-recursion counterpart of
`finalOwnerMotiveSuffixAlignmentUnderFields`: the owner is read from the
validated call rather than from the equation currently being generated. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.ownerMotiveSuffixAlignmentUnderFront
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (frontDomains : List VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (liftContextPrefix frontDomains.length suffix.reverse ++
          frontDomains.reverse ++ outer.reverse)
        (liftContextPrefix frontDomains.length expected.reverse ++
          frontDomains.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.ownerMotiveSuffixContextAlignment with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Hsuffix⟩
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have hsuffixLength : suffix.reverse.length = expected.reverse.length := by
    have htotal := Hsuffix.length_eq
    simp [outer, suffix, later, expected] at htotal ⊢
    omega
  have hfrontCtx : OnCtx (frontDomains.reverse ++ outer.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [outer, List.reverse_append, List.append_assoc] using hctx
  have Haligned := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered suffix.reverse expected.reverse
      frontDomains.reverse outer.reverse Hsuffix hsuffixLength hfrontCtx
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  simpa only [outer, suffix, later, expected, List.reverse_append,
    List.append_assoc, List.length_reverse] using Haligned

/-- The motive variable selected by a recursive call, weakened beneath an
arbitrary inner front, exposes exactly the independently reconstructed
index/major domains for that selected mutual-family owner. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.ownerMotiveFrontWitnessTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (frontDomains : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (frontDomains.reverse ++ outer.reverse)
        (.bvar (frontDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix frontDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.finalOwnerMotiveTelescopeShapeForAt selectedOwner F.entry_lt
      F.telescope with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hownerMotive : selectedOwner < F.telescope.motives.length := by
    rw [F.telescope.motives_length]
    simpa using hownerRecInfo
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have Hmotive := F.telescope.ownerMotiveOuterBvarTyping hownerMotive
  have W : Ctx.LiftN frontDomains.length 0 outer.reverse
      (frontDomains.reverse ++ outer.reverse) := by
    exact .zero frontDomains.reverse (by simp)
  have Hweak := Hmotive.weakN H.outVEnvWF.ordered W
  rw [show F.telescope.motives[selectedOwner]'hownerMotive =
      F.telescope.motives[selectedOwner]! by
        exact (getElem!_pos F.telescope.motives selectedOwner
          hownerMotive).symm,
    hmotive] at Hweak
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [outer, later, expected, VExpr.liftN_wrapForalls,
      liftContextPrefix, VExpr.liftN_liftN, VExpr.liftN, liftVar_base,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hweak⟩

/-- Re-close the call-selected suffix conversion as equality of function
types.  The residual stays the selected recursor's generated result; only
the dependent domains are replaced by those exposed by its owner motive. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.ownerMotiveSuffixTypeAlignmentUnderFront
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (frontDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.IsDefEqU Us.length
        (frontDomains.reverse ++
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).reverse)
        ((VExpr.wrapForalls suffix F.telescope.result).liftN
          frontDomains.length 0)
        (VExpr.wrapForalls expectedDomains
          (F.telescope.result.liftN frontDomains.length suffix.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.ownerMotiveSuffixAlignmentUnderFront frontDomains hctx with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Haligned⟩
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let actualRecent := liftContextPrefix frontDomains.length suffix.reverse
  let expectedRecent :=
    liftContextPrefix frontDomains.length expected.reverse
  let base := frontDomains.reverse ++ outer.reverse
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (actualRecent ++ base) (expectedRecent ++ base) := by
    simpa [Us, actualRecent, expectedRecent, base, outer, suffix, later,
      expected] using Haligned
  have HprefixType := Hprefix.isType H.outVEnvWF hctx
  rw [VExpr.liftN_wrapForalls] at HprefixType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    (ctx := base) (domains := actualRecent.reverse)
    (result := F.telescope.result.liftN frontDomains.length suffix.length)
    (by simpa [base, outer] using hctx) (by
      simpa [actualRecent, suffix, base, outer, liftContextPrefix,
        Nat.add_comm] using HprefixType)
  rcases Hopened.2 with ⟨bodyLevel, Hbody⟩
  have Hbody' : H.outVEnv.HasType Us.length
      (actualRecent ++ base)
      (F.telescope.result.liftN frontDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base, outer, suffix] using Hbody
  have hrecentLength : expectedRecent.length = actualRecent.length := by
    have hlength := Haligned'.length_eq
    simp only [List.length_append] at hlength
    omega
  have Hclosed := VEnv.IsDefEqCtx.closeHeads Haligned'
    actualRecent.length (by simp [actualRecent, suffix]) Hbody'
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have Hclosed' : H.outVEnv.IsDefEq Us.length base
      (VExpr.wrapForalls actualRecent.reverse
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (VExpr.wrapForalls expectedRecent.reverse
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (.sort closedLevel) := by
    have hrightTake : (expectedRecent ++ base).take actualRecent.length =
        expectedRecent := by
      rw [← hrecentLength]
      simp
    rw [List.drop_left, List.take_left, hrightTake] at Hclosed
    exact Hclosed
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  refine ⟨.sort closedLevel, ?_⟩
  change H.outVEnv.IsDefEq Us.length base
    ((VExpr.wrapForalls suffix F.telescope.result).liftN
      frontDomains.length 0)
    (VExpr.wrapForalls expectedRecent.reverse
      (F.telescope.result.liftN frontDomains.length suffix.length))
    (.sort closedLevel)
  rw [VExpr.liftN_wrapForalls]
  simpa [actualRecent, base, outer, suffix,
    liftContextPrefix, Nat.add_comm] using Hclosed'

/-- In a call-selected recursor context, the common prefix and selected
owner motive consume literally the same dependent index/major telescope.
This is the application-facing mutual analogue of
`finalCachedPrefixOwnerTelescope`; context transport to the equation owner's
cached parameters is deliberately left to the caller. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.prefixOwnerTelescopeUnderFront
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (frontDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let selectedOuter := F.telescope.params ++ F.telescope.motives ++
      F.telescope.minors
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ selectedOuter.reverse)
          (.bvar (frontDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  rcases F.ownerMotiveSuffixTypeAlignmentUnderFront
      frontDomains prefixTarget hctx Hprefix with
    ⟨alignedDomains, alignedLevel, halignedLength, halignedMotive,
      Haligned⟩
  rcases F.ownerMotiveFrontWitnessTyping frontDomains with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have hdomains : motiveDomains = alignedDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq hdomainLength halignedLength
      (suffix := [])
    simpa using hmotive.symm.trans halignedMotive
  subst alignedDomains
  have hresultLevel : resultLevel = alignedLevel := by
    have hsort : VExpr.sort resultLevel = VExpr.sort alignedLevel := by
      apply VExpr.wrapForalls_left_cancel motiveDomains
      exact hmotive.symm.trans halignedMotive
    exact VExpr.sort.inj hsort
  subst alignedLevel
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix frontDomains.length expected.reverse).reverse
  have hctx' : OnCtx (frontDomains.reverse ++ selectedOuter.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [selectedOuter, List.reverse_append, List.append_assoc] using hctx
  have Hprefix' : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
      ((VExpr.wrapForalls suffix F.telescope.result).liftN
        frontDomains.length 0) := by
    simpa [selectedOuter, suffix, List.reverse_append,
      List.append_assoc] using Hprefix
  have HprefixExpected : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
      (VExpr.wrapForalls expectedDomains
        (F.telescope.result.liftN frontDomains.length suffix.length)) := by
    exact Hprefix'.defeqU_r H.outVEnvWF hctx' (by
      simpa [selectedOuter, suffix, later, expected, expectedDomains,
        List.reverse_append, List.append_assoc] using Haligned)
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
    HprefixExpected, ?_, ?_⟩
  · simpa [selectedOuter, suffix, later, expected, expectedDomains,
      List.reverse_append, List.append_assoc] using Hmotive
  · exact SameTelescopeDomains.wrapForalls expectedDomains _ _

/-- Transport the call-selected prefix/motive telescope to an independently
cached outer context.  Context conversion preserves the exact prefix term,
selected motive de Bruijn variable, and shared dependent domains. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.cachedPrefixOwnerTelescopeUnderFront
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj)
    (frontDomains cachedBase : List VExpr) (prefixTarget : VExpr)
    (Hfull :
      let selectedOuter := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (frontDomains.reverse ++ selectedOuter.reverse)
        (frontDomains.reverse ++ cachedBase))
    (HcachedCtx : OnCtx (frontDomains.reverse ++ cachedBase)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (HprefixSelected :
      let selectedOuter := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      H.outVEnv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
        ((VExpr.wrapForalls
          (F.telescope.indices ++ F.telescope.major)
          F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ cachedBase) prefixTarget
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ cachedBase)
          (.bvar (frontDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have HselectedCtx : OnCtx
      (frontDomains.reverse ++ selectedOuter.reverse)
      (H.outVEnv.IsType Us.length) := Hfull.isType
  rcases F.prefixOwnerTelescopeUnderFront frontDomains prefixTarget
      (by simpa [selectedOuter, List.reverse_append,
        List.append_assoc] using HselectedCtx)
      (by simpa [selectedOuter] using HprefixSelected) with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
      HprefixExpected, HownerExpected, Hsame⟩
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix frontDomains.length expected.reverse).reverse
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_, ?_, Hsame⟩
  · exact HprefixExpected.defeqDFC H.outVEnvWF.ordered Hfull
  · exact HownerExpected.defeqDFC H.outVEnvWF.ordered Hfull

/-- Any concrete mutual-family constant retained in the executable statistics
translates under recursor universes to its installed abstract header at the
declaration-level universe instantiation. -/
theorem CompletedRecursorPhasesResult.finalInductiveHeadTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (target : Nat) (htarget : target < decl.types.length)
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    TrExprS H.outVEnv Us Delta stats.indConsts[target]!
      (.const decl.types[target].name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let targetVal := decl.types[target]
  have hlookupHeader : R.headerVEnv.constants targetVal.name =
      some targetVal.toVConstant := by
    apply VEnv.addConstVals_get R.installation.headerAbstract
    rw [R.headerValues]
    exact List.mem_map.mpr
      ⟨targetVal, List.getElem_mem htarget, rfl⟩
  have hlookupCtor : R.context.venv.constants targetVal.name =
      some targetVal.toVConstant :=
    R.installation.constructorLE.constants hlookupHeader
  have hlookup : H.outVEnv.constants targetVal.name =
      some targetVal.toVConstant :=
    H.installed.le.constants hlookupCtor
  have hsource : stats.indConsts[target]! =
      .const targetVal.name stats.levels := by
    rw [R.materializedFinal.consts]
    simp [targetVal, htarget]
  have hlevels := R.materializedFinal.recursorLevelTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      R.core.types
  have hsourceTarget : target < indTypes.toList.length := by
    simpa [htypesLength] using htarget
  have Htarget := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    R.core.types target hsourceTarget htarget
  have htargetUvars : targetVal.uvars = decl.uvars := by
    exact Htarget.header.uvars.trans R.materializedFinal.uvars
  have hlength : stats.levels.length = targetVal.uvars := by
    exact R.materializedFinal.levels.trans htargetUvars.symm
  dsimp only [Us, targetVal]
  rw [hsource]
  exact TrExprS.const hlookup hlevels hlength

/-- The concrete constructor constant at the head of the generated major
premise translates under recursor universes to the installed abstract
constructor at the declaration-level universe instantiation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalConstructorHeadTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceCtor :=
      (indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt
    TrExprS H.outVEnv Us Delta
      (.const sourceCtor.name stats.levels)
      (.const sourceCtor.name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceCtor :=
    (indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt
  let ctorVal :=
    (decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt
  have hctorMem : ctorVal ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[owner]'A.abstractOwner_lt,
      List.getElem_mem A.abstractOwner_lt,
      List.getElem_mem A.abstractCtor_lt⟩
  have hlookupBase : R.context.venv.constants ctorVal.name =
      some ctorVal.toVConstant := by
    apply VEnv.addConstVals_get R.installation.constructorAbstract
    rw [R.constructorValues]
    exact hctorMem
  have hlookup : H.outVEnv.constants ctorVal.name =
      some ctorVal.toVConstant :=
    H.installed.le.constants hlookupBase
  have hlevels := R.materializedFinal.recursorLevelTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlength : stats.levels.length = ctorVal.uvars := by
    calc
      stats.levels.length = decl.uvars := R.materializedFinal.levels
      _ = c.lparams.length := R.materializedFinal.uvars.symm
      _ = ctorVal.uvars := A.ctorTranslation.uvars.symm
  have hname : ctorVal.name = sourceCtor.name := by
    simpa [ctorVal, sourceCtor] using A.ctorTranslation.name
  dsimp only [Us, sourceCtor, ctorVal]
  rw [← hname]
  exact TrExprS.const hlookup hlevels hlength

/-- Typed canonical application of the common recursor prefix used by this
rule.  The remaining function consumes precisely the owner's indices and
major premise. -/
theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.recursorPrefixTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      H.outVEnv.HasType Us.length
        (T.params ++ T.motives ++ T.minors).reverse
        (VExpr.mkApps
          ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length))
        (VExpr.wrapForalls (T.indices ++ T.major) T.result) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  have hrec := A.recursorTyping
  have huvars := A.recursorUvars
  change Us.length = recursor.uvars at huvars
  change H.outVEnv.HasType recursor.uvars []
    (.const recursor.name (VLevel.params recursor.uvars)) recursor.type at hrec
  rw [← huvars] at hrec
  exact ⟨T, T.prefixTyping H.outVEnvWF.ordered hrec⟩

/-- Weaken the common recursor application below the genuine constructor
fields.  This packages it with the exact dependent equation context and the
checked constructor major already living there, so consuming the remaining
index/major suffix cannot accidentally choose a different telescope witness. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorPrefixEquationContextWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.semantics.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
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
          (recursorCanonicalVars stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCheckedConstructorEquationContextWithFrame with
    ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx,
      Hmajor, Htarget, HintroShape⟩
  have hrec := A.recursorTyping
  have huvars := A.recursorUvars
  change Us.length = recursor.uvars at huvars
  change H.outVEnv.HasType recursor.uvars []
    (.const recursor.name (VLevel.params recursor.uvars)) recursor.type at hrec
  rw [← huvars] at hrec
  have Hprefix := T.prefixTyping H.outVEnvWF.ordered hrec
  have Hprefix' := Hprefix.weakN H.outVEnvWF.ordered
    (Ctx.LiftN.zero fieldDomains.reverse)
  exact ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx, Hmajor, by
    simpa [List.reverse_append, List.append_assoc] using Hprefix',
    Htarget, HintroShape⟩

/-- Compatibility projection of
`finalRecursorPrefixEquationContextWithFrame` for clients that only need the
installed equation context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorPrefixEquationContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
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
          (recursorCanonicalVars stats.params.size) := by
  rcases A.finalRecursorPrefixEquationContextWithFrame with
    ⟨T, _originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, _horiginal, _hlifted, _Htail, _HoriginalCtx, hfields, Hctx, Hmajor,
      Hprefix, Htarget, HintroShape⟩
  exact ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields,
    Hctx, Hmajor, Hprefix, Htarget, HintroShape⟩

/-- The residual of the selected translated recursor is literally the owner
motive applied to its canonical index variables and major premise.  This
turns the otherwise opaque `T.result` field into the exact suffix shape that
the generated equation must instantiate. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorResultShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      T.result = VExpr.mkApps
        (.bvar
          (1 + H.recInfos[owner]!.indices.size +
            (H.recInfos.flatMap (·.minors)).size +
            ((H.recInfos.map (·.motive)).size - 1 - owner)))
        (((List.range H.recInfos[owner]!.indices.size).reverse.map
            fun index => .bvar (index + 1)) ++ [.bvar 0]) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  exact ⟨T, T.resultShape hownerMotive⟩

theorem CompletedRecursorPhasesResult.recursorNamesFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq) (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    ∀ name ∈ (H.blockCertificate rules hrules).block.recursors.map (·.name),
      R.context.venv.constants name = none := by
  have hfresh :=
    VEnv.addConstVals_names_fresh H.installed.abstract |>.2
  intro name hname
  change name ∈ (H.entries.map Prod.snd).map (·.name) at hname
  rcases List.mem_map.mp hname with ⟨recursor, hrecursor, rfl⟩
  exact hfresh recursor hrecursor


end VerifyInductive
end Lean4Lean
