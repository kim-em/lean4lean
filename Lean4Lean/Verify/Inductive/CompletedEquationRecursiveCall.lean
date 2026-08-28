import Lean4Lean.Verify.Inductive.CompletedEquationMotive

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Final-environment recursor package selected by one generated recursive
call.  The validated terminal application fixes the mutual-family owner, so
both the exact five-part telescope and the installed constant typing can be
selected without trusting the recursor name embedded in the generated term.
-/
structure
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame
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
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) where
  semantic : SemanticBoundGeneratedRecursiveCall indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    A.semantics.context decl A.semantics.depth
    A.rule.recursiveArgs[j] A.rule.recursiveResults[j]!
  root_scope : semantic.rootScope =
    (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params)
  entry_lt : semantic.generated.ownerIdx < H.entries.length
  telescope : GeneratedRecursorTelescopeTranslation H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (H.generated.entry semantic.generated.ownerIdx entry_lt).info.type
    H.entries[semantic.generated.ownerIdx].2.type
    stats.params.size (H.recInfos.map (·.motive)).size
    (H.recInfos.flatMap (·.minors)).size
    H.recInfos[semantic.generated.ownerIdx]!.indices.size
    semantic.generated.ownerIdx
  typing :
    let recursor := H.entries[semantic.generated.ownerIdx].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.recursiveCallRecursorFrame
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
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    Nonempty (A.RecursiveCallRecursorFrame j hj) := by
  rcases A.semantics.calls.entries j hj hj with ⟨S, hscope⟩
  have hrecInfo : S.generated.ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records]
    exact S.validated.target_lt
  have hentry : S.generated.ownerIdx < H.entries.length := by
    simpa [H.generated.length] using hrecInfo
  rcases H.finalRecursorTelescopeTranslationAt
      S.generated.ownerIdx hentry with ⟨T⟩
  exact ⟨{
    semantic := S
    root_scope := hscope
    entry_lt := hentry
    telescope := T
    typing := H.recursorTypingAt S.generated.ownerIdx hentry }⟩

/-- Closing first the call-local higher-order arguments and then the complete
constructor-field suffix removes every dependency except the cached inductive
parameters.  This is the narrow source-scope fact needed to replay a generated
recursive call in the cached equation context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedExposedScope
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
    ((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
      A.rule.all_args_bound.fvars
      F.semantic.generated.localArgs.size).FVarsIn
        (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
  have hlocalFvars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have Hlocal := FVarsIn.abstractList_of
    (selected := F.semantic.recent.fvars)
    (k := 0) F.semantic.exposed_scope
  rw [F.root_scope] at Hlocal
  have Hfields := FVarsIn.abstractList_of
    (selected := A.semantics.fieldOpening.fvars)
    (k := F.semantic.generated.localArgs.size) Hlocal
  have hfieldFvars : A.semantics.fieldOpening.fvars =
      A.rule.all_args_bound.fvars :=
    A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound
  simpa [hlocalFvars, hfieldFvars] using Hfields

/-- Replay the constructor fields once above the cached parameter scope.
This rule-wide frame is independent of any particular recursive call; later
call-local replay extends its retained front without changing the field
prefix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.narrowFieldRuntimeScope
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
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ fieldScope,
      ∃ HfieldScope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.recursorWF.venv Us fieldScope A.semantics.context.mlctx.vlctx,
        fieldScope.fvars =
            A.semantics.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        fieldScope.drop HfieldScope.frontSourceDomains.length =
            parameterDecls ∧
        ∃ fieldDomains,
          fieldDomains.length = A.rule.allArgs.size ∧
          HfieldScope.frontSourceDomains = fieldDomains := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls := H.parameterSuffix.parameterDecls
  let Hparameter := H.parameterSuffix.runtimeScope
  rcases A.semantics.context.onlyLams.lamPrefix
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le with
    ⟨_runtimeFieldDomains, HfieldPrefix⟩
  have hfieldRuntime :
      (A.semantics.context.mlctx.dropN A.rule.allArgs.size
        HfieldPrefix.le).vlctx = H.recursorWF.mlctx.vlctx := by
    have hle : HfieldPrefix.le = A.semantics.fieldsRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle, A.semantics.fieldsRecent.drop_eq,
      A.semantics.fieldRoot_vlctx]
  let HfieldBase := Hparameter.retargetRuntime hfieldRuntime.symm
  have HfieldWF : A.semantics.context.mlctx.WF H.recursorWF.venv Us := by
    simpa only [Us, A.semantics.context_venv] using
      A.semantics.context.mlctx_wf
  have hfieldRev : A.semantics.context.mlctx.fvarRevList
      A.rule.allArgs.size HfieldPrefix.le =
        A.semantics.fieldsRecent.fvars.reverse := by
    have hle : HfieldPrefix.le = A.semantics.fieldsRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact A.semantics.fieldsRecent.fvarRevList_eq
  have HfieldUp : IsFVarUpSet
      (fun fv => fv ∈ A.semantics.context.mlctx.fvarRevList
          A.rule.allArgs.size HfieldPrefix.le ++ parameterDecls.fvars)
      A.semantics.context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HfieldWF.tr.wf.fvwf ?_).mp
      A.semantics.fieldParameterUp
    intro fv _
    rw [hfieldRev, H.parameterSuffix.parameterDecls_fvars]
    simp [parameterDecls]
  rcases HfieldPrefix.extendNarrowRuntimeScope
      H.recursorWF.checking.tr.wf HfieldWF HfieldBase HfieldUp with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      fieldDomains, hfieldDomains, hfieldFront⟩
  have hbase : fieldScope.drop HfieldScope.frontSourceDomains.length =
      parameterDecls := by
    simpa [HfieldBase, Hparameter,
      checkInductiveTypes.loopType.NarrowRuntimeScope.retargetRuntime,
      RecursorParameterContextSuffix.runtimeScope,
      checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix]
      using hfieldBase
  have hfront : HfieldScope.frontSourceDomains = fieldDomains := by
    simpa [HfieldBase, Hparameter,
      checkInductiveTypes.loopType.NarrowRuntimeScope.retargetRuntime,
      RecursorParameterContextSuffix.runtimeScope,
      checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix]
      using hfieldFront
  exact ⟨fieldScope, HfieldScope, by simpa [hfieldRev] using
    hfieldScopeFVars, hbase, fieldDomains, hfieldDomains, hfront⟩

/-- First-class rule-wide field narrowing witness.  Recursive-result folds
retain one value of this structure and replay every call-local suffix above
its exact `fieldDomains`. -/
structure
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) where
  fieldScope : VLCtx
  runtime : checkInductiveTypes.loopType.NarrowRuntimeScope
    H.recursorWF.venv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    fieldScope A.semantics.context.mlctx.vlctx
  scope_fvars : fieldScope.fvars =
    A.semantics.fieldsRecent.fvars.reverse ++
      H.parameterSuffix.parameterDecls.fvars
  scope_base : fieldScope.drop runtime.frontSourceDomains.length =
    H.parameterSuffix.parameterDecls
  fieldDomains : List VExpr
  fieldDomains_length : fieldDomains.length = A.rule.allArgs.size
  front : runtime.frontSourceDomains = fieldDomains

/-- The rule-wide narrowing frame is literally the constructor-field
telescope abstracted over the cached parameter declarations.  This exposes
the context hidden behind `NarrowRuntimeScope` in the form used by the
selected-minor translation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.fieldScope_eq
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
    (B : A.NarrowFieldRuntimeFrame) :
    B.fieldScope.toCtx =
      (abstractForallContext B.fieldDomains
        H.parameterSuffix.parameterDecls).toCtx := by
  rw [abstractForallContext_toCtx, B.runtime.front.sourceContext,
    B.scope_base, B.front]

/-- The source identifiers closed by the fixed field narrowing frame are
literally the generated rule's constructor-field identifiers, in source
binder order. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.frontFVars
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
    (B : A.NarrowFieldRuntimeFrame) :
    (VLCtx.fvars
      (B.fieldScope.take B.runtime.frontSourceDomains.length)).reverse =
        A.rule.all_args_bound.fvars := by
  have hsplit := B.runtime.frontFVars B.scope_base
  have happend :
      VLCtx.fvars
          (B.fieldScope.take B.runtime.frontSourceDomains.length) ++
          H.parameterSuffix.parameterDecls.fvars =
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars := by
    rw [← hsplit, B.scope_fvars]
  have hfields : VLCtx.fvars
      (B.fieldScope.take B.runtime.frontSourceDomains.length) =
        A.semantics.fieldsRecent.fvars.reverse :=
    List.append_cancel_right happend
  rw [hfields, List.reverse_reverse]
  exact BoundFVarArray.fvars_eq
    A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    A.rule.all_args_bound rfl

/-- The narrowed constructor-field telescope is well formed in the final
recursor environment, over the exact cached parameter suffix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.fieldContextWF
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
    (B : A.NarrowFieldRuntimeFrame) :
    OnCtx
      (abstractForallContext B.fieldDomains
        H.parameterSuffix.parameterDecls).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have Hruntime := B.runtime.mono hbase
  have Hscope := Hruntime.scopeWF H.outVEnvWF
  rw [← B.fieldScope_eq]
  exact Hscope.toCtx

/-- Expose the rule-wide narrowing conversion before any call-local
higher-order arguments are added.  The expanded narrow context is related to
the literal field suffix of the executable semantic context, and dropping
that suffix reaches the common recursor root on both sides. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.semanticFieldContext
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    A.semantics.fieldTelescope.domains.length = A.rule.allArgs.size ∧
      A.semantics.context.mlctx.vlctx.toCtx =
        A.semantics.fieldTelescope.domains.reverse ++
          A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
      B.runtime.frontExpandedDomains.length = A.rule.allArgs.size ∧
      B.runtime.expanded.toCtx =
        B.runtime.frontExpandedDomains.reverse ++
          VLCtx.toCtx (B.runtime.expanded.drop
            B.runtime.frontExpandedDomains.length) ∧
      VLCtx.IsDefEq H.outVEnv Us.length
        (B.runtime.expanded.drop A.rule.allArgs.size)
        A.semantics.fieldRootContext.mlctx.vlctx ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        B.runtime.expanded.toCtx
        (A.semantics.fieldTelescope.domains.reverse ++
          A.semantics.fieldRootContext.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let semanticFieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hsemanticFields : semanticFieldDomains.length =
      A.rule.allArgs.size :=
    A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hsemanticContext :=
    MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
      A.semantics.context.onlyLams A.rule.allArgs.size
      A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.drop_eq] at hsemanticContext
  have hsemanticContext' : A.semantics.context.mlctx.vlctx.toCtx =
      semanticFieldDomains.reverse ++
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx := by
    simpa [semanticFieldDomains] using hsemanticContext
  have hfrontExpanded : B.runtime.frontExpandedDomains.length =
      A.rule.allArgs.size := by
    rw [← B.runtime.front.length_eq, B.front, B.fieldDomains_length]
  have hexpanded := B.runtime.front.expandedContext
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let Hruntime := B.runtime.mono hbase
  have hfieldDrop :
      A.semantics.context.mlctx.vlctx.drop A.rule.allArgs.size =
        A.semantics.fieldRootContext.mlctx.vlctx := by
    rw [← A.semantics.context.onlyLams.vlctx_dropN
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le,
      A.semantics.fieldsRecent.drop_eq]
  have HfieldBase := Hruntime.context.drop A.rule.allArgs.size
  rw [hfieldDrop] at HfieldBase
  have Hcontexts : VEnv.IsDefEqCtx H.outVEnv Us.length []
      B.runtime.expanded.toCtx
      (semanticFieldDomains.reverse ++
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx) := by
    have Hcontexts' := Hruntime.context.defeqCtx
    rw [hsemanticContext'] at Hcontexts'
    exact Hcontexts'
  simpa [semanticFieldDomains,
    BoundGeneratedRecursorRule.Semantics.fieldTelescope] using
      (show semanticFieldDomains.length = A.rule.allArgs.size ∧
          A.semantics.context.mlctx.vlctx.toCtx =
            semanticFieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
          B.runtime.frontExpandedDomains.length = A.rule.allArgs.size ∧
          B.runtime.expanded.toCtx =
            B.runtime.frontExpandedDomains.reverse ++
              VLCtx.toCtx (B.runtime.expanded.drop
                B.runtime.frontExpandedDomains.length) ∧
          VLCtx.IsDefEq H.outVEnv Us.length
            (B.runtime.expanded.drop A.rule.allArgs.size)
            A.semantics.fieldRootContext.mlctx.vlctx ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            B.runtime.expanded.toCtx
            (semanticFieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx) from
        ⟨hsemanticFields, hsemanticContext', hfrontExpanded, hexpanded,
          HfieldBase, Hcontexts⟩)

/-- Witness-stable composition of a retained first-pass consumed field
context with the fixed rule-wide narrow frame. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedFieldAlignmentFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (S : RecInfoMinorTypeShape)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (htail : HS.semantic.traversal.parameterTail =
      A.semantics.parameterTail)
    (hfields : S.fields.size = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ minorConsumedDomains : List VExpr,
      ∃ minorConsumedResidual,
      minorConsumedDomains.length = A.rule.allArgs.size ∧
      (VExpr.wrapForalls HS.semantic.fieldDomains
        HS.semantic.terminalTarget).lift'
          ((((HS.semantic.fieldsRecent.contextExtension.trans
            HS.semantic.hypothesesRecent.contextExtension).trans
              HS.semantic.extension).shift.consN 0)) =
        VExpr.wrapForalls minorConsumedDomains minorConsumedResidual ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (minorConsumedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
        B.runtime.expanded.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSemanticFieldAlignmentFor S HS htail hfields with
    ⟨minorConsumedDomains, minorConsumedResidual, hminor,
      hminorTarget, _hrule, Hminor⟩
  rcases B.semanticFieldContext with
    ⟨_hrule', _hsemanticContext, _hexpandedLength,
      _hexpandedContext, _HfieldBase, Hexpanded⟩
  have Hexpanded' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      B.runtime.expanded.toCtx
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    simpa [A.semantics.fieldRoot_vlctx] using Hexpanded
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF Hminor
    (Hexpanded'.symm H.outVEnvWF.ordered)
  exact ⟨minorConsumedDomains, minorConsumedResidual, hminor,
    by simpa using hminorTarget, Haligned⟩

/-- The field prefix obtained by translating the complete original minor in
the full recursor context is definitionally equal to the fixed narrow-field
runtime frame.  The proof passes through the exact first-pass replay target,
whose lifted field-domain prefix is independent of its hypothesis/motive
residual. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFullFieldAlignmentWithNarrowFrame
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
    (B : A.NarrowFieldRuntimeFrame)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope : VLCtx,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowFields weakenedFields fullFields installedFields
          installedHypotheses : List VExpr,
      ∃ installedResidual : VExpr,
      scope.fvars = sourceBinders.reverse ∧
      Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ sourceBinders) ∧
      narrowFields.length = A.rule.allArgs.size ∧
      weakenedFields.length = A.rule.allArgs.size ∧
      fullFields.length = A.rule.allArgs.size ∧
      installedFields.length = A.rule.allArgs.size ∧
      installedHypotheses.length = A.rule.recursiveArgs.size ∧
      weakenedFields = liftForallDomains narrowFields Hscope.shift ∧
      T.minors[minorIdx]! = VExpr.wrapForalls
        (installedFields ++ installedHypotheses) installedResidual ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
        (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (narrowFields.reverse ++ scope.toCtx)
        (installedFields.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (weakenedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
        B.runtime.expanded.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorNarrowFullContextAlignment hpositive with
    ⟨T, S, HS, scope, Hscope, narrowDomains, fullDomains,
      weakenedDomains, installedDomains, narrowResidual, fullResidual,
      weakenedResidual, installedResidual, hscope, hscopeShift,
      hfields, hhypotheses, htail, Hprefix, hnarrowLength, hfullLength,
      hweakenedLength,
      hinstalledLength, hfullTarget, hweakenedTarget, hinstalledTarget,
      HnarrowInstalled, HnarrowFull⟩
  rcases A.finalSelectedMinorExpandedFieldAlignmentFor
      B S HS htail hfields with
    ⟨minorConsumedDomains, minorConsumedResidual, hminorConsumed,
      hminorTarget, HminorNarrow⟩
  let Hext : RecursorContextExtension HS.semantic.rootWF H.recursorWF :=
    (HS.semantic.fieldsRecent.contextExtension.trans
      HS.semantic.hypothesesRecent.contextExtension).trans
        HS.semantic.extension
  let semanticDomains :=
    HS.semantic.fieldDomains ++ HS.semantic.hypothesisDomains
  have hsemanticFields : HS.semantic.fieldDomains.length =
      S.fields.size :=
    HS.semantic.terminalWF.onlyLams.forallDomains_length S.fields.size
      HS.semantic.fieldsRecent.size_le
  have hsemanticHypotheses : HS.semantic.hypothesisDomains.length =
      S.hypotheses.size :=
    HS.semantic.sourceWF.onlyLams.forallDomains_length S.hypotheses.size
      HS.semantic.hypothesesRecent.size_le
  have hsemanticLength : semanticDomains.length = arity := by
    simp [semanticDomains, hsemanticFields, hsemanticHypotheses,
      hfields, hhypotheses, arity]
  have Hreplayed₀ := HS.semantic.replayedSourceDefEqConsumed
  have Hreplayed₁ := HS.semantic.extension.weakDefEqU Hreplayed₀
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have Hreplayed : H.outVEnv.IsDefEqU Us.length
      H.recursorWF.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls semanticDomains HS.semantic.motiveTarget).lift'
        (Hext.shift.consN 0))
      (HS.semantic.consumedTarget.lift'
        (HS.semantic.extension.shift.consN 0)) := by
    have Hmono := Hreplayed₁.mono hbase
    simp only [Lift.consN] at Hmono ⊢
    dsimp only [Hext, RecursorContextExtension.trans] at Hmono ⊢
    rw [VExpr.lift'_comp]
    simpa [semanticDomains, VExpr.wrapForalls_append] using Hmono
  let replayedDomains := liftForallDomains semanticDomains
    (Hext.shift.consN 0)
  let replayedResidual := HS.semantic.motiveTarget.lift'
    ((Hext.shift.consN 0).consN semanticDomains.length)
  have hreplayedTarget :
      (VExpr.wrapForalls semanticDomains HS.semantic.motiveTarget).lift'
          (Hext.shift.consN 0) =
        VExpr.wrapForalls replayedDomains replayedResidual := by
    exact VExpr.lift'_wrapForalls_exact _ _ _
  have Hwhole : H.outVEnv.IsDefEqU Us.length
      H.recursorWF.mlctx.vlctx.toCtx
      (VExpr.wrapForalls replayedDomains replayedResidual)
      (VExpr.wrapForalls fullDomains fullResidual) := by
    rw [← hreplayedTarget, ← hfullTarget]
    exact Hreplayed
  have HruntimeWF : OnCtx H.recursorWF.mlctx.vlctx.toCtx
      (H.outVEnv.IsType Us.length) :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf.toCtx
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HruntimeWF
  have hreplayedLength : replayedDomains.length = arity := by
    simp [replayedDomains, hsemanticLength]
  have Hcontexts := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF Hbase
    (hreplayedLength.trans hfullLength.symm) Hwhole
  let replayedFields := replayedDomains.take A.rule.allArgs.size
  let narrowFields := narrowDomains.take A.rule.allArgs.size
  let weakenedFields := weakenedDomains.take A.rule.allArgs.size
  let fullFields := fullDomains.take A.rule.allArgs.size
  let installedFields := installedDomains.take A.rule.allArgs.size
  let installedHypotheses := installedDomains.drop A.rule.allArgs.size
  have hfieldLE : A.rule.allArgs.size ≤ arity := by
    dsimp only [arity]
    omega
  have hreplayedFields : replayedFields.length = A.rule.allArgs.size := by
    simp [replayedFields, hreplayedLength, Nat.min_eq_left hfieldLE]
  have hfullFields : fullFields.length = A.rule.allArgs.size := by
    simp [fullFields, hfullLength, Nat.min_eq_left hfieldLE]
  have hnarrowFields : narrowFields.length = A.rule.allArgs.size := by
    simp [narrowFields, hnarrowLength, Nat.min_eq_left hfieldLE]
  have hweakenedFields : weakenedFields.length = A.rule.allArgs.size := by
    simp [weakenedFields, hweakenedLength, Nat.min_eq_left hfieldLE]
  have hinstalledFields : installedFields.length = A.rule.allArgs.size := by
    simp [installedFields, hinstalledLength, Nat.min_eq_left hfieldLE]
  have hinstalledHypotheses : installedHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [installedHypotheses, hinstalledLength]
  have hinstalledSplit : installedDomains =
      installedFields ++ installedHypotheses := by
    exact (List.take_append_drop A.rule.allArgs.size installedDomains).symm
  have HfieldContexts :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads Hcontexts
      A.rule.recursiveArgs.size
  have hreplayedDrop :
      (replayedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx).drop
          A.rule.recursiveArgs.size =
        replayedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx := by
    have hsplit := (List.take_append_drop A.rule.allArgs.size
      replayedDomains).symm
    rw [hsplit, List.reverse_append]
    have hsuffix : (replayedDomains.drop A.rule.allArgs.size).length =
        A.rule.recursiveArgs.size := by
      rw [List.length_drop, hreplayedLength]
      dsimp only [arity]
      exact Nat.add_sub_cancel_left _ _
    simpa [replayedFields, List.append_assoc, hsuffix] using
      List.drop_left' (replayedDomains.drop A.rule.allArgs.size).reverse
        (replayedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
  have hfullDrop :
      (fullDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx).drop
          A.rule.recursiveArgs.size =
        fullFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx := by
    have hsplit := (List.take_append_drop A.rule.allArgs.size
      fullDomains).symm
    rw [hsplit, List.reverse_append]
    have hsuffix : (fullDomains.drop A.rule.allArgs.size).length =
        A.rule.recursiveArgs.size := by
      rw [List.length_drop, hfullLength]
      exact Nat.add_sub_cancel_left _ _
    simpa [fullFields, List.append_assoc, hsuffix] using
      List.drop_left' (fullDomains.drop A.rule.allArgs.size).reverse
        (fullFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
  rw [hreplayedDrop, hfullDrop] at HfieldContexts
  have hweakenedDrop :
      (weakenedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx).drop
          A.rule.recursiveArgs.size =
        weakenedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx := by
    have hsplit := (List.take_append_drop A.rule.allArgs.size
      weakenedDomains).symm
    rw [hsplit, List.reverse_append]
    have hsuffix : (weakenedDomains.drop A.rule.allArgs.size).length =
        A.rule.recursiveArgs.size := by
      rw [List.length_drop, hweakenedLength]
      exact Nat.add_sub_cancel_left _ _
    simpa [weakenedFields, List.append_assoc, hsuffix] using
      List.drop_left' (weakenedDomains.drop A.rule.allArgs.size).reverse
        (weakenedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
  have HfullWeakened :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads HnarrowFull
      A.rule.recursiveArgs.size
  rw [hfullDrop, hweakenedDrop] at HfullWeakened
  have HnarrowInstalledFields :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads HnarrowInstalled
      A.rule.recursiveArgs.size
  have hnarrowDrop :
      (narrowDomains.reverse ++ scope.toCtx).drop
          A.rule.recursiveArgs.size =
        narrowFields.reverse ++ scope.toCtx := by
    have hsplit := (List.take_append_drop A.rule.allArgs.size
      narrowDomains).symm
    rw [hsplit, List.reverse_append]
    have hsuffix : (narrowDomains.drop A.rule.allArgs.size).length =
        A.rule.recursiveArgs.size := by
      rw [List.length_drop, hnarrowLength]
      exact Nat.add_sub_cancel_left _ _
    simpa [narrowFields, List.append_assoc, hsuffix] using
      List.drop_left' (narrowDomains.drop A.rule.allArgs.size).reverse
        (narrowFields.reverse ++ scope.toCtx)
  have hinstalledDrop :
      (installedDomains.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse).drop
          A.rule.recursiveArgs.size =
        installedFields.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    rw [hinstalledSplit, List.reverse_append]
    simpa [List.append_assoc, hinstalledHypotheses] using
      List.drop_left' installedHypotheses.reverse
        (installedFields.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse)
  rw [hnarrowDrop, hinstalledDrop] at HnarrowInstalledFields
  have hreplayedFieldsExact : replayedFields =
      liftForallDomains HS.semantic.fieldDomains (Hext.shift.consN 0) := by
    dsimp only [replayedFields, replayedDomains, semanticDomains]
    rw [← hfields, ← hsemanticFields]
    exact liftForallDomains_append_take_left _ _ _
  have hminorConsumedExact :
      liftForallDomains HS.semantic.fieldDomains (Hext.shift.consN 0) =
        minorConsumedDomains := by
    have hminorConsumedLength : minorConsumedDomains.length =
        HS.semantic.fieldDomains.length :=
      hminorConsumed.trans (hsemanticFields.trans hfields).symm
    have Hlift := VExpr.lift'_wrapForalls_exact
      HS.semantic.fieldDomains HS.semantic.terminalTarget
        (Hext.shift.consN 0)
    have Hwrapped := Hlift.symm.trans hminorTarget
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      (liftForallDomains_length _ _) hminorConsumedLength
      (by simpa using Hwrapped)
  rw [hreplayedFieldsExact, hminorConsumedExact] at HfieldContexts
  have HfullConsumed := HfieldContexts.symm H.outVEnvWF.ordered
  have HfullNarrow := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HfullConsumed HminorNarrow
  have hallWeakened : liftForallDomains narrowDomains Hscope.shift =
      weakenedDomains := by
    have Hlift := VExpr.lift'_wrapForalls_exact
      narrowDomains narrowResidual Hscope.shift
    have Hwrapped := Hlift.symm.trans hweakenedTarget
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      (liftForallDomains_length _ _)
      (hweakenedLength.trans hnarrowLength.symm)
      (by simpa using Hwrapped)
  have hweakenedFieldsExact : weakenedFields =
      liftForallDomains narrowFields Hscope.shift := by
    dsimp only [weakenedFields, narrowFields]
    rw [← hallWeakened]
    have Htake := liftForallDomains_append_take_left
      (narrowDomains.take A.rule.allArgs.size)
      (narrowDomains.drop A.rule.allArgs.size) Hscope.shift
    rw [List.take_append_drop] at Htake
    rw [hnarrowFields] at Htake
    exact Htake
  have HweakenedNarrow := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (HfullWeakened.symm H.outVEnvWF.ordered) HfullNarrow
  exact ⟨T, scope, Hscope, narrowFields, weakenedFields, fullFields,
    installedFields, installedHypotheses, installedResidual,
    hscope, hscopeShift, hnarrowFields, hweakenedFields, hfullFields,
    hinstalledFields,
    hinstalledHypotheses, hweakenedFieldsExact,
    by simpa [hinstalledSplit] using hinstalledTarget, Hprefix,
    HnarrowInstalledFields, HweakenedNarrow⟩

/-- Apply the selected installed minor to the canonical constructor-field
variables in the independently replayed field context, while retaining the
same replay witness's comparison with the fixed narrow runtime frame.  This
is the synchronized starting point for the recursive-result application
fold: neither the recursor telescope nor the field representatives can drift
between the typed application and the runtime alignment. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationWithNarrowFrame
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
    (B : A.NarrowFieldRuntimeFrame)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope : VLCtx,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowFields weakenedFields hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        narrowFields.length = A.rule.allArgs.size ∧
        weakenedFields.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        weakenedFields = liftForallDomains narrowFields Hscope.shift ∧
        let later := T.minors.drop (minorIdx + 1)
        let shift := later.length + 1
        let liftedFields :=
          (liftContextPrefix shift narrowFields.reverse).reverse
        let liftedHypotheses :=
          (liftContextPrefixAt shift narrowFields.length
            hypothesisDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
            (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
          H.outVEnv.HasType Us.length
            (liftedFields.reverse ++
              (T.params ++ T.motives ++ T.minors).reverse)
            (VExpr.mkApps
              ((.bvar later.length : VExpr).liftN liftedFields.length 0)
              (recursorCanonicalVars liftedFields.length))
            (VExpr.wrapForalls liftedHypotheses
              (targetResidual.liftN shift
                (narrowFields.length + hypothesisDomains.length))) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (weakenedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
            B.runtime.expanded.toCtx := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorFullFieldAlignmentWithNarrowFrame
      B hpositive with
    ⟨T, scope, Hscope, narrowFields, weakenedFields, _fullFields,
      installedFields, installedHypotheses, installedResidual,
      hscope, hscopeShift, hnarrowFields, hweakenedFields, _hfullFields,
      hinstalledFields, hinstalledHypotheses, hweakenedExact,
      hinstalledTarget, Hprefix,
      HnarrowInstalled, HweakenedNarrow⟩
  rcases A.finalSelectedMinorFieldApplication with
    ⟨T₁, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, htarget, Happlication⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hminors] at htarget
  rw [hparams, hmotives, hminors] at Happlication
  have hfieldDomains : fieldDomains = installedFields := by
    apply VExpr.wrapForalls_prefix_domains_eq hfields hinstalledFields
    have hwhole := htarget.symm.trans hinstalledTarget
    simpa [VExpr.wrapForalls_append] using hwhole
  subst fieldDomains
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  let remaining := (T.minors.drop minorIdx).reverse
  have HsameNarrow :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hprefix HnarrowInstalled.isType
  have HsameBase := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (HsameNarrow.symm H.outVEnvWF.ordered) HnarrowInstalled
  have Hremaining : OnCtx (remaining ++ base.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hprefix := T.prefixContext H.outVEnvWF.ordered
    have hminors := List.take_append_drop minorIdx T.minors
    have hreverse : T.minors.reverse =
        (T.minors.drop minorIdx).reverse ++
          (T.minors.take minorIdx).reverse := by
      simpa only [List.reverse_append] using
        (congrArg List.reverse hminors).symm
    simp only [List.reverse_append] at Hprefix
    rw [hreverse] at Hprefix
    simpa [base, remaining, List.reverse_append, List.append_assoc] using
      Hprefix
  have Hfull := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered narrowFields.reverse installedFields.reverse
      remaining base.reverse (by simpa [base] using HsameBase)
      (by simp [hnarrowFields, hinstalledFields]) Hremaining
  let later := T.minors.drop (minorIdx + 1)
  let shift := later.length + 1
  let liftedFields :=
    (liftContextPrefix shift narrowFields.reverse).reverse
  let liftedHypotheses :=
    (liftContextPrefixAt shift narrowFields.length
      hypothesisDomains.reverse).reverse
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hdrop : T.minors.drop minorIdx =
      T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : remaining.length = shift := by
    simp [remaining, hdrop, shift]
  have hfullContext : remaining ++ base.reverse =
      (T.params ++ T.motives ++ T.minors).reverse := by
    have hminorPrefix : (T.minors.drop minorIdx).reverse ++
        (T.minors.take minorIdx).reverse = T.minors.reverse := by
      simpa only [List.reverse_append] using congrArg List.reverse
        (List.take_append_drop minorIdx T.minors)
    simp only [remaining, base, List.reverse_append]
    rw [← List.append_assoc, hminorPrefix]
  have Hcontext : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftedFields.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse)
      (liftContextPrefix shift installedFields.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse) := by
    rw [hremainingLength] at Hfull
    simp only [List.append_assoc] at Hfull
    rw [hfullContext] at Hfull
    simpa [liftedFields] using Hfull
  simp only [List.reverse_reverse] at Happlication
  have Htransported := Happlication.defeqDFC H.outVEnvWF.ordered
    (Hcontext.symm H.outVEnvWF.ordered)
  exact ⟨T, scope, Hscope, narrowFields, weakenedFields,
    hypothesisDomains, targetResidual, hscope, hscopeShift,
    hnarrowFields, hweakenedFields, hhypotheses, hweakenedExact, by
      exact Hprefix,
    by
      simpa [later, shift, liftedFields, liftedHypotheses,
        hinstalledFields, hnarrowFields] using Htransported,
    HweakenedNarrow⟩

/-- Witness-stable specialization of
`finalSelectedMinorFieldApplicationWithNarrowFrame`.  A recursive-result
fold already carries one generated recursor telescope, so the field-applied
minor must be transported to that exact witness before any dependent
hypothesis domains are compared. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationWithNarrowFrameFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ scope : VLCtx,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowFields weakenedFields hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        narrowFields.length = A.rule.allArgs.size ∧
        weakenedFields.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        weakenedFields = liftForallDomains narrowFields Hscope.shift ∧
        let later := T.minors.drop (minorIdx + 1)
        let shift := later.length + 1
        let liftedFields :=
          (liftContextPrefix shift narrowFields.reverse).reverse
        let liftedHypotheses :=
          (liftContextPrefixAt shift narrowFields.length
            hypothesisDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
            (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
          H.outVEnv.HasType Us.length
            (liftedFields.reverse ++
              (T.params ++ T.motives ++ T.minors).reverse)
            (VExpr.mkApps
              ((.bvar later.length : VExpr).liftN liftedFields.length 0)
              (recursorCanonicalVars liftedFields.length))
            (VExpr.wrapForalls liftedHypotheses
              (targetResidual.liftN shift
                (narrowFields.length + hypothesisDomains.length))) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (weakenedFields.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
            B.runtime.expanded.toCtx := by
  dsimp only
  rcases A.finalSelectedMinorFieldApplicationWithNarrowFrame B hpositive with
    ⟨T₁, scope, Hscope, narrowFields, weakenedFields,
      hypothesisDomains, targetResidual, hscope, hscopeShift,
      hnarrowFields, hweakenedFields, hhypotheses, hweakenedExact,
      Hprefix, Happlication,
      HweakenedNarrow⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at Hprefix
  rw [hparams, hmotives, hminors] at Happlication
  exact ⟨scope, Hscope, narrowFields, weakenedFields,
    hypothesisDomains, targetResidual, hscope, hscopeShift,
    hnarrowFields, hweakenedFields, hhypotheses, hweakenedExact,
    Hprefix, Happlication,
    HweakenedNarrow⟩

/-- The independently replayed selected-minor fields and the source-stable
complete-outer fields agree after each is weakened back into the executable
recursor context.  Both comparisons pass through the literal semantic field
telescope, so no syntactic identity of translated dependent domains is
assumed. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedOuterRuntimeFieldAlignmentFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    let remainingBinders := H.bindings.flatMinors.fvars.drop minorIdx
    ∃ selectedScope,
    ∃ Hselected : checkInductiveTypes.loopType.FVarNarrowScope
        H.outVEnv Us selectedScope H.recursorWF.mlctx.vlctx,
    ∃ outerScope,
    ∃ Houter : checkInductiveTypes.loopType.FVarNarrowScope
        H.outVEnv Us outerScope H.recursorWF.mlctx.vlctx,
    ∃ selectedFields outerFields hypothesisDomains : List VExpr,
    ∃ targetResidual outerResidual : VExpr,
      selectedScope.fvars = sourceBinders.reverse ∧
      Hselected.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ sourceBinders) ∧
      outerScope.fvars = outerBinders.reverse ∧
      Houter.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ outerBinders) ∧
      outerScope.fvars =
        remainingBinders.reverse ++ selectedScope.fvars ∧
      Lift.comp
          (fvarSelectionLift outerScope.fvars
            (· ∈ selectedScope.fvars)) Houter.shift =
        Hselected.shift ∧
      fvarSelectionLift outerScope.fvars (· ∈ selectedScope.fvars) =
        .skipN (.consN .refl selectedScope.fvars.length)
          remainingBinders.length ∧
      selectedFields.length = A.rule.allArgs.size ∧
      outerFields.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      TrExprS H.outVEnv Us outerScope A.semantics.parameterTail
        (VExpr.wrapForalls outerFields outerResidual) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length [] selectedScope.toCtx
        (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length [] outerScope.toCtx
        (T.params ++ T.motives ++ T.minors).reverse ∧
      (let later := T.minors.drop (minorIdx + 1)
       let shift := later.length + 1
       let liftedFields :=
         (liftContextPrefix shift selectedFields.reverse).reverse
       let liftedHypotheses :=
         (liftContextPrefixAt shift selectedFields.length
           hypothesisDomains.reverse).reverse
       H.outVEnv.HasType Us.length
         (liftedFields.reverse ++
           (T.params ++ T.motives ++ T.minors).reverse)
         (VExpr.mkApps
           ((.bvar later.length : VExpr).liftN liftedFields.length 0)
           (recursorCanonicalVars liftedFields.length))
         (VExpr.wrapForalls liftedHypotheses
           (targetResidual.liftN shift
             (selectedFields.length + hypothesisDomains.length)))) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((liftForallDomains selectedFields
          (fvarSelectionLift outerScope.fvars
            (· ∈ selectedScope.fvars))).reverse ++ outerScope.toCtx)
        (outerFields.reverse ++ outerScope.toCtx) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((liftForallDomains selectedFields Hselected.shift).reverse ++
          H.recursorWF.mlctx.vlctx.toCtx)
        ((liftForallDomains outerFields Houter.shift).reverse ++
          H.recursorWF.mlctx.vlctx.toCtx) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  let remainingBinders := H.bindings.flatMinors.fvars.drop minorIdx
  rcases A.finalSelectedMinorFieldApplicationWithNarrowFrameFor
      B T hpositive with
    ⟨selectedScope, Hselected, selectedFields, weakenedFields,
      hypothesisDomains, targetResidual, hselectedScope,
      hselectedShift, hselectedFields, _hweakenedFields,
      hhypotheses, hweakenedExact,
      HselectedPrefix, Happlication, HselectedNarrow⟩
  rcases A.finalOuterConstructorFieldRuntimeAlignmentFor T with
    ⟨outerScope, Houter, outerFields, outerResidual, houterScope,
      houterShift, houterFields, HouterTail, _HouterType,
      HouterPrefix, HouterSemantic⟩
  rcases B.semanticFieldContext with
    ⟨_hsemanticFields, _hsemanticContext, _hexpandedLength,
      _hexpandedContext, _HfieldBase, HexpandedSemantic⟩
  have HexpandedSemantic' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      B.runtime.expanded.toCtx
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    simpa [A.semantics.fieldRoot_vlctx] using HexpandedSemantic
  have HselectedSemantic := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HselectedNarrow HexpandedSemantic'
  have HselectedOuter := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HselectedSemantic (HouterSemantic.symm H.outVEnvWF.ordered)
  rw [hweakenedExact] at HselectedOuter
  have houterSplit : outerBinders = sourceBinders ++ remainingBinders := by
    simp only [outerBinders, sourceBinders, remainingBinders,
      List.append_assoc, List.take_append_drop]
  have hscopeSplit : outerScope.fvars =
      remainingBinders.reverse ++ selectedScope.fvars := by
    calc
      outerScope.fvars = outerBinders.reverse := houterScope
      _ = (sourceBinders ++ remainingBinders).reverse :=
        congrArg List.reverse houterSplit
      _ = remainingBinders.reverse ++ sourceBinders.reverse := by
        rw [List.reverse_append]
      _ = remainingBinders.reverse ++ selectedScope.fvars := by
        rw [hselectedScope]
  have hselectionSub : ∀ fv,
      fv ∈ sourceBinders → fv ∈ outerBinders := by
    intro fv hfv
    rw [houterSplit]
    exact List.mem_append_left _ hfv
  have hfactor := fvarSelectionLift_mono_comp
    H.recursorWF.mlctx.vlctx.fvars
      (· ∈ sourceBinders) (· ∈ outerBinders) hselectionSub
  rw [A.finalOuterFilteredFVars] at hfactor
  rw [← houterScope, ← hselectedShift, ← houterShift] at hfactor
  have hfactor' : Lift.comp
      (fvarSelectionLift outerScope.fvars
        (· ∈ selectedScope.fvars)) Houter.shift = Hselected.shift := by
    simpa only [hselectedScope, List.mem_reverse] using hfactor
  have hscopeNodup :
      (remainingBinders.reverse ++ selectedScope.fvars).Nodup := by
    rw [← hscopeSplit]
    exact (Houter.scopeWF H.outVEnvWF).fvars_nodup
  have hrelative := fvarSelectionLift_append_selected
    remainingBinders.reverse selectedScope.fvars
      (by
        intro fv hremaining hselected
        exact (List.nodup_append.mp hscopeNodup).2.2
          fv hremaining fv hselected rfl)
  rw [← hscopeSplit] at hrelative
  simp only [List.length_reverse] at hrelative
  have hselectedComposed :
      liftForallDomains selectedFields Hselected.shift =
        liftForallDomains
          (liftForallDomains selectedFields
            (fvarSelectionLift outerScope.fvars
              (· ∈ selectedScope.fvars))) Houter.shift := by
    rw [← hfactor', ← liftForallDomains_comp]
  have HselectedOuterExpanded := VEnv.IsDefEqCtx.rebaseCommonSuffix
    H.outVEnvWF Houter.context.defeqCtx HselectedOuter
  rw [hselectedComposed] at HselectedOuterExpanded
  have HselectedOuterNatural :=
    VEnv.IsDefEqCtx.cancelLiftForallDomains H.outVEnvWF
      Houter.lift.toCtx HselectedOuterExpanded
  exact ⟨selectedScope, Hselected, outerScope, Houter,
    selectedFields, outerFields, hypothesisDomains, targetResidual,
    outerResidual,
    hselectedScope, hselectedShift,
    houterScope, houterShift, hscopeSplit, hfactor', hrelative,
    hselectedFields, houterFields, hhypotheses, HouterTail,
    HselectedPrefix, HouterPrefix, Happlication,
    HselectedOuterNatural, HselectedOuter⟩

/-- Rewrite the selected-within-outer free-variable embedding as the ordinary
generated-prefix weakening and transport the canonical field application to
the complete outer constructor-field telescope.  All witnesses come from
`finalSelectedOuterRuntimeFieldAlignmentFor`, so the typed application and
the cancelled field conversion cannot choose different translations. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationInCompleteOuterContextFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ outerFields hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
      outerFields.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      let later := T.minors.drop (minorIdx + 1)
      let shift := later.length + 1
      let liftedHypotheses :=
        (liftContextPrefixAt shift outerFields.length
          hypothesisDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (outerFields.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse)
        (VExpr.mkApps
          ((.bvar later.length : VExpr).liftN outerFields.length 0)
          (recursorCanonicalVars outerFields.length))
        (VExpr.wrapForalls liftedHypotheses
          (targetResidual.liftN shift
            (outerFields.length + hypothesisDomains.length))) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let remainingBinders := H.bindings.flatMinors.fvars.drop minorIdx
  rcases A.finalSelectedOuterRuntimeFieldAlignmentFor B T hpositive with
    ⟨selectedScope, Hselected, outerScope, Houter,
      selectedFields, outerFields, hypothesisDomains, targetResidual,
      _outerResidual,
      _hselectedScope, _hselectedShift, _houterScope, _houterShift,
      hscopeSplit, _hfactor, hrelative, hselectedFields, houterFields,
      hhypotheses, _HouterTail, HselectedPrefix, HouterPrefix, Happlication,
      Hnatural, _Hruntime⟩
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hscopeLengths := congrArg List.length hscopeSplit
  have houterPrefixLengths := HouterPrefix.length_eq
  have hselectedPrefixLengths := HselectedPrefix.length_eq
  have hremainingLength : remainingBinders.length =
      (T.minors.drop minorIdx).length := by
    have houterScopeLength : outerScope.fvars.length =
        outerScope.toCtx.length :=
      Houter.fvars_length.trans Houter.toCtx_length.symm
    have hselectedScopeLength : selectedScope.fvars.length =
        selectedScope.toCtx.length :=
      Hselected.fvars_length.trans Hselected.toCtx_length.symm
    have houterPrefixLength : outerScope.toCtx.length =
        T.minors.length + (T.motives.length + T.params.length) := by
      simpa using houterPrefixLengths
    have hselectedPrefixLength : selectedScope.toCtx.length =
        minorIdx + (T.motives.length + T.params.length) := by
      simpa [minorIdx, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hminor)] using hselectedPrefixLengths
    have hscopeLength : outerScope.fvars.length =
        remainingBinders.length + selectedScope.fvars.length := by
      simpa [remainingBinders] using hscopeLengths
    simp only [List.length_drop]
    omega
  let later := T.minors.drop (minorIdx + 1)
  let shift := later.length + 1
  have hdrop : T.minors.drop minorIdx = T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hgeneratedRemaining : (T.minors.drop minorIdx).length = shift := by
    simp [hdrop, shift]
  have Hnatural' := Hnatural
  rw [hrelative, liftForallDomains_skipN_consN_refl,
    hremainingLength, hgeneratedRemaining] at Hnatural'
  have HfieldsFull := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HouterPrefix.symm H.outVEnvWF.ordered) Hnatural'
  have Htransported := Happlication.defeqDFC H.outVEnvWF.ordered
    HfieldsFull
  exact ⟨outerFields, hypothesisDomains, targetResidual,
    houterFields, hhypotheses, by
      simpa [later, shift, hselectedFields, houterFields] using Htransported⟩

/-- The source-stable fields reconstructed in the complete generated outer
scope agree with the independently checked constructor fields after the
motive/minor block is inserted.  The comparison is made only after both
translations are weakened into the executable recursor context; factoring
the parameter selection through the outer selection then lets us cancel the
common non-contiguous weakening. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterCheckedEquationFieldAlignmentFor
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
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (outerScope : VLCtx)
    (Houter : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      outerScope H.recursorWF.mlctx.vlctx)
    (outerFields : List VExpr) (outerResidual : VExpr)
    (houterScope : outerScope.fvars =
      (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars).reverse)
    (houterShift : Houter.shift = fvarSelectionLift
      H.recursorWF.mlctx.vlctx.fvars
      (· ∈ H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars))
    (houterFields : outerFields.length = A.rule.allArgs.size)
    (HouterTail : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      outerScope A.semantics.parameterTail
      (VExpr.wrapForalls outerFields outerResidual))
    (HouterPrefix : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      outerScope.toCtx (T.params ++ T.motives ++ T.minors).reverse)
    (checkedDomains : List VExpr) (checkedResidual : VExpr)
    (hcheckedFields : checkedDomains.length = A.rule.allArgs.size)
    (HcheckedTail : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let inserted := T.motives ++ T.minors
    ∃ equationFieldDomains : List VExpr,
      equationFieldDomains =
        (liftContextPrefix inserted.length checkedDomains.reverse).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (outerFields.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse)
        (equationFieldDomains.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let inserted := T.motives ++ T.minors
  let parameterBinders := H.params.fvars
  let insertedBinders := H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  let outerBinders := parameterBinders ++ insertedBinders
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hfieldRootEnv : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv :=
    A.semantics.fieldsRecent.venv_eq.symm.trans
      A.semantics.context_venv
  have Hruntime : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail A.semantics.parameterTarget := by
    have Htr := A.semantics.parameterTranslation
    rw [hfieldRootEnv, A.semantics.fieldRoot_vlctx] at Htr
    exact Htr.mono hbase
  have HruntimeWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf
  let Hparameter := (H.parameterSuffix.runtimeScope).mono hbase
  have HcheckedWhole := Hparameter.fullTargetEq H.outVEnvWF
    HcheckedTail (Hruntime.trExpr H.outVEnvWF HruntimeWF)
  have HouterWhole := Houter.fullTargetEq H.outVEnvWF HouterTail
    (Hruntime.trExpr H.outVEnvWF HruntimeWF)
  have Hwhole : H.outVEnv.IsDefEqU Us.length
      H.recursorWF.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls checkedDomains checkedResidual).lift'
        Hparameter.shift)
      ((VExpr.wrapForalls outerFields outerResidual).lift'
        Houter.shift) :=
    HcheckedWhole.trans H.outVEnvWF HruntimeWF.toCtx HouterWhole.symm
  rw [VExpr.lift'_wrapForalls_exact,
    VExpr.lift'_wrapForalls_exact] at Hwhole
  have HruntimeBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx
      H.recursorWF.mlctx.vlctx.toCtx := .refl HruntimeWF.toCtx
  have HruntimeFields := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF HruntimeBase
      ((liftForallDomains_length checkedDomains Hparameter.shift).trans
        ((hcheckedFields.trans houterFields.symm).trans
          (liftForallDomains_length outerFields Houter.shift).symm)) Hwhole
  have hparameterFVars : H.parameterSuffix.parameterDecls.fvars =
      parameterBinders.reverse := by
    rw [H.parameterSuffix.parameterDecls_fvars]
    simpa only [parameterBinders] using
      congrArg List.reverse H.params.exprArrayFVarIds
  have houterScope' : outerScope.fvars = outerBinders.reverse := by
    simpa [outerBinders, parameterBinders, insertedBinders,
      List.append_assoc] using houterScope
  have houterShift' : Houter.shift =
      fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ outerBinders) := by
    simpa [outerBinders, parameterBinders, insertedBinders,
      List.append_assoc] using houterShift
  have houterSplit : outerScope.fvars =
      insertedBinders.reverse ++ H.parameterSuffix.parameterDecls.fvars := by
    calc
      outerScope.fvars = outerBinders.reverse := houterScope'
      _ = insertedBinders.reverse ++ parameterBinders.reverse := by
        rw [List.reverse_append]
      _ = insertedBinders.reverse ++
          H.parameterSuffix.parameterDecls.fvars := by
        rw [hparameterFVars]
  have houterNodup :
      (insertedBinders.reverse ++
        H.parameterSuffix.parameterDecls.fvars).Nodup := by
    rw [← houterSplit]
    exact (Houter.scopeWF H.outVEnvWF).fvars_nodup
  have hrelativeBase := fvarSelectionLift_append_selected
    insertedBinders.reverse H.parameterSuffix.parameterDecls.fvars
      (by
        intro fv hinserted hparameter
        exact (List.nodup_append.mp houterNodup).2.2
          fv hinserted fv hparameter rfl)
  have hrelative : fvarSelectionLift outerScope.fvars
      (· ∈ parameterBinders) =
        .skipN (.consN .refl
          H.parameterSuffix.parameterDecls.fvars.length)
          insertedBinders.length := by
    rw [houterSplit]
    simpa only [hparameterFVars, List.mem_reverse,
      List.length_reverse] using hrelativeBase
  have hparameterSub : ∀ fv,
      fv ∈ parameterBinders → fv ∈ outerBinders := by
    intro fv hfv
    exact List.mem_append_left _ hfv
  have hfactor := fvarSelectionLift_mono_comp
    H.recursorWF.mlctx.vlctx.fvars
      (· ∈ parameterBinders) (· ∈ outerBinders) hparameterSub
  have houterFiltered : H.recursorWF.mlctx.vlctx.fvars.filter
      (· ∈ outerBinders) = outerBinders.reverse := by
    simpa [outerBinders, parameterBinders, insertedBinders,
      List.append_assoc] using A.finalOuterFilteredFVars
  rw [houterFiltered] at hfactor
  have hfactor' : Lift.comp
      (fvarSelectionLift outerScope.fvars (· ∈ parameterBinders))
        Houter.shift =
      fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ parameterBinders) := by
    rw [houterScope', houterShift']
    exact hfactor
  have hruntimeFVars : H.recursorWF.mlctx.vlctx.fvars =
      H.parameterSuffix.ambientDecls.fvars ++
        H.parameterSuffix.parameterDecls.fvars := by
    rw [H.parameterSuffix.context, VLCtx.fvars_append]
  have hruntimeNodup :
      (H.parameterSuffix.ambientDecls.fvars ++
        H.parameterSuffix.parameterDecls.fvars).Nodup := by
    rw [← hruntimeFVars]
    exact HruntimeWF.fvars_nodup
  have hparameterSelectionBase := fvarSelectionLift_append_selected
    H.parameterSuffix.ambientDecls.fvars
      H.parameterSuffix.parameterDecls.fvars
      (by
        intro fv hambient hparameter
        exact (List.nodup_append.mp hruntimeNodup).2.2
          fv hambient fv hparameter rfl)
  have hparameterSelection :
      fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ parameterBinders) =
        .skipN (.consN .refl
          H.parameterSuffix.parameterDecls.fvars.length)
          H.parameterSuffix.ambientDecls.fvars.length := by
    rw [hruntimeFVars]
    simpa only [hparameterFVars, List.mem_reverse] using
      hparameterSelectionBase
  have hparameterToCtxLength :
      H.parameterSuffix.parameterDecls.toCtx.length =
        H.parameterSuffix.parameterDecls.length :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
      H.parameterSuffix.cached
  have hparameterFVarsLength :
      H.parameterSuffix.parameterDecls.fvars.length =
        H.parameterSuffix.parameterDecls.length := by
    rw [hparameterFVars, List.length_reverse,
      H.params.length_fvars,
      H.parameterSuffix.parameterDecls_length]
  have hruntimeToCtxLength := H.recursorWF.onlyLams.toCtx_length
  have hruntimeFVarsLength := H.recursorWF.onlyLams.fvars_length
  have htoCtxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterSuffix.context
  have hfvarParts := congrArg List.length hruntimeFVars
  simp only [VLCtx.toCtx_append, List.length_append] at htoCtxParts
  simp only [List.length_append] at hfvarParts
  have hambientLengths : H.parameterSuffix.ambientDecls.toCtx.length =
      H.parameterSuffix.ambientDecls.fvars.length := by
    omega
  have hparameterShift : Hparameter.shift =
      .skipN .refl H.parameterSuffix.ambientDecls.toCtx.length := rfl
  have hparameterRuntime :
      liftForallDomains checkedDomains Hparameter.shift =
        liftForallDomains checkedDomains
          (fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
            (· ∈ parameterBinders)) := by
    rw [hparameterShift, liftForallDomains_skipN_refl,
      hparameterSelection, liftForallDomains_skipN_consN_refl,
      hambientLengths]
  have hcheckedComposed :
      liftForallDomains checkedDomains Hparameter.shift =
        liftForallDomains
          (liftForallDomains checkedDomains
            (fvarSelectionLift outerScope.fvars
              (· ∈ parameterBinders))) Houter.shift := by
    rw [liftForallDomains_comp, hfactor']
    exact hparameterRuntime
  have Hexpanded := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    Houter.context.defeqCtx HruntimeFields
  rw [hcheckedComposed] at Hexpanded
  have Hnatural := VEnv.IsDefEqCtx.cancelLiftForallDomains
    H.outVEnvWF Houter.lift.toCtx Hexpanded
  have hinsertedLengths : insertedBinders.length = inserted.length := by
    simp only [insertedBinders, inserted, List.length_append]
    rw [H.bindings.motives.length_fvars,
      H.bindings.flatMinors.length_fvars,
      T.motives_length, T.minors_length]
  rw [hrelative, liftForallDomains_skipN_consN_refl,
    hinsertedLengths] at Hnatural
  let equationFieldDomains :=
    (liftContextPrefix inserted.length checkedDomains.reverse).reverse
  have Hfull := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HouterPrefix.symm H.outVEnvWF.ordered) Hnatural
  exact ⟨equationFieldDomains, rfl, by
      simpa [equationFieldDomains, inserted] using
        (Hfull.symm H.outVEnvWF.ordered)⟩

/-- Compose the selected minor's transported consumed fields with the
rule-wide narrowing conversion.  The result relates the literal first-pass
field suffix to the expanded narrow context used by the canonical recursive
results, with no call-local declarations present. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedFieldAlignment
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ minorConsumedDomains : List VExpr,
          minorConsumedDomains.length = A.rule.allArgs.size ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (minorConsumedDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx)
            B.runtime.expanded.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSemanticFieldAlignment with
    ⟨S, HS, minorConsumedDomains, hminor, _hrule, Hminor⟩
  rcases B.semanticFieldContext with
    ⟨_hrule', _hsemanticContext, _hexpandedLength,
      _hexpandedContext, _HfieldBase, Hexpanded⟩
  have Hexpanded' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      B.runtime.expanded.toCtx
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    simpa [A.semantics.fieldRoot_vlctx] using Hexpanded
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF Hminor
    (Hexpanded'.symm H.outVEnvWF.ordered)
  exact ⟨S, HS, minorConsumedDomains, hminor, Haligned⟩

/-- Retain the untranslated source telescope while composing the selected
minor's field conversion with the rule-wide narrowing conversion.  This is
the cancellation-facing form of `finalSelectedMinorExpandedFieldAlignment`:
the source translation and the final expanded context now belong to one
existential witness, so no choice of intermediate consumed domains is lost. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedSourceFieldAlignment
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ sourceDomains sourceResidual,
          sourceDomains.length = A.rule.allArgs.size ∧
          HS.semantic.traversal.parameterTail =
            A.semantics.parameterTail ∧
          TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
            A.semantics.parameterTail
            (VExpr.wrapForalls sourceDomains sourceResidual) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (sourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
            B.runtime.expanded.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorTransportedFieldContext with
    ⟨S, HS, sourceDomains, sourceResidual, consumedDomains,
      _consumedResidual, _hlocal, htail, hsource, hconsumed,
      Hsource, _hconsumedTarget, HsourceConsumed⟩
  rcases A.semantics.fieldContextDefEq with
    ⟨ruleSourceDomains, ruleSourceResidual, hruleSource,
      hparameterTarget, HruleContexts⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have HruleSource₀ : TrExprS A.semantics.fieldRootContext.venv Us
      A.semantics.fieldRootContext.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    rw [← hparameterTarget]
    exact A.semantics.parameterTranslation
  have hsemanticRoot : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv := by
    exact A.semantics.fieldsRecent.venv_eq.symm.trans
      A.semantics.context_venv
  rw [hsemanticRoot] at HruleSource₀ HruleContexts
  have HruleSource : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    have Hsource' := HruleSource₀.mono hbase
    simpa [A.semantics.fieldRoot_vlctx] using Hsource'
  have Hsource' := Hsource.mono hbase
  have HrootWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf
  have HsourceTarget := Hsource'.uniq H.outVEnvWF
    (.refl H.outVEnvWF HrootWF) HruleSource
  have HrootBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HrootWF.toCtx
  have HsourceRule := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF HrootBase (hsource.trans hruleSource.symm) HsourceTarget
  have HsourceConsumed' := HsourceConsumed.mono hbase
  have HruleContexts' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (ruleSourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    have Hcontexts := HruleContexts.mono hbase
    simpa [A.semantics.fieldRoot_vlctx] using Hcontexts
  have HconsumedSource := HsourceConsumed'.symm H.outVEnvWF.ordered
  have HconsumedRuleSource := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HconsumedSource HsourceRule
  have HconsumedSemantic := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HconsumedRuleSource HruleContexts'
  rcases B.semanticFieldContext with
    ⟨_hrule, _hsemanticContext, _hexpandedLength,
      _hexpandedContext, _HfieldBase, Hexpanded⟩
  have Hexpanded' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      B.runtime.expanded.toCtx
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    simpa [A.semantics.fieldRoot_vlctx] using Hexpanded
  have HconsumedExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HconsumedSemantic (Hexpanded'.symm H.outVEnvWF.ordered)
  have HsourceExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HsourceConsumed' HconsumedExpanded
  exact ⟨S, HS, sourceDomains, sourceResidual, hsource, htail,
    Hsource', HsourceExpanded⟩

/-- Cancel the rule-wide free-variable embedding and compare the selected
minor's constructor fields with the literal narrow field telescope in the
cached parameter scope.  This is the exact field-domain equality required
before the installed minor can be applied to canonical recursive results. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorNarrowFieldAlignment
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ narrowDomains narrowResidual,
          narrowDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us H.parameterSuffix.parameterDecls
            A.semantics.parameterTail
            (VExpr.wrapForalls narrowDomains narrowResidual) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (narrowDomains.reverse ++
              H.parameterSuffix.parameterDecls.toCtx)
            (B.fieldDomains.reverse ++
              H.parameterSuffix.parameterDecls.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorExpandedSourceFieldAlignment B with
    ⟨S, HS, sourceDomains, sourceResidual, hsource, htail, Hsource,
      HsourceExpanded⟩
  rcases HS.semantic.parameterTranslationAtSuffix with
    ⟨narrowTarget, Hnarrow₀⟩
  have hbaseEnv : HS.semantic.rootWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.fieldsRecent.contextExtension.venv_eq,
      ← HS.semantic.hypothesesRecent.contextExtension.venv_eq,
      ← HS.semantic.extension.venv_eq, H.recursorEnv]
    exact H.installed.le
  have Hnarrow₁ := Hnarrow₀.mono hbaseEnv
  have Hnarrow : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      narrowTarget := by
    simpa only [HS.parameterDecls_eq, htail] using Hnarrow₁
  rcases TrExprS.forallTelescope_shape
      A.semantics.fieldOpening.telescope Hnarrow with
    ⟨narrowDomains, narrowResidual, hnarrowLength, hnarrowTarget⟩
  rw [hnarrowTarget] at Hnarrow
  rcases B.runtime.front.base with
    ⟨baseScope, baseExpanded, baseShift, hscopeBase,
      hexpandedBase, hshift, Wbase⟩
  have hbaseScope : baseScope = H.parameterSuffix.parameterDecls := by
    rw [← hscopeBase, B.scope_base]
  subst baseScope
  rcases B.semanticFieldContext with
    ⟨_hruleLength, _hsemanticContext, hfrontExpanded,
      _hexpandedContext, HfieldBase, _Hexpanded⟩
  have HbaseContext : VLCtx.IsDefEq H.outVEnv Us.length
      baseExpanded H.recursorWF.mlctx.vlctx := by
    rw [hfrontExpanded] at hexpandedBase
    have HfieldBase' := HfieldBase
    rw [hexpandedBase] at HfieldBase'
    simpa [A.semantics.fieldRoot_vlctx] using HfieldBase'
  rw [hbaseScope] at Wbase
  have HnarrowWeak : TrExprS H.outVEnv Us baseExpanded
      A.semantics.parameterTail
      ((VExpr.wrapForalls narrowDomains narrowResidual).lift'
        baseShift) := by
    exact Hnarrow.weakFV' H.outVEnvWF.ordered Wbase HbaseContext.wf
  have Htarget := HnarrowWeak.uniq H.outVEnvWF HbaseContext Hsource
  rw [VExpr.lift'_wrapForalls_exact] at Htarget
  let liftedDomains := liftForallDomains narrowDomains baseShift
  have hliftedLength : liftedDomains.length = narrowDomains.length := by
    exact liftForallDomains_length narrowDomains baseShift
  have HbaseDefEq : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (VLCtx.toCtx baseExpanded) H.recursorWF.mlctx.vlctx.toCtx :=
    HbaseContext.defeqCtx
  have HliftedSource := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF HbaseDefEq
      (hliftedLength.trans hnarrowLength |>.trans hsource.symm) Htarget
  have HliftedExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HliftedSource HsourceExpanded
  have hexpandedContext : B.runtime.expanded.toCtx =
      B.runtime.frontExpandedDomains.reverse ++ VLCtx.toCtx baseExpanded := by
    rw [B.runtime.front.expandedContext, hexpandedBase]
  rw [hexpandedContext] at HliftedExpanded
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hsemanticRoot : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv := by
    exact A.semantics.fieldsRecent.venv_eq.symm.trans
      A.semantics.context_venv
  have HsourceType₀ := A.semantics.parameterType
  rw [hsemanticRoot, A.semantics.fieldRoot_vlctx] at HsourceType₀
  have HsourceType := HsourceType₀.mono hrecBase
  have HrootWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hrecBase).tr.wf
  have HparameterTranslation₀ := A.semantics.parameterTranslation
  rw [hsemanticRoot, A.semantics.fieldRoot_vlctx] at HparameterTranslation₀
  have HparameterTranslation := HparameterTranslation₀.mono hrecBase
  have HparameterSource := HparameterTranslation.uniq H.outVEnvWF
    (.refl H.outVEnvWF HrootWF) Hsource
  have HsourceWrappedType := VEnv.IsType.defeqU_l H.outVEnvWF
    HrootWF.toCtx HparameterSource HsourceType
  have HsourceTypeAtBase := HsourceWrappedType.defeqDFC
    H.outVEnvWF.ordered
    (HbaseContext.defeqCtx.symm H.outVEnvWF.ordered)
  have HwholeType : H.outVEnv.IsType Us.length
      (VLCtx.toCtx baseExpanded)
      (VExpr.wrapForalls liftedDomains
        (narrowResidual.lift'
          (baseShift.consN narrowDomains.length))) :=
    VEnv.IsType.defeqU_l H.outVEnvWF HbaseContext.wf.toCtx
      Htarget.symm HsourceTypeAtBase
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    HbaseContext.wf.toCtx HwholeType
  rcases Hopened.2 with ⟨bodyLevel, Hbody⟩
  have Hclosed := VEnv.IsDefEqCtx.closeHeads HliftedExpanded
    liftedDomains.length (by simp [liftedDomains]) Hbody
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have hfrontLength : B.runtime.frontExpandedDomains.length =
      liftedDomains.length := by
    rw [hfrontExpanded, hliftedLength, hnarrowLength]
  have Hclosed' : H.outVEnv.IsDefEq Us.length (VLCtx.toCtx baseExpanded)
      (VExpr.wrapForalls liftedDomains
        (narrowResidual.lift'
          (baseShift.consN narrowDomains.length)))
      (VExpr.wrapForalls B.runtime.frontExpandedDomains
        (narrowResidual.lift'
          (baseShift.consN narrowDomains.length)))
      (.sort closedLevel) := by
    have hleftDrop :
        (liftedDomains.reverse ++ VLCtx.toCtx baseExpanded).drop
            liftedDomains.length = VLCtx.toCtx baseExpanded := by
      simp
    have hleftTake :
        (liftedDomains.reverse ++ VLCtx.toCtx baseExpanded).take
            liftedDomains.length = liftedDomains.reverse := by
      simp
    have hrightTake :
        (B.runtime.frontExpandedDomains.reverse ++
            VLCtx.toCtx baseExpanded).take liftedDomains.length =
          B.runtime.frontExpandedDomains.reverse := by
      rw [← hfrontLength]
      simp
    rw [hleftDrop, hleftTake, hrightTake] at Hclosed
    simpa using Hclosed
  have hfrontSourceLength : B.runtime.frontSourceDomains.length =
      narrowDomains.length := by
    rw [B.front, B.fieldDomains_length, hnarrowLength]
  have hrightLift :
      (VExpr.wrapForalls B.fieldDomains narrowResidual).lift' baseShift =
        VExpr.wrapForalls B.runtime.frontExpandedDomains
          (narrowResidual.lift'
            (baseShift.consN narrowDomains.length)) := by
    have Hclose := B.runtime.front.closeAtBase baseShift hshift narrowResidual
    rw [B.front, hshift, hfrontSourceLength] at Hclose
    exact Hclose
  have Hlifted : H.outVEnv.IsDefEqU Us.length (VLCtx.toCtx baseExpanded)
      ((VExpr.wrapForalls narrowDomains narrowResidual).lift' baseShift)
      ((VExpr.wrapForalls B.fieldDomains narrowResidual).lift' baseShift) := by
    rw [VExpr.lift'_wrapForalls_exact, hrightLift]
    exact ⟨.sort closedLevel, Hclosed'⟩
  have HnarrowFields :=
    (VEnv.IsDefEqU.weak'_iff H.outVEnvWF HbaseContext.wf.toCtx
      Wbase.toCtx).1 Hlifted
  have HparameterBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.parameterSuffix.parameterDecls.toCtx
      H.parameterSuffix.parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.refl
      (Wbase.wf H.outVEnvWF HbaseContext.wf).toCtx
  have Hfields := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    HparameterBase (hnarrowLength.trans B.fieldDomains_length.symm)
      HnarrowFields
  exact ⟨S, HS, narrowDomains, narrowResidual, hnarrowLength,
    Hnarrow, Hfields⟩

/-- The independently checked constructor-field telescope and the narrow
rule-wide field telescope are definitionally equal over the cached parameter
scope.  The selected minor is the bridge: both parameter-scoped translations
come from its retained constructor tail, while `finalSelectedMinorSharedFieldContext`
connects that tail to the constructor checker. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedNarrowFieldAlignment
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ checkedDomains checkedResidual,
      checkedDomains.length = A.rule.allArgs.size ∧
      TrExprS H.outVEnv Us H.parameterSuffix.parameterDecls
        A.semantics.parameterTail
        (VExpr.wrapForalls checkedDomains checkedResidual) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (checkedDomains.reverse ++
          H.parameterSuffix.parameterDecls.toCtx)
        (B.fieldDomains.reverse ++
          H.parameterSuffix.parameterDecls.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSharedFieldContext with
    ⟨_S₁, _HS₁, minorDomains, minorResidual,
      checkedDomains, checkedResidual, _hlocal₁, _htail₁,
      hminor, hchecked, Hminor, Hchecked, HminorChecked⟩
  rcases A.finalSelectedMinorNarrowFieldAlignment B with
    ⟨_S₂, _HS₂, narrowDomains, narrowResidual,
      hnarrow, Hnarrow, HnarrowFields⟩
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us] using HfieldCtx.drop B.fieldDomains.length
  have Hminor' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls minorDomains minorResidual) := by
    simpa only [← H.parameterDecls] using Hminor
  have Hchecked' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual) := by
    simpa only [← H.parameterDecls] using Hchecked
  have HminorChecked' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (minorDomains.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
      (checkedDomains.reverse ++ H.parameterSuffix.parameterDecls.toCtx) := by
    simpa only [← H.parameterDecls] using HminorChecked
  have HminorNarrowTarget := Hminor'.uniq H.outVEnvWF
    (VLCtx.IsDefEq.refl H.outVEnvWF
      (H.parameterSuffix.parameterWF.mono hrecBase)) Hnarrow
  have HparameterBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.parameterSuffix.parameterDecls.toCtx
      H.parameterSuffix.parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.refl HparameterCtx
  have HminorNarrow := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    HparameterBase (hminor.trans hnarrow.symm) HminorNarrowTarget
  have HcheckedMinor := HminorChecked'.symm H.outVEnvWF.ordered
  have HcheckedNarrow := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcheckedMinor HminorNarrow
  have HcheckedFields := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcheckedNarrow HnarrowFields
  exact ⟨checkedDomains, checkedResidual, hchecked, Hchecked',
    HcheckedFields⟩

/-- Insert the generated motive/minor block beneath the checked-to-narrow
field conversion and transport the older generated parameter context to the
cached parameter suffix.  The right side is exactly the fixed equation
context used by `CanonicalRecursiveResultAt`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedNarrowEquationContextAlignment
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ checkedDomains equationFieldDomains : List VExpr,
        checkedDomains.length = A.rule.allArgs.size ∧
        equationFieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            checkedDomains.reverse).reverse ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (equationFieldDomains.reverse ++
            (T.params ++ T.motives ++ T.minors).reverse)
          ((liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse) ++
            (T.motives ++ T.minors).reverse ++
              H.parameterSuffix.parameterDecls.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, checkedDomains, checkedResidual, _introTarget, hparams,
      hchecked, Hchecked, _HfieldResidual, _HtailType,
      _HtailTypeT, HcheckedContext, _HintroType, _Hintro,
      _HintroShape⟩
  rcases A.finalCheckedNarrowFieldAlignment B with
    ⟨otherCheckedDomains, otherCheckedResidual, hotherChecked,
      HotherChecked, HotherNarrow⟩
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have Hchecked' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual) := by
    simpa only [← H.parameterDecls] using Hchecked
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us] using HfieldCtx.drop B.fieldDomains.length
  have HcheckedTarget := Hchecked'.uniq H.outVEnvWF
    (VLCtx.IsDefEq.refl H.outVEnvWF
      (H.parameterSuffix.parameterWF.mono hrecBase)) HotherChecked
  have HparameterBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.parameterSuffix.parameterDecls.toCtx
      H.parameterSuffix.parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.refl HparameterCtx
  have HcheckedOther := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    HparameterBase (hchecked.trans hotherChecked.symm) HcheckedTarget
  have HcheckedNarrow := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcheckedOther HotherNarrow
  let inserted := T.motives ++ T.minors
  let checkedRecent := checkedDomains.reverse
  let narrowRecent := B.fieldDomains.reverse
  let insertedCtx := inserted.reverse
  have HprefixCanonical : OnCtx (insertedCtx ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [inserted, insertedCtx, Us, List.reverse_append,
      List.append_assoc] using T.prefixContext H.outVEnvWF.ordered
  have HprefixEq : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (insertedCtx ++ T.params.reverse)
      (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx) := by
    have Hextended :=
      Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
        hparams HprefixCanonical
    simpa [insertedCtx, ← H.parameterDecls] using Hextended
  have HinsertedCtx : OnCtx
      (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) :=
    (HprefixEq.symm H.outVEnvWF.ordered).isType
  have HfieldsInserted := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered checkedRecent narrowRecent insertedCtx
      H.parameterSuffix.parameterDecls.toCtx HcheckedNarrow
      (by simp [checkedRecent, narrowRecent, hchecked,
        B.fieldDomains_length]) HinsertedCtx
  have HcheckedRecent : OnCtx
      (checkedRecent ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [checkedRecent, Us] using HcheckedContext
  have HcanonicalEquation := Lean4Lean.OnCtx.insertAfterPrefix
    H.outVEnvWF.ordered HcheckedRecent HprefixCanonical
  have HcanonicalToCached :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      HprefixEq (by
        simpa [List.append_assoc] using HcanonicalEquation)
  have HfieldsInserted' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix insertedCtx.length checkedRecent ++
        (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx))
      (liftContextPrefix insertedCtx.length narrowRecent ++
        (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx)) := by
    simpa [List.append_assoc] using HfieldsInserted
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcanonicalToCached HfieldsInserted'
  let equationFieldDomains :=
    (liftContextPrefix inserted.length checkedDomains.reverse).reverse
  exact ⟨T, checkedDomains, equationFieldDomains, hchecked, rfl, by
    simpa [equationFieldDomains, inserted, checkedRecent, narrowRecent,
      insertedCtx, List.reverse_append, List.append_assoc,
      Nat.add_comm] using Haligned⟩

/-- Witness-stable form of
`finalCheckedNarrowEquationContextAlignment`.  Consumers of canonical
recursive results already carry a particular recursor telescope translation;
this specialization transports the equation-context conversion to that exact
witness instead of forcing a second existential choice. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedNarrowEquationContextAlignmentFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ checkedDomains equationFieldDomains : List VExpr,
      checkedDomains.length = A.rule.allArgs.size ∧
      equationFieldDomains =
        (liftContextPrefix (T.motives ++ T.minors).length
          checkedDomains.reverse).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse)
        ((liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse) ++
          (T.motives ++ T.minors).reverse ++
            H.parameterSuffix.parameterDecls.toCtx) := by
  dsimp only
  rcases A.finalCheckedNarrowEquationContextAlignment B with
    ⟨T₁, checkedDomains, equationFieldDomains, hchecked,
      hequationFields, Hcontext⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hmotives, hminors] at hequationFields
  rw [hparams, hmotives, hminors] at Hcontext
  exact ⟨checkedDomains, equationFieldDomains, hchecked,
    hequationFields, Hcontext⟩

/-- Frame-parameterized form of the checked-to-fixed equation conversion.
Unlike the existential wrapper, this theorem preserves the exact checked
field translation already compared with another independently reconstructed
telescope. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedNarrowEquationContextAlignmentFromFrameFor
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (checkedDomains : List VExpr) (checkedResidual : VExpr)
    (hparams : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx)
    (hchecked : checkedDomains.length = A.rule.allArgs.size)
    (Hchecked : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual))
    (HcheckedContext : OnCtx (checkedDomains.reverse ++ T.params.reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let inserted := T.motives ++ T.minors
    ∃ equationFieldDomains : List VExpr,
      equationFieldDomains =
        (liftContextPrefix inserted.length checkedDomains.reverse).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse)
        ((liftContextPrefix inserted.length B.fieldDomains.reverse) ++
          inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalCheckedNarrowFieldAlignment B with
    ⟨otherCheckedDomains, otherCheckedResidual, hotherChecked,
      HotherChecked, HotherNarrow⟩
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us] using HfieldCtx.drop B.fieldDomains.length
  have HcheckedTarget := Hchecked.uniq H.outVEnvWF
    (VLCtx.IsDefEq.refl H.outVEnvWF
      (H.parameterSuffix.parameterWF.mono hrecBase)) HotherChecked
  have HparameterBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.parameterSuffix.parameterDecls.toCtx
      H.parameterSuffix.parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.refl HparameterCtx
  have HcheckedOther := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    HparameterBase (hchecked.trans hotherChecked.symm) HcheckedTarget
  have HcheckedNarrow := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcheckedOther HotherNarrow
  let inserted := T.motives ++ T.minors
  let checkedRecent := checkedDomains.reverse
  let narrowRecent := B.fieldDomains.reverse
  let insertedCtx := inserted.reverse
  have HprefixCanonical : OnCtx (insertedCtx ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [inserted, insertedCtx, Us, List.reverse_append,
      List.append_assoc] using T.prefixContext H.outVEnvWF.ordered
  have HprefixEq : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (insertedCtx ++ T.params.reverse)
      (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx) := by
    have Hextended :=
      Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
        hparams HprefixCanonical
    simpa [insertedCtx] using Hextended
  have HinsertedCtx : OnCtx
      (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) :=
    (HprefixEq.symm H.outVEnvWF.ordered).isType
  have HfieldsInserted := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered checkedRecent narrowRecent insertedCtx
      H.parameterSuffix.parameterDecls.toCtx HcheckedNarrow
      (by simp [checkedRecent, narrowRecent, hchecked,
        B.fieldDomains_length]) HinsertedCtx
  have HcheckedRecent : OnCtx
      (checkedRecent ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [checkedRecent, Us] using HcheckedContext
  have HcanonicalEquation := Lean4Lean.OnCtx.insertAfterPrefix
    H.outVEnvWF.ordered HcheckedRecent HprefixCanonical
  have HcanonicalToCached :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      HprefixEq (by
        simpa [List.append_assoc] using HcanonicalEquation)
  have HfieldsInserted' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix insertedCtx.length checkedRecent ++
        (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx))
      (liftContextPrefix insertedCtx.length narrowRecent ++
        (insertedCtx ++ H.parameterSuffix.parameterDecls.toCtx)) := by
    simpa [List.append_assoc] using HfieldsInserted
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HcanonicalToCached HfieldsInserted'
  let equationFieldDomains :=
    (liftContextPrefix inserted.length checkedDomains.reverse).reverse
  exact ⟨equationFieldDomains, rfl, by
    simpa [equationFieldDomains, inserted, checkedRecent, narrowRecent,
      insertedCtx, List.reverse_append, List.append_assoc,
      Nat.add_comm] using Haligned⟩

/-- The selected minor variable is available in the same fixed narrowed
equation context used by every canonical recursive result.  Besides the
lookup itself, retain the conversion from the independently checked field
context: subsequent applications can transport typed terms without silently
changing their constructor-field telescope. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalNarrowSelectedMinorFrame
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ checkedDomains equationFieldDomains : List VExpr,
        checkedDomains.length = A.rule.allArgs.size ∧
        equationFieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            checkedDomains.reverse).reverse ∧
        let inserted := T.motives ++ T.minors
        let fixedFieldRecent :=
          liftContextPrefix inserted.length B.fieldDomains.reverse
        let fixedContext := fixedFieldRecent ++ inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := fixedFieldRecent.length + later.length
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            (equationFieldDomains.reverse ++ inserted.reverse ++
              T.params.reverse)
            fixedContext ∧
          minorIdx < T.minors.length ∧
          H.outVEnv.HasType Us.length fixedContext (.bvar minorVar)
            (T.minors[minorIdx]!.liftN
              (later.length + 1 + fixedFieldRecent.length) 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCheckedNarrowEquationContextAlignment B with
    ⟨T, checkedDomains, equationFieldDomains, hchecked,
      hequationFields, Hcontext⟩
  let inserted := T.motives ++ T.minors
  let fixedFieldRecent :=
    liftContextPrefix inserted.length B.fieldDomains.reverse
  let fixedContext := fixedFieldRecent ++ inserted.reverse ++
    H.parameterSuffix.parameterDecls.toCtx
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := fixedFieldRecent.length + later.length
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  let older := (T.minors.take minorIdx).reverse ++
    T.motives.reverse ++ H.parameterSuffix.parameterDecls.toCtx
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
  have hfixedContext : fixedContext =
      (fixedFieldRecent ++ later.reverse) ++
        T.minors[minorIdx] :: older := by
    dsimp only [fixedContext, inserted, older]
    rw [List.reverse_append, hminorsReverse]
    simp [List.append_assoc]
  have hlookup : Lookup
      ((fixedFieldRecent ++ later.reverse) ++
        T.minors[minorIdx] :: older)
      minorVar
      (T.minors[minorIdx]!.liftN
        (later.length + 1 + fixedFieldRecent.length) 0) := by
    have hselected : T.minors[minorIdx] = T.minors[minorIdx]! :=
      (getElem!_pos T.minors minorIdx hminor).symm
    rw [← hselected]
    have Hlookup := Lookup.append_zero
      (fixedFieldRecent ++ later.reverse)
      (T.minors[minorIdx]'hminor) older
    simpa only [minorVar, List.length_append, List.length_reverse,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hlookup
  have Hminor : H.outVEnv.HasType Us.length fixedContext
      (.bvar minorVar)
      (T.minors[minorIdx]!.liftN
        (later.length + 1 + fixedFieldRecent.length) 0) := by
    apply VEnv.HasType.bvar
    rw [hfixedContext]
    exact hlookup
  exact ⟨T, checkedDomains, equationFieldDomains, hchecked,
    hequationFields, by
      simpa [inserted, fixedFieldRecent, fixedContext,
        List.append_assoc] using Hcontext,
    hminor, Hminor⟩

/-- Fix the narrow selected-minor lookup to the same telescope witness that
exposes its installed field/hypothesis split.  This isolates the remaining
application obligation exactly: the surrounding equation context contains
the narrow rule-wide fields, while the displayed minor type begins with the
installed `fieldDomains`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalNarrowSelectedMinorTypeFrame
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains hypothesisDomains targetResidual,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let fixedFieldRecent :=
          liftContextPrefix inserted.length B.fieldDomains.reverse
        let fixedContext := fixedFieldRecent ++ inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := fixedFieldRecent.length + later.length
        OnCtx fixedContext (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length fixedContext (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + fixedFieldRecent.length) 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorTargetContext with
    ⟨T, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, htarget, _HtargetContext,
      _HtargetResidual⟩
  rcases A.finalNarrowSelectedMinorFrame B with
    ⟨T₁, _checkedDomains, _equationFieldDomains, _hchecked,
      _hequationFields, Hcontext, hminor, Hminor⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at Hcontext
  rw [hmotives, hminors] at Hminor
  rw [hminors] at hminor
  have HfixedContext :=
    (Hcontext.symm H.outVEnvWF.ordered).isType
  rw [htarget] at Hminor
  exact ⟨T, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, htarget, HfixedContext, Hminor⟩

/-- Restrict the terminal constructor target to the retained rule-wide
field scope and close those named fields.  The resulting target is typed in
the exact anonymous field/parameter context used by canonical recursive
results. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.closedTargetTranslation
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ target,
      TrExprS H.outVEnv Us
        (abstractForallContext B.fieldDomains
          H.parameterSuffix.parameterDecls)
        (A.rule.target.abstractList A.rule.all_args_bound.fvars) target ∧
      H.outVEnv.IsType Us.length
        (abstractForallContext B.fieldDomains
          H.parameterSuffix.parameterDecls).toCtx target := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let Hruntime := B.runtime.mono hbase
  have Hfull : TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx
      A.rule.target A.semantics.targetTarget := by
    have Htr := A.semantics.target_translation
    rw [A.semantics.context_venv] at Htr
    exact Htr.mono hbase
  have HfullType : H.outVEnv.IsType Us.length
      A.semantics.context.mlctx.vlctx.toCtx A.semantics.targetTarget := by
    have Htype := A.semantics.target_type
    rw [A.semantics.context_venv] at Htype
    exact Htype.mono hbase
  have hclosed : Closed A.rule.target 0 := by
    have h := Hfull.closed
    rw [A.semantics.context.mlctx.noBV] at h
    exact h
  have hscope : A.rule.target.FVarsIn (· ∈ B.fieldScope.fvars) := by
    apply A.semantics.targetFVarsIn.mono
    intro fv hfv
    rw [B.scope_fvars, H.parameterSuffix.parameterDecls_fvars]
    rcases hfv with hfield | hparam
    · exact List.mem_append_left _ (List.mem_reverse.mpr hfield)
    · exact List.mem_append_right _ (List.mem_reverse.mpr hparam)
  rcases Hruntime.restrictEq H.outVEnvWF Hfull hclosed hscope with
    ⟨target, Htarget, _HtargetEq⟩
  rcases HfullType with ⟨level, HfullTyping⟩
  have HtargetType : H.outVEnv.IsType Us.length B.fieldScope.toCtx target :=
    ⟨level, Hruntime.hasTypeOfFull H.outVEnvWF Htarget Hfull
      HfullTyping⟩
  have Hclosed := Hruntime.abstractFront H.outVEnvWF B.scope_base Htarget
  have hfrontRev :
      VLCtx.fvars
          (B.fieldScope.take Hruntime.frontSourceDomains.length) =
        A.semantics.fieldsRecent.fvars.reverse := by
    have hsplit := Hruntime.frontFVars B.scope_base
    have happend :
        VLCtx.fvars
            (B.fieldScope.take Hruntime.frontSourceDomains.length) ++
              H.parameterSuffix.parameterDecls.fvars =
          A.semantics.fieldsRecent.fvars.reverse ++
              H.parameterSuffix.parameterDecls.fvars := by
      rw [← hsplit, B.scope_fvars]
    exact List.append_cancel_right happend
  have hfieldFVars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have hfront :
      (VLCtx.fvars
        (B.fieldScope.take Hruntime.frontSourceDomains.length)).reverse =
          A.rule.all_args_bound.fvars := by
    rw [hfrontRev, List.reverse_reverse, hfieldFVars]
  dsimp only [Hruntime,
    checkInductiveTypes.loopType.NarrowRuntimeScope.mono] at hfront Hclosed
  rw [hfront, B.front] at Hclosed
  have HtargetType' : H.outVEnv.IsType Us.length
      (abstractForallContext B.fieldDomains
        H.parameterSuffix.parameterDecls).toCtx target := by
    rw [← B.fieldScope_eq]
    exact HtargetType
  exact ⟨target, Hclosed, HtargetType'⟩

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.narrowFieldRuntimeFrame
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
    Nonempty A.NarrowFieldRuntimeFrame := by
  rcases A.narrowFieldRuntimeScope with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      fieldDomains, hfieldDomains, hfieldFront⟩
  exact ⟨{
    fieldScope := fieldScope
    runtime := HfieldScope
    scope_fvars := hfieldScopeFVars
    scope_base := hfieldBase
    fieldDomains := fieldDomains
    fieldDomains_length := hfieldDomains
    front := hfieldFront }⟩

/-- Replay one exact higher-order call suffix above a fixed rule-wide field
and cached-parameter frame.  The fixed-frame argument is the common-context
anchor needed by the recursive-result list fold. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowRuntimeScopeFor
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        scope.fvars = F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        scope.drop Hscope.frontSourceDomains.length = parameterDecls ∧
        ∃ localDomains,
          B.fieldDomains.length = A.rule.allArgs.size ∧
          localDomains.length = F.semantic.generated.localArgs.size ∧
          Hscope.frontSourceDomains = B.fieldDomains ++ localDomains := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases B with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      fieldDomains, hfieldDomains, hfieldFront⟩
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨localDomains, HlocalPrefix⟩
  have hlocalRuntime :
      (F.semantic.current_context.mlctx.dropN
        F.semantic.generated.localArgs.size HlocalPrefix.le).vlctx =
          A.semantics.context.mlctx.vlctx := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.semantic.recent.drop_eq]
  let HlocalBase := HfieldScope.retargetRuntime hlocalRuntime.symm
  have HlocalWF : F.semantic.current_context.mlctx.WF
      H.recursorWF.venv Us := by
    have hvenv : F.semantic.current_context.venv = H.recursorWF.venv :=
      F.semantic.recent.venv_eq.trans A.semantics.context_venv
    simpa only [Us, hvenv] using F.semantic.current_context.mlctx_wf
  have hlocalRev : F.semantic.current_context.mlctx.fvarRevList
      F.semantic.generated.localArgs.size HlocalPrefix.le =
        F.semantic.recent.fvars.reverse := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.fvarRevList_eq
  have HlocalUp : IsFVarUpSet
      (fun fv => fv ∈ F.semantic.current_context.mlctx.fvarRevList
          F.semantic.generated.localArgs.size HlocalPrefix.le ++
            fieldScope.fvars)
      F.semantic.current_context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HlocalWF.tr.wf.fvwf ?_).mp
      F.semantic.current_scope_up
    intro fv _
    rw [F.root_scope, hlocalRev, hfieldScopeFVars,
      H.parameterSuffix.parameterDecls_fvars]
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
    simp [parameterDecls]
  rcases HlocalPrefix.extendNarrowRuntimeScope
      H.recursorWF.checking.tr.wf HlocalWF HlocalBase HlocalUp with
    ⟨scope, Hscope, hscopeFVars, hscopeBase,
      localDomains, hlocalDomains, hlocalFront⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hlocalBaseDrop :
      fieldScope.drop HlocalBase.frontSourceDomains.length =
        parameterDecls := by
    simpa [HlocalBase,
      checkInductiveTypes.loopType.NarrowRuntimeScope.retargetRuntime]
      using hfieldBase
  refine ⟨scope, Hscope.mono hbase, ?_, ?_, localDomains,
    hfieldDomains, hlocalDomains, ?_⟩
  · rw [hscopeFVars, hlocalRev, hfieldScopeFVars]
    simp [parameterDecls, List.append_assoc]
  · change scope.drop Hscope.frontSourceDomains.length = parameterDecls
    exact hscopeBase.trans hlocalBaseDrop
  · change Hscope.frontSourceDomains = fieldDomains ++ localDomains
    rw [hlocalFront]
    change HfieldScope.frontSourceDomains ++ localDomains =
      fieldDomains ++ localDomains
    rw [hfieldFront]

/-- Replay the exact higher-order call-local forall telescope while extending
the fixed narrowed field frame.  Unlike `narrowRuntimeScopeFor`, this retains
the strict translations of the narrowed local domains, so a later
first-pass/second-pass comparison can use `SameForallPrefix` without
reconstructing those binder translations from a context conversion. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowLocalForallReplayFor
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        scope.fvars = F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse ++
            H.parameterSuffix.parameterDecls.fvars ∧
        scope.drop Hscope.frontSourceDomains.length =
          H.parameterSuffix.parameterDecls ∧
        ∃ localDomains,
          localDomains.length = F.semantic.generated.localArgs.size ∧
          Hscope.frontSourceDomains = B.fieldDomains ++ localDomains ∧
          ∀ {body target},
            TrExprS H.outVEnv Us scope body target →
            H.outVEnv.IsType Us.length scope.toCtx target →
            TrExprS H.outVEnv Us B.fieldScope
                (F.semantic.generated.current.lctx.mkForall
                  F.semantic.generated.localArgs body)
                (VExpr.wrapForalls localDomains target) ∧
              H.outVEnv.IsType Us.length B.fieldScope.toCtx
                (VExpr.wrapForalls localDomains target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases B with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      fieldDomains, _hfieldDomains, hfieldFront⟩
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨semanticLocalDomains, HlocalPrefix⟩
  have hlocalRuntime :
      (F.semantic.current_context.mlctx.dropN
        F.semantic.generated.localArgs.size HlocalPrefix.le).vlctx =
          A.semantics.context.mlctx.vlctx := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.semantic.recent.drop_eq]
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let HfieldScopeOut := HfieldScope.mono hbase
  let HlocalBase := HfieldScopeOut.retargetRuntime hlocalRuntime.symm
  have HlocalWF : F.semantic.current_context.mlctx.WF H.outVEnv Us := by
    have hvenv : F.semantic.current_context.venv = H.recursorWF.venv :=
      F.semantic.recent.venv_eq.trans A.semantics.context_venv
    have Hwf : F.semantic.current_context.mlctx.WF
        H.recursorWF.venv Us := by
      simpa only [Us, hvenv] using F.semantic.current_context.mlctx_wf
    exact Hwf.mono hbase
  have hlocalRev : F.semantic.current_context.mlctx.fvarRevList
      F.semantic.generated.localArgs.size HlocalPrefix.le =
        F.semantic.recent.fvars.reverse := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.fvarRevList_eq
  have HlocalUp : IsFVarUpSet
      (fun fv => fv ∈ F.semantic.current_context.mlctx.fvarRevList
          F.semantic.generated.localArgs.size HlocalPrefix.le ++
            fieldScope.fvars)
      F.semantic.current_context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HlocalWF.tr.wf.fvwf ?_).mp
      F.semantic.current_scope_up
    intro fv _
    rw [F.root_scope, hlocalRev, hfieldScopeFVars,
      H.parameterSuffix.parameterDecls_fvars]
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
    simp [List.append_assoc]
  rcases HlocalPrefix.extendNarrowRuntimeScopeForallReplay
      H.outVEnvWF HlocalWF HlocalBase HlocalUp with
    ⟨scope, Hscope, hscopeFVars, hscopeBase,
      localDomains, hlocalDomains, hlocalFront, Hreplay⟩
  have hsource : ∀ body,
      F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs body =
        F.semantic.current_context.mlctx.mkForall
          F.semantic.generated.localArgs.size HlocalPrefix.le body := by
    intro body
    rw [← F.semantic.current_context.lctx_eq]
    apply F.semantic.current_context.mlctx_wf.mkForall_eq
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.reverse_eq
  have hlocalBaseDrop :
      fieldScope.drop HlocalBase.frontSourceDomains.length =
        H.parameterSuffix.parameterDecls := by
    simpa [HlocalBase, HfieldScopeOut,
      checkInductiveTypes.loopType.NarrowRuntimeScope.retargetRuntime,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using hfieldBase
  refine ⟨scope, Hscope, ?_, hscopeBase.trans hlocalBaseDrop,
    localDomains, hlocalDomains, ?_, ?_⟩
  · rw [hscopeFVars, hlocalRev, hfieldScopeFVars]
    simp [List.append_assoc]
  · change Hscope.frontSourceDomains = fieldDomains ++ localDomains
    rw [hlocalFront]
    change HfieldScopeOut.frontSourceDomains ++ localDomains =
      fieldDomains ++ localDomains
    simpa [HfieldScopeOut,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using
      congrArg (· ++ localDomains) hfieldFront
  · intro body target Hbody HbodyType
    rw [hsource]
    simpa [HlocalBase, HfieldScopeOut,
      checkInductiveTypes.loopType.NarrowRuntimeScope.retargetRuntime,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using
      Hreplay Hbody HbodyType

/-- The higher-order local binder domains generated for a recursive call do
not depend on motives, minors, or induction hypotheses.  Closing the exact
local suffix in the narrowed field scope and then abstracting the constructor
fields leaves only the original inductive parameters free. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedNeutralLocalForallSourceScope
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
    (B : A.NarrowFieldRuntimeFrame) :
    ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
      A.rule.all_args_bound.fvars).FVarsIn
        (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.narrowLocalForallReplayFor B with
    ⟨scope, _Hscope, _hscopeFVars, _hscopeBase,
      _localDomains, _hlocal, _hfront, Hreplay⟩
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hzero : TrExprS H.outVEnv Us scope
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have HzeroType : H.outVEnv.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  have Hneutral := (Hreplay Hzero HzeroType).1
  have HneutralScope :
      (F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).FVarsIn
          (fun fv => fv ∈ A.rule.all_args_bound.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params) := by
    apply Hneutral.fvarsIn.mono
    intro fv hfv
    rw [B.scope_fvars] at hfv
    rcases List.mem_append.mp hfv with hfield | hparam
    · left
      have hfield' : fv ∈ A.semantics.fieldsRecent.fvars :=
        List.mem_reverse.mp hfield
      have hfvars : A.semantics.fieldsRecent.fvars =
          A.rule.all_args_bound.fvars :=
        BoundFVarArray.fvars_eq
          A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
          A.rule.all_args_bound rfl
      simpa [hfvars] using hfield'
    · right
      simpa [H.parameterSuffix.parameterDecls_fvars] using hparam
  exact FVarsIn.abstractList_of HneutralScope

/-- Existential specialization of `narrowRuntimeScopeFor` used by the
earlier pointwise call lemmas.  List-level reconstruction instead retains
the `NarrowFieldRuntimeFrame` witness and calls the parameterized theorem. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowRuntimeScope
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
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        scope.fvars = F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        scope.drop Hscope.frontSourceDomains.length = parameterDecls ∧
        ∃ fieldDomains localDomains,
          fieldDomains.length = A.rule.allArgs.size ∧
          localDomains.length = F.semantic.generated.localArgs.size ∧
          Hscope.frontSourceDomains = fieldDomains ++ localDomains := by
  rcases A.narrowFieldRuntimeFrame with ⟨B⟩
  rcases F.narrowRuntimeScopeFor B with
    ⟨scope, Hscope, hscopeFVars, hscopeBase, localDomains,
      hfields, hlocal, hfront⟩
  exact ⟨scope, Hscope, hscopeFVars, hscopeBase,
    B.fieldDomains, localDomains, hfields, hlocal, hfront⟩

/-- The retained narrowing witness exposes the exact semantic context on its
expanded side.  In particular, the independently narrowed field/local front
is related to the literal local-then-field suffix of the executable semantic
context without identifying either list syntactically. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowRuntimeSemanticContextFor
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        ∃ (localDomains semanticLocalDomains semanticFieldDomains :
            List VExpr),
          Hscope.frontSourceDomains = B.fieldDomains ++ localDomains ∧
          localDomains.length = F.semantic.generated.localArgs.size ∧
          semanticLocalDomains.length =
            F.semantic.generated.localArgs.size ∧
          semanticFieldDomains.length = A.rule.allArgs.size ∧
          F.semantic.current_context.mlctx.vlctx.toCtx =
            semanticLocalDomains.reverse ++ semanticFieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
          Hscope.expanded.toCtx =
            Hscope.frontExpandedDomains.reverse ++
              VLCtx.toCtx (Hscope.expanded.drop
                Hscope.frontExpandedDomains.length) ∧
          List.Forall₂
            (fun fv entry => ∃ deps type,
              entry = (some (fv, deps), .vlam type))
            A.semantics.fieldsRecent.fvars.reverse
            ((Hscope.expanded.drop
              F.semantic.generated.localArgs.size).take
                A.rule.allArgs.size) ∧
          VLCtx.IsDefEq H.outVEnv Us.length
            (Hscope.expanded.drop
              F.semantic.generated.localArgs.size)
            A.semantics.context.mlctx.vlctx ∧
          VLCtx.IsDefEq H.outVEnv Us.length
            (Hscope.expanded.drop
              (F.semantic.generated.localArgs.size +
                A.rule.allArgs.size))
            A.semantics.fieldRootContext.mlctx.vlctx ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            Hscope.expanded.toCtx
            (semanticLocalDomains.reverse ++ semanticFieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.narrowRuntimeScopeFor B with
    ⟨scope, Hscope, _hscopeFVars, _hscopeBase, localDomains,
      _hfields, hlocal, hfront⟩
  let semanticLocalDomains := MLCtxForallDomains
    F.semantic.current_context.mlctx
    F.semantic.generated.localArgs.size F.semantic.recent.size_le
  let semanticFieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hsemanticLocal : semanticLocalDomains.length =
      F.semantic.generated.localArgs.size :=
    F.semantic.current_context.onlyLams.forallDomains_length
      F.semantic.generated.localArgs.size F.semantic.recent.size_le
  have hsemanticFields : semanticFieldDomains.length = A.rule.allArgs.size :=
    A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hsemanticContext :=
    MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
      F.semantic.current_context.onlyLams
      F.semantic.generated.localArgs.size F.semantic.recent.size_le
  rw [F.semantic.recent.drop_eq] at hsemanticContext
  have hfieldContext :=
    MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
      A.semantics.context.onlyLams A.rule.allArgs.size
      A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.drop_eq] at hfieldContext
  rw [hfieldContext] at hsemanticContext
  have hsemanticContext' :
      F.semantic.current_context.mlctx.vlctx.toCtx =
        semanticLocalDomains.reverse ++ semanticFieldDomains.reverse ++
          A.semantics.fieldRootContext.mlctx.vlctx.toCtx := by
    simpa [semanticLocalDomains, semanticFieldDomains] using hsemanticContext
  have hexpanded := Hscope.front.expandedContext
  have hlocalDrop :
      F.semantic.current_context.mlctx.vlctx.drop
          F.semantic.generated.localArgs.size =
        A.semantics.context.mlctx.vlctx := by
    rw [← F.semantic.current_context.onlyLams.vlctx_dropN
      F.semantic.generated.localArgs.size F.semantic.recent.size_le,
      F.semantic.recent.drop_eq]
  have HlocalBase := Hscope.context.drop
    F.semantic.generated.localArgs.size
  rw [hlocalDrop] at HlocalBase
  have HsemanticFieldDecls :=
    A.semantics.context.onlyLams.fvarRevList_declarations
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.fvarRevList_eq] at HsemanticFieldDecls
  have HexpandedFieldDecls :=
    HlocalBase.leftLambdaDeclarations HsemanticFieldDecls
  have hfieldDrop :
      A.semantics.context.mlctx.vlctx.drop A.rule.allArgs.size =
        A.semantics.fieldRootContext.mlctx.vlctx := by
    rw [← A.semantics.context.onlyLams.vlctx_dropN
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le,
      A.semantics.fieldsRecent.drop_eq]
  have HfieldBase := HlocalBase.drop A.rule.allArgs.size
  rw [List.drop_drop, hfieldDrop] at HfieldBase
  have hcontexts : VEnv.IsDefEqCtx H.outVEnv Us.length []
      Hscope.expanded.toCtx
      (semanticLocalDomains.reverse ++ semanticFieldDomains.reverse ++
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx) := by
    have hcontexts' := Hscope.context.defeqCtx
    rw [hsemanticContext'] at hcontexts'
    simpa [semanticLocalDomains, semanticFieldDomains] using hcontexts'
  exact ⟨scope, Hscope, localDomains, semanticLocalDomains,
    semanticFieldDomains, hfront, hlocal, hsemanticLocal, hsemanticFields,
    hsemanticContext', hexpanded, HexpandedFieldDecls, HlocalBase, by
      simpa [Nat.add_comm] using HfieldBase, hcontexts⟩
/-- The validated terminal application of a recursive call consumes the
same canonical motive telescope retained for the call-selected mutual
family.  This is the semantic index/major alignment needed to consume the
selected recursor's owner-specific suffix after its common prefix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.semanticMotiveTelescopeEvidence
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
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence
        F.semantic.current_context stats H.recInfos[selectedOwner]!
        binding F.semantic.generated.exposedType F.semantic.exposedTarget) := by
  let selectedOwner := F.semantic.generated.ownerIdx
  have hrecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  let HextRule : RecursorContextExtension H.recursorWF
      A.semantics.context :=
    A.semantics.fieldRootExtension.trans
      A.semantics.fieldsRecent.contextExtension
  let Hext : RecursorContextExtension H.recursorWF
      F.semantic.current_context :=
    HextRule.trans F.semantic.recent.contextExtension
  rcases H.motiveShapes.motiveBindingAtMono
      (Rcurrent := F.semantic.current_context) H.bindings H.origins
      Hext.contextLE selectedOwner hrecInfo with ⟨Hbinding⟩
  let binding : RecursorMotiveBinding F.semantic.current_context
      H.recInfos[selectedOwner]! H.elimLevel := Hbinding.toBinding
  have HexposedType : F.semantic.current_context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.exposedTarget :=
    VEnv.IsType.defeqU_l F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm F.semantic.terminal_type
  refine ⟨binding, ?_⟩
  exact H.motiveTelescopes.telescope selectedOwner hrecInfo
    F.semantic.current_context Hext binding F.semantic.exposed_translation
    HexposedType F.semantic.validated

/-- Final-environment form of the exact higher-order field telescope fixed
by this recursive-call frame.  Unlike the earlier rule-indexed existential,
the source call, exposed family target, and eta-expanded major are all tied
to `F.semantic`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalAppliedFieldTelescope
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
    ∃ domains : List VExpr,
      domains.length = F.semantic.generated.localArgs.size ∧
      TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx
        (F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs F.semantic.generated.exposedType)
        (VExpr.wrapForalls domains F.semantic.exposedTarget) ∧
      H.outVEnv.IsType Us.length A.semantics.context.mlctx.vlctx.toCtx
        (VExpr.wrapForalls domains F.semantic.exposedTarget) ∧
      TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx
        (F.semantic.generated.current.lctx.mkLambda
          F.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs))
        (VExpr.wrapLams domains F.semantic.appliedFieldTarget) ∧
      H.outVEnv.HasType Us.length A.semantics.context.mlctx.vlctx.toCtx
        (VExpr.wrapLams domains F.semantic.appliedFieldTarget)
        (VExpr.wrapForalls domains F.semantic.exposedTarget) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let E := F.semantic.appliedFieldTelescope
  have hsemantic : A.semantics.context.venv = R.context.venv :=
    A.semantics.context_venv.trans
      H.recursorEnv
  have Hexposed := E.exposed_translation
  have HexposedType := E.exposed_type
  have Happlied := E.applied_translation
  have HappliedType := E.applied_typing
  rw [hsemantic] at Hexposed HexposedType Happlied HappliedType
  exact ⟨E.domains, E.domains_length,
    Hexposed.mono H.installed.le, HexposedType.mono H.installed.le,
    Happlied.mono H.installed.le, HappliedType.mono H.installed.le⟩

/-- Residual form of `finalAppliedFieldTelescope`: after opening the retained
higher-order domains, the exact generated major premise translates to the
semantic eta-expanded field target.  This is the typed derivation that will
be closed over the outer rule binders and identified with the canonical
de Bruijn field application. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalAppliedMajorTranslation
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
    ∃ localDomains : List VExpr,
      localDomains.length = F.semantic.generated.localArgs.size ∧
      TrExprS H.outVEnv Us
        (abstractForallContext localDomains
          A.semantics.context.mlctx.vlctx)
        F.semantic.generated.abstractedMajor
        F.semantic.appliedFieldTarget := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.finalAppliedFieldTelescope with
    ⟨localDomains, hlocal, _Hexposed, _HexposedType,
      Happlied, _HappliedType⟩
  refine ⟨localDomains, hlocal, ?_⟩
  exact TrExprS.lambdaTelescope_exact_residual
    F.semantic.generated.appliedFieldLambdaTelescope hlocal Happlied

/-- Close the constructor-field suffix around the exact applied-major
translation.  The call-local domains remain innermost, while the production
field-opening domains are inserted immediately outside them; the source is
simultaneously abstracted over the rule's retained field variables at the
matching cutoff. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalFieldAbstractedAppliedMajorTranslation
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
    ∃ (localDomains fieldDomains : List VExpr),
      localDomains.length = F.semantic.generated.localArgs.size ∧
      fieldDomains.length = A.rule.allArgs.size ∧
      TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ localDomains)
          A.semantics.fieldRootContext.mlctx.vlctx)
        (F.semantic.generated.abstractedMajor.abstractList
          A.rule.all_args_bound.fvars localDomains.length)
        F.semantic.appliedFieldTarget := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.finalAppliedMajorTranslation with
    ⟨localDomains, hlocal, Hmajor⟩
  let fieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have Hclosed := A.semantics.fieldsRecent.abstractRecent
    localDomains Hmajor
  have hfields : fieldDomains.length = A.rule.allArgs.size :=
    A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hfvars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  refine ⟨localDomains, fieldDomains, hlocal, hfields, ?_⟩
  simpa [fieldDomains, hfvars] using Hclosed

/-- The semantic eta-expanded major target is exactly one canonical
constructor-field variable applied to the generated call-local spine.  By
closing the fields before identifying the target, all older recursor-local
declarations disappear from the expression; only their eventual context
conversion remains. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalAppliedMajorTarget
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
    ∃ (localDomains fieldDomains : List VExpr) (fv : FVarId)
        (fieldVar : Nat),
      localDomains.length = F.semantic.generated.localArgs.size ∧
      fieldDomains.length = A.rule.allArgs.size ∧
      fieldVar < fieldDomains.length ∧
      A.rule.recursiveArgs[j] = .fvar fv ∧
      fv ∈ A.rule.all_args_bound.fvars ∧
      (Expr.fvar fv).abstractList
          A.rule.all_args_bound.fvars = .bvar fieldVar ∧
      TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ localDomains)
          A.semantics.fieldRootContext.mlctx.vlctx)
        (F.semantic.generated.abstractedMajor.abstractList
          A.rule.all_args_bound.fvars localDomains.length)
        F.semantic.appliedFieldTarget ∧
      F.semantic.appliedFieldTarget =
        VExpr.mkApps (.bvar (localDomains.length + fieldVar))
          (F.semantic.generated.localIndices.map VExpr.bvar) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.finalFieldAbstractedAppliedMajorTranslation with
    ⟨localDomains, fieldDomains, hlocal, hfields, Hmajor⟩
  rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
    ⟨hjFvars, hsource⟩
  let fv := A.rule.recursive_args_bound.fvars[j]
  have hsource' : A.rule.recursiveArgs[j] = .fvar fv := hsource
  have hfieldRoot : fv ∈ A.rule.root.lctx.fvars :=
    A.rule.recursive_args_bound.members fv (List.getElem_mem hjFvars)
  have hfield : fv ∈ A.rule.all_args_bound.fvars :=
    A.rule.recursive_args_bound.fvars_subset_of_sublist
      A.rule.all_args_bound A.rule.recursive_args_sublist
      (List.getElem_mem hjFvars)
  have hruleDomains : fieldDomains.length =
      A.rule.all_args_bound.fvars.length :=
    hfields.trans A.rule.all_args_bound.length_fvars.symm
  have Hmajor' : TrExprS H.outVEnv Us
      (abstractForallContext localDomains
        (abstractForallContext fieldDomains
          A.semantics.fieldRootContext.mlctx.vlctx))
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars)
      F.semantic.appliedFieldTarget := by
    unfold BoundGeneratedRecursiveCall.outerAbstractedMajor
    rw [← hlocal]
    simpa using Hmajor
  rcases F.semantic.generated.translatedOuterAbstractedMajor_eq_of_field_eq
      hsource' hfieldRoot A.rule.all_args_nodup hfield
      hruleDomains hlocal Hmajor' with
    ⟨fieldVar, hfieldVar, hfieldSource, htarget⟩
  exact ⟨localDomains, fieldDomains, fv, fieldVar,
    hlocal, hfields, hfieldVar, hsource', hfield,
    hfieldSource, Hmajor, htarget⟩

/-- Full-rule source alignment for the recursive major.  Adding the outer
parameter/motive/minor binders does not change the de Bruijn number of a
constructor field, because the fields are the innermost rule group.  Thus the
production two-stage abstraction and the semantic applied-field target use
literally the same application spine. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedAppliedMajorAlignment
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
    ∃ (localDomains fieldDomains : List VExpr) (fv : FVarId)
        (fieldVar : Nat),
      localDomains.length = F.semantic.generated.localArgs.size ∧
      fieldDomains.length = A.rule.allArgs.size ∧
      fieldVar < fieldDomains.length ∧
      A.rule.recursiveArgs[j] = .fvar fv ∧
      (Expr.fvar fv).abstractList A.rule.binders = .bvar fieldVar ∧
      F.semantic.generated.outerAbstractedMajor A.rule.binders =
        mkAppN (.bvar (localDomains.length + fieldVar))
          (F.semantic.generated.localIndices.map Expr.bvar).toArray ∧
      F.semantic.appliedFieldTarget =
        VExpr.mkApps (.bvar (localDomains.length + fieldVar))
          (F.semantic.generated.localIndices.map VExpr.bvar) := by
  rcases F.finalAppliedMajorTarget with
    ⟨localDomains, fieldDomains, fv, fieldVar,
      hlocal, hfields, hfieldVar, hsource, hfield,
      hfieldSource, _Hmajor, htarget⟩
  have hfieldFull : fv ∈ A.rule.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ hfield
  have hfieldRoot : fv ∈ A.rule.root.lctx.fvars :=
    A.rule.all_args_bound.members fv hfield
  have hnotOuter : fv ∉
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars :=
    A.rule.all_args_outer_fresh fv hfield
  have hfullSource : (Expr.fvar fv).abstractList A.rule.binders =
      .bvar fieldVar := by
    unfold BoundGeneratedRecursorRule.binders
    rw [Expr.abstractList_append,
      Expr.abstractList_fvar_of_not_mem hnotOuter, hfieldSource]
  rcases F.semantic.generated.outerAbstractedMajor_eq_bvar_of_field_eq
      hsource hfieldRoot A.rule.binders_nodup hfieldFull with
    ⟨otherFieldVar, _hotherBound, hotherSource, hmajorShape⟩
  have hotherSource' : (Expr.fvar fv).abstractList A.rule.binders =
      .bvar otherFieldVar := by
    simpa [BoundGeneratedRecursorRule.binders, List.append_assoc] using
      hotherSource
  rw [hfullSource] at hotherSource'
  cases hotherSource'
  refine ⟨localDomains, fieldDomains, fv, fieldVar,
    hlocal, hfields, hfieldVar, hsource, hfullSource, ?_, htarget⟩
  simpa [hlocal, BoundGeneratedRecursorRule.binders,
    List.append_assoc] using hmajorShape

/-- Ordinal form of `outerAbstractedAppliedMajorAlignment`.  Replay of the
recursive-field mask identifies the existential field variable with the
reverse de Bruijn ordinal of the selected constructor-field position. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedAppliedMajorOrdinal
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
    let fieldPosition := A.semantics.recursivePositions[j]!
    F.semantic.generated.outerAbstractedMajor A.rule.binders =
        mkAppN
          (.bvar (F.semantic.generated.localArgs.size +
            (A.rule.allArgs.size - 1 - fieldPosition)))
          (F.semantic.generated.localIndices.map Expr.bvar).toArray ∧
      F.semantic.appliedFieldTarget =
        VExpr.mkApps
          (.bvar (F.semantic.generated.localArgs.size +
            (A.rule.allArgs.size - 1 - fieldPosition)))
          (F.semantic.generated.localIndices.map VExpr.bvar) := by
  dsimp only
  rcases F.outerAbstractedAppliedMajorAlignment with
    ⟨localDomains, fieldDomains, fv, fieldVar,
      hlocal, hfields, _hfieldVar, hsource, hfieldSource,
      hmajor, htarget⟩
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
  constructor
  · simpa [fieldPosition, hfieldVarExact, hlocal] using hmajor
  · simpa [fieldPosition, hfieldVarExact, hlocal] using htarget

/-- The validated recursive field determines the exact expected motive
application in the final environment.  Its index targets and eta-expanded
major are the same semantic witnesses that must next be consumed by the
generated recursor's owner-specific suffix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalSemanticMotiveApplication
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        evidence.indices.length = F.telescope.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
          (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
          evidence.indices ∧
        let sourceIndices :=
          F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
        let sourceMajor := mkAppN A.rule.recursiveArgs[j]
          F.semantic.generated.localArgs
        let target := VExpr.app
          (VExpr.mkApps binding.motiveTarget evidence.indices)
          F.semantic.appliedFieldTarget
        TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx
          (Expr.app
            (mkAppN H.recInfos[selectedOwner]!.motive sourceIndices)
            sourceMajor)
          target ∧
        H.outVEnv.HasType Us.length
          F.semantic.current_context.mlctx.vlctx.toCtx target
          (.sort evidence.resultLevel) ∧
        TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx
          (F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs
            (Expr.app
              (mkAppN H.recInfos[selectedOwner]!.motive sourceIndices)
              sourceMajor))
          (VExpr.wrapForalls
            (MLCtxForallDomains F.semantic.current_context.mlctx
              F.semantic.generated.localArgs.size
              F.semantic.recent.size_le)
            target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.semanticMotiveTelescopeEvidence with ⟨binding, ⟨evidence⟩⟩
  have hrecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have htranslated :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      evidence.indices_translation
  have hsourceArity := checkPositivityStep.getIIndices.index_arity
    F.semantic.generated.owner_valid
  have hrecArity := H.arities selectedOwner hrecInfo
  have hlength : evidence.indices.length = F.telescope.indices.length := by
    rw [F.telescope.indices_length, hrecArity]
    simpa [AddInductive.getIIndices] using
      htranslated.symm.trans hsourceArity
  have HmajorType : F.semantic.current_context.venv.HasType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.appliedFieldTarget F.semantic.exposedTarget :=
    F.semantic.applied_field_typing.defeqU_r
      F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm
  have Happ := evidence.applyMajorTypedExact
    F.semantic.applied_field_translation HmajorType
  rcases Happ with ⟨Htr, Htyped⟩
  have Hforall := F.semantic.recent.mkForallExact Htr
    (⟨evidence.resultLevel, Htyped⟩ :
      F.semantic.current_context.venv.IsType Us.length
        F.semantic.current_context.mlctx.vlctx.toCtx _)
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (A.semantics.context_venv.trans
        H.recursorEnv)
  have hsemanticRoot : A.semantics.context.venv =
      R.context.venv :=
    A.semantics.context_venv.trans
      H.recursorEnv
  have Hindices := evidence.indices_translation
  rw [hsemantic] at Hindices
  have HindicesFinal := Lean4Lean.List.Forall₂.imp
    (fun _ _ Hindex => Hindex.mono H.installed.le) Hindices
  rw [hsemantic] at Htr Htyped
  rw [hsemanticRoot] at Hforall
  exact ⟨binding, evidence, hlength, HindicesFinal,
    Htr.mono H.installed.le,
    Htyped.mono H.installed.le,
    Hforall.1.mono H.installed.le⟩

/-- Close the higher-order arguments introduced while inspecting one
recursive field.  The exact expected motive application and its typing now
live over the rule context, extended only by anonymous domains; no semantic
free variable from the call-local suffix remains in the source expression. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalAbstractedSemanticMotiveApplication
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ localDomains : List VExpr,
          localDomains.length = F.semantic.generated.localArgs.size ∧
          localDomains = MLCtxForallDomains
            F.semantic.current_context.mlctx
            F.semantic.generated.localArgs.size
            F.semantic.recent.size_le ∧
          let sourceIndices :=
            F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
          let sourceMajor := mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs
          let sourceType := Expr.app
            (mkAppN H.recInfos[selectedOwner]!.motive sourceIndices)
            sourceMajor
          let target := VExpr.app
            (VExpr.mkApps binding.motiveTarget evidence.indices)
            F.semantic.appliedFieldTarget
          TrExprS H.outVEnv Us
              (abstractForallContext localDomains
                A.semantics.context.mlctx.vlctx)
              (sourceType.abstractList
                F.semantic.generated.arguments_bound.fvars) target ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext localDomains
                A.semantics.context.mlctx.vlctx).toCtx
              target (.sort evidence.resultLevel) ∧
            TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx
              (F.semantic.generated.current.lctx.mkForall
                F.semantic.generated.localArgs sourceType)
              (VExpr.wrapForalls localDomains target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.finalSemanticMotiveApplication with
    ⟨binding, evidence, _hlength, _Hindices, Htr, Htyped, Hforall⟩
  let localDomains := MLCtxForallDomains F.semantic.current_context.mlctx
    F.semantic.generated.localArgs.size F.semantic.recent.size_le
  have Hclosed := F.semantic.recent.abstractRecent [] (by
    simpa [abstractForallContext] using Htr)
  have hlocalDomains : localDomains.length =
      F.semantic.generated.localArgs.size :=
    F.semantic.current_context.onlyLams.forallDomains_length
      F.semantic.generated.localArgs.size F.semantic.recent.size_le
  have hctx := F.semantic.recent.abstractRecent_toCtx
  have hfvars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  refine ⟨binding, evidence, localDomains, hlocalDomains, rfl, ?_, ?_, ?_⟩
  · simpa [localDomains, hfvars] using Hclosed
  · rw [hctx]
    exact Htyped
  · simpa [localDomains] using Hforall

/-- Close both local higher-order arguments and constructor fields around the
semantic motive application expected from one recursive call.  This packages
the source indices, exact eta-expanded major, and their common result type in
the same field-closed context used by `finalAppliedMajorTarget`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalFieldAbstractedSemanticMotiveApplication
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ (localDomains fieldDomains : List VExpr),
          localDomains.length = F.semantic.generated.localArgs.size ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          F.semantic.current_context.mlctx.vlctx.toCtx =
            localDomains.reverse ++ fieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
          let sourceIndices :=
            F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
          let sourceMajor := mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs
          let sourceType := Expr.app
            (mkAppN H.recInfos[selectedOwner]!.motive sourceIndices)
            sourceMajor
          let target := VExpr.app
            (VExpr.mkApps binding.motiveTarget evidence.indices)
            F.semantic.appliedFieldTarget
          TrExprS H.outVEnv Us
              (abstractForallContext (fieldDomains ++ localDomains)
                A.semantics.fieldRootContext.mlctx.vlctx)
              ((sourceType.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.all_args_bound.fvars localDomains.length) target ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext (fieldDomains ++ localDomains)
                A.semantics.fieldRootContext.mlctx.vlctx).toCtx
              target (.sort evidence.resultLevel) ∧
            TrExprS H.outVEnv Us
              (abstractForallContext fieldDomains
                A.semantics.fieldRootContext.mlctx.vlctx)
              ((F.semantic.generated.current.lctx.mkForall
                F.semantic.generated.localArgs sourceType).abstractList
                  A.rule.all_args_bound.fvars)
              (VExpr.wrapForalls localDomains target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.finalAbstractedSemanticMotiveApplication with
    ⟨binding, evidence, localDomains, hlocal, hlocalExact,
      Htr, Htyped, Hforall⟩
  let fieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have Hclosed := A.semantics.fieldsRecent.abstractRecent localDomains Htr
  have HforallClosed := A.semantics.fieldsRecent.abstractRecent [] (by
    simpa [abstractForallContext] using Hforall)
  have hfields : fieldDomains.length = A.rule.allArgs.size :=
    A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hfvars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have hctx :=
    A.semantics.fieldsRecent.abstractRecent_toCtx_withPrefix localDomains
  have hlocalCtx :=
    MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
      F.semantic.current_context.onlyLams
      F.semantic.generated.localArgs.size F.semantic.recent.size_le
  rw [F.semantic.recent.drop_eq] at hlocalCtx
  rw [← hlocalExact] at hlocalCtx
  have hfieldCtx :=
    MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
      A.semantics.context.onlyLams A.rule.allArgs.size
      A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.drop_eq] at hfieldCtx
  rw [hfieldCtx] at hlocalCtx
  refine ⟨binding, evidence, localDomains, fieldDomains,
    hlocal, hfields, ?_, ?_, ?_, ?_⟩
  · simpa [fieldDomains] using hlocalCtx
  · simpa [fieldDomains, hfvars] using Hclosed
  · rw [hctx]
    exact Htyped
  · simpa [fieldDomains, hfvars] using HforallClosed

/-- Normalized source form of
`finalFieldAbstractedSemanticMotiveApplication`.  The source now exposes the
same replay trace consumed by the first/second-pass alignment theorem. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalFieldAbstractedNormalizedMotiveApplication
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ (localDomains fieldDomains : List VExpr),
          localDomains.length = F.semantic.generated.localArgs.size ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          F.semantic.current_context.mlctx.vlctx.toCtx =
            localDomains.reverse ++ fieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx ∧
          let target := VExpr.app
            (VExpr.mkApps binding.motiveTarget evidence.indices)
            F.semantic.appliedFieldTarget
          TrExprS H.outVEnv Us
              (abstractForallContext (fieldDomains ++ localDomains)
                A.semantics.fieldRootContext.mlctx.vlctx)
              (F.semantic.generated.outerAbstractedMotiveApp
                A.rule.all_args_bound.fvars) target ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext (fieldDomains ++ localDomains)
                A.semantics.fieldRootContext.mlctx.vlctx).toCtx
              target (.sort evidence.resultLevel) ∧
            TrExprS H.outVEnv Us
              (abstractForallContext fieldDomains
                A.semantics.fieldRootContext.mlctx.vlctx)
              ((F.semantic.generated.current.lctx.mkForall
                F.semantic.generated.localArgs
                (Expr.app
                  (mkAppN H.recInfos[selectedOwner]!.motive
                    F.semantic.generated.exposedType.getAppArgs[
                      stats.params.size:])
                  (mkAppN A.rule.recursiveArgs[j]
                    F.semantic.generated.localArgs))).abstractList
                A.rule.all_args_bound.fvars)
              (VExpr.wrapForalls localDomains target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.finalFieldAbstractedSemanticMotiveApplication with
    ⟨binding, evidence, localDomains, fieldDomains,
      hlocal, hfields, hcontext, Hsource, Htyped, Hforall⟩
  have howner : selectedOwner < H.recInfos.size := by
    simpa [selectedOwner, H.generated.length] using F.entry_lt
  have hsource := F.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.all_args_bound.fvars
  have hselectedMotive :
      (H.recInfos.map (·.motive))[selectedOwner]! =
        H.recInfos[selectedOwner]!.motive := by
    rw [getElem!_pos (H.recInfos.map (·.motive)) selectedOwner
      (by simpa using howner),
      getElem!_pos H.recInfos selectedOwner howner]
    simp
  rw [hselectedMotive] at hsource
  have hsource' :
      ((Expr.app
        (mkAppN H.recInfos[selectedOwner]!.motive
          F.semantic.generated.exposedType.getAppArgs[stats.params.size:])
        (mkAppN A.rule.recursiveArgs[j]
          F.semantic.generated.localArgs)).abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars localDomains.length =
        F.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars := by
    simpa [selectedOwner, hlocal] using hsource
  rw [hsource'] at Hsource
  exact ⟨binding, evidence, localDomains, fieldDomains,
    hlocal, hfields, hcontext, Hsource, Htyped, Hforall⟩

/-- Move the unopened semantic local telescope through the narrowing context
conversion and then close the expanded constructor fields.  The target is
kept existential because context conversion may change its representatives;
the source is the exact field-abstracted telescope used by replay. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.expandedFieldAbstractedSemanticMotiveTelescopeFor
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
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        ∃ expandedFieldDomains expandedTarget,
          expandedFieldDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us
            (abstractForallContext expandedFieldDomains
              (Hscope.expanded.drop
                (F.semantic.generated.localArgs.size +
                  A.rule.allArgs.size)))
            ((F.semantic.generated.current.lctx.mkForall
              F.semantic.generated.localArgs
              (Expr.app
                (mkAppN H.recInfos[selectedOwner]!.motive
                  F.semantic.generated.exposedType.getAppArgs[
                    stats.params.size:])
                (mkAppN A.rule.recursiveArgs[j]
                  F.semantic.generated.localArgs))).abstractList
              A.rule.all_args_bound.fvars)
            expandedTarget ∧
          VLCtx.IsDefEq H.outVEnv Us.length
            (Hscope.expanded.drop
              (F.semantic.generated.localArgs.size +
                A.rule.allArgs.size))
            A.semantics.fieldRootContext.mlctx.vlctx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.narrowRuntimeSemanticContextFor B with
    ⟨scope, Hscope, _narrowLocalDomains, _semanticLocalDomains,
      _semanticFieldDomains, _hfront, _hnarrowLocal, _hsemanticLocal,
      _hsemanticFields, _hsemanticContext, _hexpanded,
      HexpandedFieldDecls, HlocalBase, HfieldBase, _hcontexts⟩
  rcases F.finalSemanticMotiveApplication with
    ⟨_binding, _evidence, _hlength, _Hindices, _Hsource, _Htyped,
      Hforall⟩
  rcases Hforall.defeqDFC H.outVEnvWF
      (HlocalBase.symm H.outVEnvWF.ordered) with
    ⟨expandedTarget, Hexpanded⟩
  let expandedFieldPrefix :=
    (Hscope.expanded.drop F.semantic.generated.localArgs.size).take
      A.rule.allArgs.size
  let expandedFieldRoot :=
    Hscope.expanded.drop
      (F.semantic.generated.localArgs.size + A.rule.allArgs.size)
  have hsplit : Hscope.expanded.drop
        F.semantic.generated.localArgs.size =
      expandedFieldPrefix ++ expandedFieldRoot := by
    dsimp only [expandedFieldPrefix, expandedFieldRoot]
    calc
      Hscope.expanded.drop F.semantic.generated.localArgs.size =
          (Hscope.expanded.drop F.semantic.generated.localArgs.size).take
              A.rule.allArgs.size ++
            (Hscope.expanded.drop F.semantic.generated.localArgs.size).drop
              A.rule.allArgs.size :=
        (List.take_append_drop A.rule.allArgs.size
          (Hscope.expanded.drop
            F.semantic.generated.localArgs.size)).symm
      _ = (Hscope.expanded.drop F.semantic.generated.localArgs.size).take
              A.rule.allArgs.size ++
            Hscope.expanded.drop
              (F.semantic.generated.localArgs.size +
                A.rule.allArgs.size) := by
        rw [List.drop_drop]
  have Hexpanded' : TrExprS H.outVEnv Us
      (abstractForallContext []
        (expandedFieldPrefix ++ expandedFieldRoot))
      (F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs
        (Expr.app
          (mkAppN H.recInfos[selectedOwner]!.motive
            F.semantic.generated.exposedType.getAppArgs[stats.params.size:])
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs)))
      expandedTarget := by
    simpa [abstractForallContext, hsplit] using Hexpanded
  have hfieldFVars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have hfieldNodup : A.semantics.fieldsRecent.fvars.reverse.Nodup := by
    rw [hfieldFVars]
    exact List.nodup_reverse.mpr A.rule.all_args_nodup
  have Hclosed := TrExprS.abstractFVarLambdaPrefix
    (domains := []) (tail := expandedFieldRoot)
    (by simpa [expandedFieldPrefix] using HexpandedFieldDecls)
    hfieldNodup Hexpanded'
  let expandedFieldDomains :=
    (VLCtx.toCtx expandedFieldPrefix).reverse
  have hprefixLength : (VLCtx.toCtx expandedFieldPrefix).length =
      expandedFieldPrefix.length := by
    have go : ∀ {fvars : List FVarId} {entries : VLCtx},
        List.Forall₂
          (fun fv entry => ∃ deps type,
            entry = (some (fv, deps), .vlam type))
          fvars entries →
        entries.toCtx.length = entries.length := by
      intro fvars entries Hdecls
      induction Hdecls with
      | nil => rfl
      | cons Hhead _ ih =>
        rcases Hhead with ⟨deps, type, rfl⟩
        simp [VLCtx.toCtx, ih]
    exact go (by simpa [expandedFieldPrefix] using HexpandedFieldDecls)
  have hexpandedFields : expandedFieldDomains.length =
      A.rule.allArgs.size := by
    have hdeclLength :
        A.semantics.fieldsRecent.fvars.reverse.length =
          expandedFieldPrefix.length := by
      simpa [expandedFieldPrefix] using
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          HexpandedFieldDecls
    calc
      expandedFieldDomains.length =
          (VLCtx.toCtx expandedFieldPrefix).length := by
        simp [expandedFieldDomains]
      _ = expandedFieldPrefix.length := hprefixLength
      _ = A.semantics.fieldsRecent.fvars.reverse.length := hdeclLength.symm
      _ = A.rule.allArgs.size := by
        simp [hfieldFVars, A.rule.all_args_bound.length_fvars]
  refine ⟨scope, Hscope, expandedFieldDomains, expandedTarget,
    hexpandedFields, ?_, ?_⟩
  · simpa [expandedFieldDomains, expandedFieldRoot, hfieldFVars] using Hclosed
  · simpa [expandedFieldRoot] using HfieldBase

/-- Place the retained first-pass hypothesis declaration and the
field-abstracted second-pass semantic telescope over the same expanded
field-root base.  Their sources are deliberately not identified here: that
is the subsequent alpha/replay step.  This theorem isolates the context
transport that was previously missing from that comparison. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.expandedRawHypothesisAndSemanticTelescopeAt
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
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (F : A.RecursiveCallRecursorFrame j hj)
    (B : A.NarrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecInfoMinorTypeShape,
      ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
          S.sourceFullContext S.recursiveFields S.hypotheses,
      ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
      ∃ originRoot sourceType,
      ∃ O : RecInfoMinorHypothesisTypeOrigin
          hypothesisOrigins.stats hypothesisOrigins.recInfos
          originRoot S.recursiveFields[j]! sourceType,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
      ∃ rawTarget expandedFieldDomains semanticTarget,
        D.type = sourceType ∧
        expandedFieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (Hscope.expanded.drop
            (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
          D.type rawTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext expandedFieldDomains
            (Hscope.expanded.drop
              (F.semantic.generated.localArgs.size + A.rule.allArgs.size)))
          ((F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs
            (Expr.app
              (mkAppN
                H.recInfos[F.semantic.generated.ownerIdx]!.motive
                F.semantic.generated.exposedType.getAppArgs[
                  stats.params.size:])
              (mkAppN A.rule.recursiveArgs[j]
                F.semantic.generated.localArgs))).abstractList
            A.rule.all_args_bound.fvars)
          semanticTarget ∧
        VLCtx.IsDefEq H.outVEnv Us.length
          (Hscope.expanded.drop
            (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
          H.recursorWF.mlctx.vlctx := by
  dsimp only
  rcases A.finalSelectedMinorRawHypothesisTypeAt j hj with
    ⟨S, hypothesisOrigins, D, originRoot, sourceType, O, _HS,
      _sourceTarget, rawTarget, _hlocal, _hfields, _hhypotheses,
      _hsourceContext, htype, _HsourceTarget, _hrawTarget, Hraw⟩
  rcases F.expandedFieldAbstractedSemanticMotiveTelescopeFor B with
    ⟨scope, Hscope, expandedFieldDomains, semanticTarget,
      hfieldDomains, Hsemantic, HfieldBase⟩
  have HfieldBase' : VLCtx.IsDefEq H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (Hscope.expanded.drop
        (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
      H.recursorWF.mlctx.vlctx := by
    simpa [A.semantics.fieldRoot_vlctx] using HfieldBase
  rcases Hraw.defeqDFC H.outVEnvWF
      (HfieldBase'.symm H.outVEnvWF.ordered) with
    ⟨expandedRawTarget, HexpandedRaw⟩
  exact ⟨S, hypothesisOrigins, D, originRoot, sourceType, O,
    scope, Hscope, expandedRawTarget, expandedFieldDomains,
    semanticTarget, htype, hfieldDomains, HexpandedRaw, Hsemantic,
    HfieldBase'⟩

/-- Pointwise field-closed form of the semantic recursive index spine.  Each
index is first closed over the call-local higher-order arguments and then
over the constructor fields, preserving the exact target list selected by
the validated motive telescope. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.finalFieldAbstractedSemanticIndices
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ (localDomains fieldDomains : List VExpr),
          localDomains.length = F.semantic.generated.localArgs.size ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          evidence.indices.length = F.telescope.indices.length ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext (fieldDomains ++ localDomains)
                H.recursorWF.mlctx.vlctx))
            ((F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
                ).toList.map fun index =>
              (index.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.all_args_bound.fvars localDomains.length)
            evidence.indices ∧
          ∀ source ∈
            ((F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
                ).toList.map fun index =>
              (index.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.all_args_bound.fvars localDomains.length),
            FVarsIn
              (· ∈ ExprArrayFVarIds stats.params)
              source := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.finalSemanticMotiveApplication with
    ⟨binding, evidence, hlength, Hindices, _Htr, _Htyped, _Hforall⟩
  let localDomains := MLCtxForallDomains F.semantic.current_context.mlctx
    F.semantic.generated.localArgs.size F.semantic.recent.size_le
  let fieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hlocal : localDomains.length =
      F.semantic.generated.localArgs.size :=
    F.semantic.current_context.onlyLams.forallDomains_length
      F.semantic.generated.localArgs.size F.semantic.recent.size_le
  have hfields : fieldDomains.length = A.rule.allArgs.size :=
    A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hlocalFvars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have hfieldFvars : A.semantics.fieldsRecent.fvars =
      A.rule.all_args_bound.fvars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have closeIndices : ∀ {sources targets : List _},
      List.Forall₂
          (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
          sources targets →
        List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext (fieldDomains ++ localDomains)
                H.recursorWF.mlctx.vlctx))
            (sources.map fun index =>
              (index.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.all_args_bound.fvars localDomains.length)
            targets := by
    intro sources targets Hsource
    induction Hsource with
    | nil => exact .nil
    | @cons source target sources targets Hindex _ ih =>
      have Hlocal := F.semantic.recent.abstractRecent [] (by
        simpa [abstractForallContext] using Hindex)
      have Hlocal' : TrExprS H.outVEnv Us
          (abstractForallContext localDomains
            A.semantics.context.mlctx.vlctx)
          (source.abstractList
            F.semantic.generated.arguments_bound.fvars) target := by
        simpa [localDomains, hlocalFvars] using Hlocal
      have Hfield := A.semantics.fieldsRecent.abstractRecent
        localDomains Hlocal'
      exact List.Forall₂.cons (by
        simpa [localDomains, fieldDomains, hlocalFvars,
          hfieldFvars, A.semantics.fieldRoot_vlctx] using Hfield) ih
  have HclosedIndices := closeIndices Hindices
  have Hscoped : ∀ source ∈
      ((F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
          ).toList.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars localDomains.length),
      FVarsIn (· ∈ ExprArrayFVarIds stats.params) source := by
    intro closedSource hclosedSource
    rcases List.mem_map.mp hclosedSource with ⟨source, hsource, rfl⟩
    have hsourceFull : source ∈
        F.semantic.generated.exposedType.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      rw [Subarray.toList_eq_drop_take,
        Array.array_toSubarray] at hsource
      exact List.mem_of_mem_take (List.mem_of_mem_drop hsource)
    have Hsource := F.semantic.exposed_scope.getAppArgsList hsourceFull
    have Hlocal := FVarsIn.abstractList_of
      (selected := F.semantic.recent.fvars) (k := 0) Hsource
    rw [F.root_scope] at Hlocal
    have Hfield := FVarsIn.abstractList_of
      (selected := A.semantics.fieldOpening.fvars)
      (k := localDomains.length) Hlocal
    have hopenFvars : A.semantics.fieldOpening.fvars =
        A.rule.all_args_bound.fvars :=
      A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound
    simpa [hlocalFvars, hopenFvars] using Hfield
  exact ⟨binding, evidence, localDomains, fieldDomains,
    hlocal, hfields, hlength, HclosedIndices, Hscoped⟩

/-- Domain-witness-free form of the source-scope conclusion above.  Once
call locals and constructor fields are abstracted, recursive indices mention
only the common inductive parameters; in particular they avoid every motive
and minor variable that will later be inserted into the equation context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedSemanticIndexSourcesScoped
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
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    ∀ source ∈ sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size,
      FVarsIn (· ∈ ExprArrayFVarIds stats.params) source := by
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  rcases F.finalFieldAbstractedSemanticIndices with
    ⟨_binding, _evidence, localDomains, _fieldDomains,
      hlocal, _hfields, _hlength, _Hindices, Hscoped⟩
  simpa [hlocal] using Hscoped

/-- After closing call locals and constructor fields, the complete semantic
motive application mentions only the common parameters and motive binders.
In particular it is independent of every generated induction-hypothesis
identifier from the first pass. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedNormalizedMotiveSourceScope
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
    (F.semantic.generated.outerAbstractedMotiveApp
      A.rule.all_args_bound.fvars).FVarsIn fun fv =>
        fv ∈ ExprArrayFVarIds stats.params ++
          ExprArrayFVarIds (H.recInfos.map (·.motive)) := by
  let P := fun fv => fv ∈ ExprArrayFVarIds stats.params ++
    ExprArrayFVarIds (H.recInfos.map (·.motive))
  have hselectedOwner : F.semantic.generated.ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hselectedMotive : F.semantic.generated.ownerIdx <
      (H.recInfos.map (·.motive)).size := by
    simpa using hselectedOwner
  rcases A.rule.motives_bound.getElem_eq_fvar
      F.semantic.generated.ownerIdx hselectedMotive with
    ⟨hselectedMotiveFVars, hmot⟩
  let motiveFVar :=
    A.rule.motives_bound.fvars[F.semantic.generated.ownerIdx]
  have hmotBang : (H.recInfos.map (·.motive))[
      F.semantic.generated.ownerIdx]! = .fvar motiveFVar := by
    rw [getElem!_pos (H.recInfos.map (·.motive))
      F.semantic.generated.ownerIdx hselectedMotive]
    simpa [motiveFVar] using hmot
  have hmotiveScope : (Expr.fvar motiveFVar).FVarsIn P := by
    change P motiveFVar
    apply List.mem_append_right
    rw [A.rule.motives_bound.exprArrayFVarIds]
    exact List.getElem_mem hselectedMotiveFVars
  have hmotiveLocal :
      ((Expr.fvar motiveFVar).abstractList
        F.semantic.generated.arguments_bound.fvars).FVarsIn P := by
    apply FVarsIn.abstractList_of
    exact hmotiveScope.mono fun fv hfv => Or.inr hfv
  have hmotiveFields :
      (((Expr.fvar motiveFVar).abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
          F.semantic.generated.localArgs.size).FVarsIn P := by
    apply FVarsIn.abstractList_of
    exact hmotiveLocal.mono fun fv hfv => Or.inr hfv
  have Hindices := F.fieldAbstractedSemanticIndexSourcesScoped
  have hindicesScope : ∀ index ∈
      (F.semantic.generated.replayTrace
        A.rule.all_args_bound.fvars).indices,
      index.FVarsIn P := by
    intro index hindex
    simp only [BoundGeneratedRecursiveCall.replayTrace] at hindex
    rcases Array.mem_map.mp hindex with ⟨source, hsource, rfl⟩
    apply (Hindices _ ?_).mono
    · intro fv hparam
      exact List.mem_append_left _ hparam
    · apply List.mem_map.mpr
      refine ⟨source, ?_, rfl⟩
      rw [← Subarray.toList_toArray]
      exact Array.mem_toList_iff.mpr hsource
  rcases F.finalAppliedMajorTarget with
    ⟨_localDomains, _fieldDomains, fieldFVar, _fieldVar,
      _hlocal, _hfields, _hfieldVar, hfieldEq, hfield,
      _hfieldSource, _Hmajor, _htarget⟩
  have hfieldRoot : fieldFVar ∈ A.rule.root.lctx.fvars :=
    A.rule.all_args_bound.members fieldFVar hfield
  rcases F.semantic.generated.outerAbstractedMajor_eq_bvar_of_field_eq
      hfieldEq hfieldRoot A.rule.all_args_nodup hfield with
    ⟨fieldVar, _hfieldVarBound, _hfieldAbstract, hmajorShape⟩
  have hmajorScope :
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars).FVarsIn P := by
    rw [hmajorShape, Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · trivial
    · intro arg harg
      have harg' : arg ∈
          F.semantic.generated.localIndices.map Expr.bvar := by
        simpa using harg
      rcases List.mem_map.mp harg' with ⟨index, _hindex, rfl⟩
      trivial
  unfold BoundGeneratedRecursiveCall.outerAbstractedMotiveApp
  change FVarsIn P (Expr.app _ _)
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · simpa [BoundGeneratedRecursiveCall.replayTrace, hmotBang]
        using hmotiveFields
    · intro index hindex
      exact hindicesScope index (Array.mem_toList_iff.mp hindex)
  · exact hmajorScope

/-- Closing the remaining outer rule binders around the field-normalized
motive application is exactly the one-shot full rule abstraction. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedNormalizedMotiveSource
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
    let outer := (A.rule.params_bound.fvars ++
      A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
    (F.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars).abstractList outer
          (F.semantic.generated.localArgs.size +
            A.rule.all_args_bound.fvars.length) =
      F.semantic.generated.outerAbstractedMotiveApp A.rule.binders := by
  let outer := (A.rule.params_bound.fvars ++
    A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[F.semantic.generated.ownerIdx]!
      F.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      F.semantic.generated.localArgs)
  have hfields := F.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.all_args_bound.fvars
  have hfull := F.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.binders
  dsimp only at hfields hfull
  have happend := Expr.abstractList_after_inner
    (e := motiveApp.abstractList
      F.semantic.generated.arguments_bound.fvars)
    (outer := outer) (inner := A.rule.all_args_bound.fvars)
    (k := F.semantic.generated.localArgs.size) (by
      simpa [outer, BoundGeneratedRecursorRule.binders,
        List.append_assoc] using A.rule.binders_nodup)
  have hfields' :
      (motiveApp.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size =
        F.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars := by
    simpa [motiveApp] using hfields
  have hfull' :
      (motiveApp.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          (outer ++ A.rule.all_args_bound.fvars)
            F.semantic.generated.localArgs.size =
        F.semantic.generated.outerAbstractedMotiveApp A.rule.binders := by
    simpa [motiveApp, outer, BoundGeneratedRecursorRule.binders,
      List.append_assoc] using hfull
  rw [hfields'] at happend
  exact happend.trans hfull'

/-- Restrict every semantic recursive index to the replayed
parameter/field/local scope while retaining its exact relationship to the
target produced in the executable context.  This is the pointwise inverse
weakening step needed before the retained front is closed. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowSemanticIndices
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
            scope.fvars = F.semantic.recent.fvars.reverse ++
              A.semantics.fieldsRecent.fvars.reverse ++
                parameterDecls.fvars ∧
            scope.drop Hscope.frontSourceDomains.length = parameterDecls ∧
            ∃ localDomains,
              localDomains.length = F.semantic.generated.localArgs.size ∧
              Hscope.frontSourceDomains = B.fieldDomains ++ localDomains ∧
              (∀ {body target},
                TrExprS H.outVEnv Us scope body target →
                H.outVEnv.IsType Us.length scope.toCtx target →
                TrExprS H.outVEnv Us B.fieldScope
                    (F.semantic.generated.current.lctx.mkForall
                      F.semantic.generated.localArgs body)
                    (VExpr.wrapForalls localDomains target) ∧
                  H.outVEnv.IsType Us.length B.fieldScope.toCtx
                    (VExpr.wrapForalls localDomains target)) ∧
            ∃ narrowIndices,
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂ (TrExprS H.outVEnv Us scope)
                sourceIndices narrowIndices ∧
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
  rcases F.finalSemanticMotiveApplication with
    ⟨binding, evidence, hlength, Hindices, _Happlication, _Htyping,
      _Hforall⟩
  rcases F.narrowLocalForallReplayFor B with
    ⟨scope, Hscope, hscopeFVars, hscopeBase,
      localDomains, hlocal, hfront, HforallReplay⟩
  have HsourceScope : ∀ source ∈ sourceIndices,
      source.FVarsIn (fun fv =>
        fv ∈ F.semantic.recent.fvars ∨ F.semantic.rootScope fv) := by
    intro source hsource
    have hsourceFull : source ∈
        F.semantic.generated.exposedType.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      change source ∈
        (F.semantic.generated.exposedType.getAppArgs.toSubarray
          stats.params.size).toList at hsource
      rw [Subarray.toList_eq_drop_take,
        Array.array_toSubarray] at hsource
      exact List.mem_of_mem_take (List.mem_of_mem_drop hsource)
    exact F.semantic.exposed_scope.getAppArgsList hsourceFull
  have hnarrow : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
          (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
          sources targets →
      sources ⊆ sourceIndices →
      ∃ narrowTargets,
        List.Forall₂ (TrExprS H.outVEnv Us scope)
          sources narrowTargets ∧
        List.Forall₂
          (fun narrow full => H.outVEnv.IsDefEqU Us.length
            F.semantic.current_context.mlctx.vlctx.toCtx
            (narrow.lift' Hscope.shift) full)
          narrowTargets targets := by
    intro sources targets Htranslated hsubset
    induction Htranslated with
    | nil => exact ⟨[], .nil, .nil⟩
    | @cons source target sources targets Hindex _ ih =>
      have hsource : source ∈ sourceIndices :=
        hsubset (List.mem_cons_self)
      have Hsource := HsourceScope source hsource
      have HsourceNarrow : source.FVarsIn (· ∈ scope.fvars) := by
        apply Hsource.mono
        intro fv hfv
        rw [F.root_scope,
          A.semantics.fieldOpening.fvars_eq_bound
            A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
          at hfv
        rw [hscopeFVars, H.parameterSuffix.parameterDecls_fvars]
        rcases hfv with hlocal | hfield | hparam
        · simp only [List.mem_append]
          exact Or.inl (Or.inl (List.mem_reverse.mpr hlocal))
        · simp only [List.mem_append]
          exact Or.inl (Or.inr (List.mem_reverse.mpr hfield))
        · simp only [List.mem_append]
          exact Or.inr (List.mem_reverse.mpr hparam)
      have hclosed : Closed source 0 := by
        have h := Hindex.closed
        rw [F.semantic.current_context.mlctx.noBV] at h
        exact h
      rcases Hscope.restrictEq H.outVEnvWF Hindex hclosed HsourceNarrow with
        ⟨narrowTarget, HnarrowTarget, HtargetEq⟩
      have htailSubset : sources ⊆ sourceIndices := by
        intro other hother
        exact hsubset (List.mem_cons_of_mem _ hother)
      rcases ih htailSubset with ⟨narrowTargets, Hnarrow, Heq⟩
      exact ⟨narrowTarget :: narrowTargets,
        .cons HnarrowTarget Hnarrow, .cons HtargetEq.symm Heq⟩
  rcases hnarrow Hindices (by intro source; exact id) with
    ⟨narrowIndices, HnarrowIndices, HindexEq⟩
  exact ⟨binding, evidence, scope, Hscope, hscopeFVars, hscopeBase,
    localDomains, hlocal, hfront, HforallReplay,
    narrowIndices, hlength, HnarrowIndices, HindexEq⟩

/-- Replay the eta-expanded recursive field in the same narrow runtime scope
used for its semantic indices.  The source contains only the selected
constructor field and the freshly introduced higher-order arguments, so the
ambient declarations discarded by `NarrowRuntimeScope` are irrelevant. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowSemanticAppliedMajor
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
    (scope : VLCtx)
    (Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
      H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      scope F.semantic.current_context.mlctx.vlctx)
    (hscopeFVars : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars) :
    ∃ narrowMajor,
      TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope
        (mkAppN A.rule.recursiveArgs[j]
          F.semantic.generated.localArgs) narrowMajor ∧
      H.outVEnv.IsDefEqU
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        F.semantic.current_context.mlctx.vlctx.toCtx
        F.semantic.appliedFieldTarget (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
    ⟨hjFVars, hfieldSource⟩
  let fv := A.rule.recursive_args_bound.fvars[j]
  have hfieldAll : fv ∈ A.rule.all_args_bound.fvars :=
    A.rule.recursive_args_bound.fvars_subset_of_sublist
      A.rule.all_args_bound A.rule.recursive_args_sublist
      (List.getElem_mem hjFVars)
  have hfieldRecent : fv ∈ A.semantics.fieldsRecent.fvars := by
    have hfvars : A.semantics.fieldsRecent.fvars =
        A.rule.all_args_bound.fvars :=
      BoundFVarArray.fvars_eq
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
        A.rule.all_args_bound rfl
    rw [hfvars]
    exact hfieldAll
  have hlocalFVars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have hsourceScope :
      (mkAppN A.rule.recursiveArgs[j]
        F.semantic.generated.localArgs).FVarsIn
          (· ∈ scope.fvars) := by
    rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · rw [hfieldSource]
      change fv ∈ scope.fvars
      rw [hscopeFVars]
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_reverse.mpr hfieldRecent))
    · intro arg harg
      have harg' : arg ∈
          F.semantic.generated.arguments_bound.fvars.map Expr.fvar := by
        simpa [F.semantic.generated.arguments_bound.expressions] using harg
      rcases List.mem_map.mp harg' with ⟨localFv, hlocal, rfl⟩
      have hlocalRecent : localFv ∈ F.semantic.recent.fvars := by
        rw [hlocalFVars]
        exact hlocal
      change localFv ∈ scope.fvars
      rw [hscopeFVars]
      exact List.mem_append_left _
        (List.mem_append_left _
          (List.mem_reverse.mpr hlocalRecent))
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (A.semantics.context_venv.trans
        H.recursorEnv)
  have Hmajor := F.semantic.applied_field_translation
  rw [hsemantic] at Hmajor
  have HmajorFinal := Hmajor.mono H.installed.le
  have hclosed : Closed
      (mkAppN A.rule.recursiveArgs[j]
        F.semantic.generated.localArgs) 0 := by
    have h := HmajorFinal.closed
    rw [F.semantic.current_context.mlctx.noBV] at h
    exact h
  rcases Hscope.restrictEq H.outVEnvWF HmajorFinal hclosed hsourceScope with
    ⟨narrowMajor, HnarrowMajor, HmajorEq⟩
  exact ⟨narrowMajor, HnarrowMajor, HmajorEq⟩

/-- Restrict the recursive field's exposed inductive type to the same replayed
scope used for its indices and eta-expanded major.  The resulting narrow
target remains a type and is definitionally related to the semantic target
in the full executable context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowSemanticExposedType
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
    (scope : VLCtx)
    (Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
      H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      scope F.semantic.current_context.mlctx.vlctx)
    (hscopeFVars : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ narrowExposed resultLevel,
      TrExprS H.outVEnv Us scope F.semantic.generated.exposedType
        narrowExposed ∧
      H.outVEnv.IsDefEqU Us.length
        F.semantic.current_context.mlctx.vlctx.toCtx
        (narrowExposed.lift' Hscope.shift) F.semantic.exposedTarget ∧
      H.outVEnv.HasType Us.length scope.toCtx narrowExposed
        (.sort resultLevel) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  have hsourceScope : F.semantic.generated.exposedType.FVarsIn
      (· ∈ scope.fvars) := by
    apply F.semantic.exposed_scope.mono
    intro fv hfv
    rw [F.root_scope,
      A.semantics.fieldOpening.fvars_eq_bound
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
      at hfv
    rw [hscopeFVars, H.parameterSuffix.parameterDecls_fvars]
    rcases hfv with hlocal | hfield | hparam
    · exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_reverse.mpr hlocal))
    · exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_reverse.mpr hfield))
    · exact List.mem_append_right _ (List.mem_reverse.mpr hparam)
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (A.semantics.context_venv.trans
        H.recursorEnv)
  have Hfull := F.semantic.exposed_translation
  have HfullType : F.semantic.current_context.venv.IsType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.exposedTarget :=
    VEnv.IsType.defeqU_l F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm F.semantic.terminal_type
  rw [hsemantic] at Hfull HfullType
  have HfullFinal := Hfull.mono H.installed.le
  have HfullTypeFinal := HfullType.mono H.installed.le
  have hclosed : Closed F.semantic.generated.exposedType 0 := by
    have h := HfullFinal.closed
    rw [F.semantic.current_context.mlctx.noBV] at h
    exact h
  rcases Hscope.restrictEq H.outVEnvWF HfullFinal hclosed hsourceScope with
    ⟨narrowExposed, HnarrowExposed, HexposedEq⟩
  rcases HfullTypeFinal with ⟨resultLevel, Htyped⟩
  have HnarrowTyped := Hscope.hasTypeOfFull H.outVEnvWF
    HnarrowExposed HfullFinal Htyped
  exact ⟨narrowExposed, resultLevel, HnarrowExposed,
    HexposedEq.symm, HnarrowTyped⟩

/-- The narrowed eta-expanded major has the narrowed exposed inductive type.
Both translations are restricted through the same runtime-scope witness, so
the dependent term/type relation survives inverse weakening exactly. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowSemanticAppliedMajorTyping
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
    (scope : VLCtx)
    (Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
      H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      scope F.semantic.current_context.mlctx.vlctx)
    (hscopeFVars : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ narrowMajor narrowExposed,
      TrExprS H.outVEnv Us scope
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs) narrowMajor ∧
        TrExprS H.outVEnv Us scope F.semantic.generated.exposedType
          narrowExposed ∧
        H.outVEnv.HasType Us.length scope.toCtx narrowMajor narrowExposed := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.narrowSemanticAppliedMajor scope Hscope hscopeFVars with
    ⟨narrowMajor, HnarrowMajor, _HmajorEq⟩
  rcases F.narrowSemanticExposedType scope Hscope hscopeFVars with
    ⟨narrowExposed, _resultLevel, HnarrowExposed, _HexposedEq,
      _HnarrowType⟩
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (A.semantics.context_venv.trans
        H.recursorEnv)
  have HfullMajor := F.semantic.applied_field_translation
  have HfullExposed := F.semantic.exposed_translation
  have HfullMajorType : F.semantic.current_context.venv.HasType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.appliedFieldTarget F.semantic.exposedTarget :=
    F.semantic.applied_field_typing.defeqU_r
      F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm
  rw [hsemantic] at HfullMajor HfullExposed HfullMajorType
  have Htyped := Hscope.hasTypeOfFullPair H.outVEnvWF
    HnarrowMajor HnarrowExposed
    (HfullMajor.mono H.installed.le)
    (HfullExposed.mono H.installed.le)
    (HfullMajorType.mono H.installed.le)
  exact ⟨narrowMajor, narrowExposed, HnarrowMajor, HnarrowExposed, Htyped⟩

/-- Type any particular narrow translation of the eta-expanded recursive
major.  This parameterized form is the bridge used by the later cached
equation frame: it retains that frame's exact target instead of choosing a
second existential translation and subsequently appealing to uniqueness. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowSemanticAppliedMajorTypingFor
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
    (scope : VLCtx)
    (Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
      H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      scope F.semantic.current_context.mlctx.vlctx)
    (hscopeFVars : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars)
    {narrowMajor : VExpr}
    (HnarrowMajor : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope
      (mkAppN A.rule.recursiveArgs[j]
        F.semantic.generated.localArgs) narrowMajor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ narrowExposed,
      TrExprS H.outVEnv Us scope F.semantic.generated.exposedType
          narrowExposed ∧
        H.outVEnv.HasType Us.length scope.toCtx narrowMajor narrowExposed := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.narrowSemanticExposedType scope Hscope hscopeFVars with
    ⟨narrowExposed, _resultLevel, HnarrowExposed, _HexposedEq,
      _HnarrowType⟩
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (A.semantics.context_venv.trans
        H.recursorEnv)
  have HfullMajor := F.semantic.applied_field_translation
  have HfullExposed := F.semantic.exposed_translation
  have HfullMajorType : F.semantic.current_context.venv.HasType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.appliedFieldTarget F.semantic.exposedTarget :=
    F.semantic.applied_field_typing.defeqU_r
      F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm
  rw [hsemantic] at HfullMajor HfullExposed HfullMajorType
  have Htyped := Hscope.hasTypeOfFullPair H.outVEnvWF
    HnarrowMajor HnarrowExposed
    (HfullMajor.mono H.installed.le)
    (HfullExposed.mono H.installed.le)
    (HfullMajorType.mono H.installed.le)
  exact ⟨narrowExposed, HnarrowExposed, Htyped⟩

/-- The replayed narrow front is exactly the constructor fields followed by
the higher-order call arguments, in source-binder order.  This packages the
ordering, arity, and well-formedness facts shared by index and major closure. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowRuntimeFrontAlignment
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
    (scope : VLCtx)
    (Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope
      H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      scope F.semantic.current_context.mlctx.vlctx)
    (hscopeFVars : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars)
    (hscopeBase : scope.drop Hscope.frontSourceDomains.length =
      H.parameterSuffix.parameterDecls) :
    (VLCtx.fvars
        (scope.take Hscope.frontSourceDomains.length)).reverse =
      A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars ∧
    Hscope.frontSourceDomains.length =
      A.rule.allArgs.size + F.semantic.generated.localArgs.size ∧
    OnCtx
      (abstractForallContext Hscope.frontSourceDomains
        H.parameterSuffix.parameterDecls).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
  let parameterDecls := H.parameterSuffix.parameterDecls
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
  have hlengthNames := congrArg List.length hfrontFVars
  have hfrontLength : Hscope.frontSourceDomains.length =
      A.rule.allArgs.size + F.semantic.generated.localArgs.size := by
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
          F.semantic.generated.arguments_bound.fvars).length := by
        simpa using hlengthNames
      _ = A.rule.allArgs.size +
          F.semantic.generated.localArgs.size := by
        simp [A.rule.all_args_bound.length_fvars,
          F.semantic.generated.arguments_bound.length_fvars]
  exact ⟨hfrontFVars, hfrontLength,
    Hscope.abstractFrontWF H.outVEnvWF hscopeBase⟩


end VerifyInductive
end Lean4Lean
