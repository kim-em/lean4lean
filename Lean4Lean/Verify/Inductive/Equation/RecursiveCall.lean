import Lean4Lean.Verify.Inductive.Equation.RecursiveCallScope

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

open checkInductiveTypes.loopType

theorem RecursorPhasesResult.constructorVEnv_le
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
    R.declared.venvCtors ≤ H.outVEnv :=
  VEnv.addEliminators_addProjections_le.trans H.installed.le

/-- Every retained constructor-field variable is present in the exact
producer root of this recursive call.  Earlier induction hypotheses may make
that root strictly larger than the common field context, so consumers must
use the retained extension rather than identify the two contexts. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.field_mem_originRoot
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
    {fv : FVarId} (hfv : fv ∈ A.rule.all_args_bound.fvars) :
    fv ∈ F.originRoot.lctx.fvars := by
  have hfieldRecent : fv ∈ A.semantics.fieldsRecent.fvars := by
    rw [BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl]
    exact hfv
  exact F.originExtension.contextLE.fvars
    (A.semantics.fieldsRecent.members fv hfieldRecent)

/-- Every identifier selected by the producer's root-scope predicate is an
actual declaration of its staged origin context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScope_mem_originContext
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
    {fv : FVarId} (hfv : F.semantic.rootScope fv) :
    fv ∈ F.originContext.mlctx.vlctx.fvars := by
  rw [F.root_scope] at hfv
  have hcommon : fv ∈ A.semantics.context.mlctx.vlctx.fvars := by
    rcases hfv with hfield | hparam
    · have hfieldRecent : fv ∈ A.semantics.fieldsRecent.fvars := by
        rw [← A.semantics.fieldOpening.fvars_eq_bound
          A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
        exact hfield
      have hraw := A.semantics.fieldsRecent.members fv hfieldRecent
      rw [← A.semantics.context.lctx_eq,
        A.semantics.context.mlctx_wf.tr.fvars_eq] at hraw
      exact hraw
    · have hparamDecl : fv ∈
          A.semantics.parameterSuffix.parameterDecls.fvars := by
        rw [A.semantics.parameterSuffix.parameterDecls_fvars]
        exact List.mem_reverse.mpr hparam
      have hroot : fv ∈
          A.semantics.fieldRootContext.mlctx.vlctx.fvars := by
        rw [A.semantics.parameterSuffix.context, VLCtx.fvars_append]
        exact List.mem_append_right _ hparamDecl
      have hraw : fv ∈ A.semantics.fieldRoot.lctx.fvars := by
        rw [← A.semantics.fieldRootContext.lctx_eq,
          A.semantics.fieldRootContext.mlctx_wf.tr.fvars_eq]
        exact hroot
      have hraw' := A.semantics.fieldsRecent.contextLE.fvars hraw
      rw [← A.semantics.context.lctx_eq,
        A.semantics.context.mlctx_wf.tr.fvars_eq] at hraw'
      exact hraw'
  have horigin := F.originExtension.contextLE.fvars <| by
    rw [← A.semantics.context.lctx_eq,
      A.semantics.context.mlctx_wf.tr.fvars_eq]
    exact hcommon
  rw [← F.originContext.lctx_eq,
    F.originContext.mlctx_wf.tr.fvars_eq] at horigin
  exact horigin

/-- The producer-root part of a recursive call's retained source scope is
dependency closed in the exact producer context.  The proof drops only the
fresh call-local lambda suffix from the producer's existing up-set; it does
not identify the producer context with the earlier common field context, so
earlier generated induction hypotheses may remain ambient and unselected. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScope_up
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
    (F : A.RecursiveCallRecursorFrame j hj) :
    IsFVarUpSet F.semantic.rootScope
      F.originContext.mlctx.vlctx := by
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨_domains, HlocalPrefix⟩
  have Htail := HlocalPrefix.dropN_isFVarUpSet
    F.semantic.current_scope_up
  have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
    Subsingleton.elim _ _
  rw [hle, F.semantic.recent.drop_eq] at Htail
  apply (IsFVarUpSet.congr
    F.originContext.mlctx_wf.tr.wf.fvwf ?_).mp Htail
  intro fv hfv
  constructor
  · intro hselected
    rcases hselected with hrecent | hroot
    · exact False.elim <| F.semantic.recent.fresh fv hrecent <| by
        rw [← F.originContext.lctx_eq,
          F.originContext.mlctx_wf.tr.fvars_eq]
        exact hfv
    · exact hroot
  · exact Or.inr

/-- Closing first the call-local higher-order arguments and then the complete
constructor-field suffix removes every dependency except the cached inductive
parameters.  This is the narrow source-scope fact needed to replay a generated
recursive call in the cached equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedExposedScope
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
    (F : A.RecursiveCallRecursorFrame j hj) :
    ((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
      A.rule.all_args_bound.fvars
      F.semantic.generated.localArgs.size).FVarsIn
        F.semantic.rootScope := by
  have hlocalFvars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have Hlocal := FVarsIn.abstractList_of
    (selected := F.semantic.recent.fvars)
    (k := 0) F.semantic.exposed_scope
  have Hfields := FVarsIn.abstractList_of
    (selected := A.rule.all_args_bound.fvars)
    (k := F.semantic.generated.localArgs.size)
    (Hlocal.mono fun _ hfv => Or.inr hfv)
  simpa [hlocalFvars] using Hfields

/-- First-class rule-wide field narrowing witness.  Recursive-result folds
retain one value of this structure and replay every call-local suffix above
its exact `fieldDomains`. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) where
  fieldScope : VLCtx
  runtime : checkInductiveTypes.loopType.NarrowRuntimeScope
    A.semantics.fieldRootContext.venv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    fieldScope A.semantics.context.mlctx.vlctx
  scope_fvars : fieldScope.fvars =
    A.semantics.fieldsRecent.fvars.reverse ++
      A.semantics.parameterSuffix.parameterDecls.fvars
  scope_base : fieldScope.drop runtime.frontSourceDomains.length =
    A.semantics.parameterSuffix.parameterDecls
  fieldDomains : List VExpr
  fieldDomains_length : fieldDomains.length = A.rule.allArgs.size
  front : runtime.frontSourceDomains = fieldDomains
  forwardDomains : List VExpr
  forwardResidual : VExpr
  forwardDomains_length : forwardDomains.length = A.rule.allArgs.size
  forwardTarget :
    (VExpr.wrapForalls A.semantics.fieldTelescope.domains
      A.semantics.targetTarget).lift'
        (A.semantics.fieldRootExtension.shift.consN 0) =
      VExpr.wrapForalls forwardDomains forwardResidual

/-- The rule-wide narrowing frame is literally the constructor-field
telescope abstracted over the cached parameter declarations.  This exposes
the context hidden behind `NarrowRuntimeScope` in the form used by the
selected-minor translation. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.fieldScope_eq
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
    (B : A.NarrowFieldRuntimeFrame) :
    B.fieldScope.toCtx =
      (abstractForallContext B.fieldDomains
        A.semantics.parameterSuffix.parameterDecls).toCtx := by
  rw [abstractForallContext_toCtx, B.runtime.front.sourceContext,
    B.scope_base, B.front]

/-- The source identifiers closed by the fixed field narrowing frame are
literally the generated rule's constructor-field identifiers, in source
binder order. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.frontFVars
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
    (B : A.NarrowFieldRuntimeFrame) :
    (VLCtx.fvars
      (B.fieldScope.take B.runtime.frontSourceDomains.length)).reverse =
        A.rule.all_args_bound.fvars := by
  have hsplit := B.runtime.frontFVars B.scope_base
  have happend :
      VLCtx.fvars
          (B.fieldScope.take B.runtime.frontSourceDomains.length) ++
          A.semantics.parameterSuffix.parameterDecls.fvars =
        A.semantics.fieldsRecent.fvars.reverse ++
          A.semantics.parameterSuffix.parameterDecls.fvars := by
    rw [← hsplit, B.scope_fvars]
  have hfields : VLCtx.fvars
      (B.fieldScope.take B.runtime.frontSourceDomains.length) =
        A.semantics.fieldsRecent.fvars.reverse :=
    List.append_cancel_right happend
  rw [hfields, List.reverse_reverse]
  exact BoundFVarArray.fvars_eq
    A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    A.rule.all_args_bound rfl

private theorem cachedParameterCoreDeclarations
    {params : List Expr} {scope : VLCtx}
    (H : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl params scope) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      scope.fvars scope := by
  induction H with
  | nil => exact .nil
  | cons h _ ih =>
    rcases h with ⟨fv, deps, type, _hparam, rfl⟩
    exact .cons ⟨deps, type, rfl⟩ ih


/-- The narrowed constructor-field telescope is well formed in the final
recursor environment, over the exact cached parameter suffix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.fieldContextWF
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
    (B : A.NarrowFieldRuntimeFrame) :
    OnCtx
      (abstractForallContext B.fieldDomains
        A.semantics.parameterSuffix.parameterDecls).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv_legacy, R.declared.contextVEnv]
    exact H.installed.le
  have hfieldBase : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq]
    exact hbase
  have Hruntime := B.runtime.mono hfieldBase
  have Hscope := Hruntime.scopeWF H.outVEnvWF
  rw [← B.fieldScope_eq]
  exact Hscope.toCtx

/-- Expose the rule-wide narrowing conversion before any call-local
higher-order arguments are added.  The expanded narrow context is related to
the literal field suffix of the executable semantic context, and dropping
that suffix reaches the common recursor root on both sides. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.semanticFieldContext
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
    rw [H.recursorEnv_legacy, R.declared.contextVEnv]
    exact H.installed.le
  have hfieldBaseEnv : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq]
    exact hbase
  let Hruntime := B.runtime.mono hfieldBaseEnv
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedFieldAlignmentFor
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
        (B.forwardDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSemanticFieldAlignmentFor S HS htail hfields with
    ⟨minorConsumedDomains, minorConsumedResidual,
      ruleConsumedDomains, ruleConsumedResidual,
      hminor, hminorTarget, hrule, hruleTarget, Hminor⟩
  have hruleDomains : ruleConsumedDomains = B.forwardDomains := by
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) hrule
      B.forwardDomains_length (by
        simpa using hruleTarget.symm.trans B.forwardTarget)
  rw [hruleDomains] at Hminor
  exact ⟨minorConsumedDomains, minorConsumedResidual, hminor,
    hminorTarget, Hminor⟩

/-- Compose the selected minor's transported consumed fields with the
rule-wide narrowing conversion.  The result relates the literal first-pass
field suffix to the expanded narrow context used by the canonical recursive
results, with no call-local declarations present. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedFieldAlignment
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
            (B.forwardDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSemanticSource with
    ⟨S, HS, _hlocal, htail⟩
  have hfields : S.fields.size = A.rule.allArgs.size := by
    have htraversalFields := HS.semantic.traversal_fields
    have hsemanticFields := congrArg Array.size htraversalFields
    have hterminal := HS.semantic.traversal.fieldTelescope
    have hrule := A.semantics.fieldOpening.telescope
    rw [htail] at hterminal
    have hsemanticResidual :
        A.semantics.fieldOpening.residual.isForall = false := by
      rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
      exact A.semantics.target_not_forall
    exact hsemanticFields.symm.trans
      (hterminal.eq_of_residual_not_forall hrule
        HS.semantic.traversal.fieldResidual_not_forall
        hsemanticResidual).1
  rcases A.finalSelectedMinorExpandedFieldAlignmentFor B S HS htail hfields with
    ⟨minorConsumedDomains, _minorConsumedResidual, hminor,
      _hminorTarget, Haligned⟩
  exact ⟨S, HS, minorConsumedDomains, hminor, Haligned⟩

/-- Retain the untranslated source telescope while composing the selected
minor's field conversion with the rule-wide narrowing conversion.  This is
the cancellation-facing form of `finalSelectedMinorExpandedFieldAlignment`:
the source translation and the final expanded context now belong to one
existential witness, so no choice of intermediate consumed domains is lost. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExpandedSourceFieldAlignment
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
            (B.forwardDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorTransportedFieldContext with
    ⟨S, HS, sourceDomains, sourceResidual, consumedDomains,
      consumedResidual, _hlocal, htail, hsource, hconsumed,
      Hsource, hconsumedTarget, HsourceConsumed⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv_legacy, R.declared.contextVEnv]
    exact H.installed.le
  have Hsource' := Hsource.mono hbase
  have hfields : S.fields.size = A.rule.allArgs.size := by
    have htraversalFields := HS.semantic.traversal_fields
    have hsemanticFields := congrArg Array.size htraversalFields
    have hterminal := HS.semantic.traversal.fieldTelescope
    have hrule := A.semantics.fieldOpening.telescope
    rw [htail] at hterminal
    have hsemanticResidual :
        A.semantics.fieldOpening.residual.isForall = false := by
      rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
      exact A.semantics.target_not_forall
    exact hsemanticFields.symm.trans
      (hterminal.eq_of_residual_not_forall hrule
        HS.semantic.traversal.fieldResidual_not_forall
        hsemanticResidual).1
  rcases A.finalSelectedMinorExpandedFieldAlignmentFor B S HS htail hfields with
    ⟨minorConsumedDomains, minorConsumedResidual, hminor,
      hminorTarget, HminorNarrow⟩
  have hconsumedDomains : consumedDomains = minorConsumedDomains := by
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hconsumed hminor (by
        simpa using hconsumedTarget.symm.trans hminorTarget)
  rw [hconsumedDomains] at HsourceConsumed
  have HsourceExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (HsourceConsumed.mono hbase) HminorNarrow
  exact ⟨S, HS, sourceDomains, sourceResidual, hsource, htail,
    Hsource', HsourceExpanded⟩

/-- Domain-witness-free form of the source-scope conclusion above.  Once
call locals and constructor fields are abstracted, recursive indices mention
only the common inductive parameters; in particular they avoid every motive
and minor variable that will later be inserted into the equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedSemanticIndexSourcesScoped
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
    (F : A.RecursiveCallRecursorFrame j hj) :
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    ∀ source ∈ sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size,
      FVarsIn (· ∈ ExprArrayFVarIds stats.params) source := by
  dsimp only
  intro closedSource hclosedSource
  rcases List.mem_map.mp hclosedSource with ⟨source, hsource, rfl⟩
  have hsourceFull : source ∈
      F.semantic.generated.exposedType.getAppArgsList := by
    rw [← Expr.getAppArgs_toList]
    change source ∈
      (F.semantic.generated.exposedType.getAppArgs.toSubarray
        stats.params.size).toList at hsource
    rw [Subarray.toList_eq_drop_take,
      Array.array_toSubarray] at hsource
    exact List.mem_of_mem_take (List.mem_of_mem_drop hsource)
  have Hsource := F.semantic.exposed_scope.getAppArgsList hsourceFull
  have Hlocal := FVarsIn.abstractList_of
    (selected := F.semantic.recent.fvars) (k := 0) Hsource
  rw [F.root_scope] at Hlocal
  have Hfield := FVarsIn.abstractList_of
    (selected := A.semantics.fieldOpening.fvars)
    (k := F.semantic.generated.localArgs.size) Hlocal
  have hlocalFvars : F.semantic.recent.fvars =
      F.semantic.generated.arguments_bound.fvars :=
    BoundFVarArray.fvars_eq
      F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
      F.semantic.generated.arguments_bound.toBoundFVarArray rfl
  have hopenFvars : A.semantics.fieldOpening.fvars =
      A.rule.all_args_bound.fvars :=
    A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound
  simpa [hlocalFvars, hopenFvars] using Hfield

/-- After closing call locals and constructor fields, the complete semantic
motive application mentions only the common parameters and motive binders.
In particular it is independent of every generated induction-hypothesis
identifier from the first pass. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedNormalizedMotiveSourceScope
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
  rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
    ⟨hjFVars, hfieldEq⟩
  let fieldFVar := A.rule.recursive_args_bound.fvars[j]
  have hfield : fieldFVar ∈ A.rule.all_args_bound.fvars :=
    A.rule.recursive_args_bound.fvars_subset_of_sublist
      A.rule.all_args_bound A.rule.recursive_args_sublist
      (List.getElem_mem hjFVars)
  have hfieldRoot : fieldFVar ∈ F.originRoot.lctx.fvars :=
    F.field_mem_originRoot hfield
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
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedNormalizedMotiveSource
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
  have hfieldClosed : A.rule.recursiveArgs[j].looseBVarRange' = 0 :=
    F.semantic.fieldClosed
  have hfields := F.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.all_args_bound.fvars hfieldClosed
  have hfull := F.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.binders hfieldClosed
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


/-- The replayed narrow front is exactly the constructor fields followed by
the higher-order call arguments, in source-binder order.  This packages the
ordering, arity, and well-formedness facts shared by index and major closure. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowRuntimeFrontAlignment
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
