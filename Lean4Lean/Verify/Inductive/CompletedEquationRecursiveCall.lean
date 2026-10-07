import Lean4Lean.Verify.Inductive.CompletedEquationRecursiveCallScope

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

open checkInductiveTypes.loopType

theorem CompletedRecursorPhasesResult.constructorVEnv_le
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    R.context.venv ≤ H.outVEnv :=
  H.installed.le

/-- Every retained constructor-field variable is present in the exact
producer root of this recursive call.  Earlier induction hypotheses may make
that root strictly larger than the common field context, so consumers must
use the retained extension rather than identify the two contexts. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.field_mem_originRoot
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
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScope_mem_originContext
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
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScope_up
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
  /-- The narrow field scope is aligned with the checker context in which the
  fields were opened. -/
  checkAlign : 0 < A.rule.allArgs.size →
    VLCtx.IsDefEq A.semantics.fieldRootContext.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      fieldScope A.semantics.context.chk.vlctx

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
        A.semantics.parameterSuffix.parameterDecls).toCtx := by
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

/-- Forget only source-declaration provenance from the fixed field frame.
The resulting dependency-selection core retains its exact cached parameter
and field targets, which are the targets consumed by equation assembly. -/
def CompletedRecursorPhasesResult.GeneratedRuleAlignment.NarrowFieldRuntimeFrame.core
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
    checkInductiveTypes.loopType.FVarNarrowCore H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      B.fieldScope A.semantics.context.mlctx.vlctx := by
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
  have hfieldBase : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq]
    exact hbase
  let Hruntime := B.runtime.mono hfieldBase
  have Hfront := Hruntime.front.sourceDeclarations
  have Hparams := cachedParameterCoreDeclarations
    H.parameterSuffix.cached
  have Hdeclarations : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      B.fieldScope.fvars B.fieldScope := by
    have Happ := Lean4Lean.VerifyInductive.List.Forall₂.append'
      Hfront Hparams
    have hscope : B.fieldScope.take Hruntime.frontSourceDomains.length ++
        H.parameterSuffix.parameterDecls = B.fieldScope := by
      change B.fieldScope.take B.runtime.frontSourceDomains.length ++
        H.parameterSuffix.parameterDecls = B.fieldScope
      rw [← A.parameterDecls_eq, ← B.scope_base]
      exact List.take_append_drop B.runtime.frontSourceDomains.length
        B.fieldScope
    rw [← hscope, VLCtx.fvars_append]
    simpa [Hruntime,
      checkInductiveTypes.loopType.NarrowRuntimeScope.mono] using Happ
  exact {
    expanded := Hruntime.expanded
    shift := Hruntime.shift
    lift := Hruntime.lift
    context := Hruntime.context
    upset := Hruntime.upset
    noBV := Hruntime.noBV
    declarations := Hdeclarations
    wf := Hruntime.wf }

/-- Extend the exact cached field core through the producer's skipped prior
hypotheses and then through this call's retained higher-order locals.  The
target telescope is definitionally based on `B.fieldScope`; non-contiguity
is represented solely by the core weakening. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.currentCachedNarrowCore
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
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowCore H.outVEnv Us
          scope F.semantic.current_context.mlctx.vlctx,
        scope.fvars = F.semantic.recent.fvars.reverse ++
          B.fieldScope.fvars ∧
        scope.drop F.semantic.generated.localArgs.size = B.fieldScope ∧
        ∃ localDomains : List VExpr,
          localDomains.length = F.semantic.generated.localArgs.size ∧
          scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
          (∀ {body target},
            TrExprS H.outVEnv Us scope body target →
            H.outVEnv.IsType Us.length scope.toCtx target →
            TrExprS H.outVEnv Us B.fieldScope
                (F.semantic.generated.current.lctx.mkForall
                  F.semantic.generated.localArgs body)
                (VExpr.wrapForalls localDomains target) ∧
              H.outVEnv.IsType Us.length B.fieldScope.toCtx
                (VExpr.wrapForalls localDomains target)) ∧
          ChkEmbeds H.outVEnv Us.length
            F.semantic.current_context.chk.vlctx scope := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let Hfield := B.core
  rcases F.originContext.onlyLams.lamPrefix
      F.priorHypotheses.size F.originRecent.size_le with
    ⟨_priorDomains, HpriorPrefix⟩
  have hpriorBase :
      (F.originContext.mlctx.dropN F.priorHypotheses.size
        HpriorPrefix.le).vlctx = A.semantics.context.mlctx.vlctx := by
    have hle : HpriorPrefix.le = F.originRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.originRecent.drop_eq]
  let HpriorBase := Hfield.retargetRuntime hpriorBase.symm
  have HoriginWF : F.originContext.mlctx.WF H.outVEnv Us := by
    have henv : F.originContext.venv ≤ H.outVEnv := by
      rw [F.originRecent.venv_eq, A.semantics.context_venv,
        H.recursorEnv]
      exact H.constructorVEnv_le
    exact F.originContext.mlctx_wf.mono henv
  have hpriorSkip : ∀ fv ∈ F.originContext.mlctx.fvarRevList
      F.priorHypotheses.size HpriorPrefix.le,
      fv ∉ B.fieldScope.fvars := by
    intro fv hfv hselected
    have hle : HpriorPrefix.le = F.originRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.originRecent.fvarRevList_eq] at hfv
    apply F.originRecent.fresh fv (List.mem_reverse.mp hfv)
    rw [← A.semantics.context.lctx_eq,
      A.semantics.context.mlctx_wf.tr.fvars_eq]
    have hexpanded : fv ∈ Hfield.expanded.fvars :=
      Hfield.lift.fvars_sublist.subset hselected
    rw [Hfield.context.fvars] at hexpanded
    exact hexpanded
  rcases HpriorPrefix.skipFVarNarrowCore H.outVEnvWF HoriginWF
      ⟨HpriorBase⟩ hpriorSkip with ⟨Horigin⟩
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨_localSourceDomains, HlocalPrefix⟩
  have hlocalBase :
      (F.semantic.current_context.mlctx.dropN
        F.semantic.generated.localArgs.size HlocalPrefix.le).vlctx =
          F.originContext.mlctx.vlctx := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.semantic.recent.drop_eq]
  let HlocalBase := Horigin.retargetRuntime hlocalBase.symm
  have HlocalWF : F.semantic.current_context.mlctx.WF H.outVEnv Us := by
    have henv : F.semantic.current_context.venv ≤ H.outVEnv := by
      rw [F.semantic.recent.venv_eq, F.originRecent.venv_eq,
        A.semantics.context_venv, H.recursorEnv]
      exact H.constructorVEnv_le
    exact F.semantic.current_context.mlctx_wf.mono henv
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
            B.fieldScope.fvars)
      F.semantic.current_context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HlocalWF.tr.wf.fvwf ?_).mp
      F.semantic.current_scope_up
    intro fv _
    rw [F.root_scope, hlocalRev, B.scope_fvars,
      A.parameterDecls_eq, H.parameterSuffix.parameterDecls_fvars]
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
    simp [List.append_assoc]
  have hposFields : 0 < A.rule.allArgs.size := by
    have hlen := A.semantics.selection.fields_length
    have hne : A.semantics.fields ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    obtain ⟨cert, hcert⟩ := List.exists_mem_of_ne_nil _ hne
    have := A.semantics.selection.positions_lt cert hcert
    omega
  obtain ⟨hnC, hagreeC, jC, hjC, _ty₀, hdropC, _⟩ := F.semantic.chkAgree
  have hchkLocalWF : F.semantic.current_context.chk.WF H.outVEnv Us := by
    have henv : F.semantic.current_context.venv ≤ H.outVEnv := by
      rw [F.semantic.recent.venv_eq, F.originRecent.venv_eq,
        A.semantics.context_venv, H.recursorEnv]
      exact H.constructorVEnv_le
    exact F.semantic.current_context.check.wf.mono henv
  have hhn : HlocalPrefix.le = F.semantic.recent.size_le :=
    Subsingleton.elim _ _
  have hbaseEmb : ChkEmbeds H.outVEnv Us.length
      (F.semantic.current_context.chk.dropN
        F.semantic.generated.localArgs.size hnC).vlctx B.fieldScope := by
    rw [hdropC]
    have hchkEq : F.originContext.chk = A.semantics.context.chk :=
      F.originCheck
    have hjC' : jC ≤ A.semantics.context.chk.length := hchkEq ▸ hjC
    have key : ∀ (m m' : TypeChecker.MLCtx), m = m' → ∀ hj hj',
        (m.dropN jC hj).vlctx = (m'.dropN jC hj').vlctx := by
      intro m m' h hj hj'
      subst h
      rfl
    have hdropEq := key _ _ hchkEq hjC hjC'
    rw [hdropEq]
    have hfieldEnv : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
      rw [← A.semantics.fieldsRecent.venv_eq, A.semantics.context_venv,
        H.recursorEnv]
      exact H.constructorVEnv_le
    exact ⟨_, _, (A.semantics.context.check.onlyLams.dropN_fvlift jC hjC').toFVLift',
      ((B.checkAlign hposFields).mono hfieldEnv).symm H.outVEnvWF.ordered⟩
  rcases HlocalPrefix.extendFVarNarrowCoreEmbedded H.outVEnvWF HlocalWF
      HlocalBase HlocalUp hchkLocalWF hnC hagreeC hbaseEmb with
    ⟨scope, Hscope, hscope, hdrop, localDomains, hlocal,
      hcontext, _hshift, Hreplay, hembLocal⟩
  have hsource : ∀ body, Closed body →
      F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs body =
        F.semantic.current_context.mlctx.mkForall
          F.semantic.generated.localArgs.size HlocalPrefix.le body := by
    intro body hbody
    rw [← F.semantic.current_context.lctx_eq]
    refine F.semantic.current_context.mlctx_wf.mkForall_eq _ _ ?_ hbody
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.reverse_eq
  exact ⟨scope, Hscope, by simpa [hlocalRev] using hscope,
    hdrop, localDomains, hlocal, hcontext, by
      intro body target Hbody HbodyType
      rw [hsource body (by
        have h := Hbody.closed
        rwa [Hscope.noBV] at h)]
      simpa [HlocalBase,
        checkInductiveTypes.loopType.FVarNarrowCore.retargetRuntime] using
        Hreplay Hbody HbodyType, hembLocal⟩

theorem TrExprS.getAppArgsList_translations {env : VEnv} {Us : List Name}
    {Δ : VLCtx} {e : Expr} {t : VExpr} (H : TrExprS env Us Δ e t) :
    ∃ args', List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  rw [← Expr.mkAppList_getAppArgsList e] at H
  obtain ⟨_, args', _, hargs, _⟩ := checkPositivityStep.TrExprS.mkAppList_inv H
  exact ⟨args', hargs⟩

theorem _root_.List.Forall₂.drop_both {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ n : Nat,
      List.Forall₂ R (l.drop n) (l'.drop n)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => .cons h t
  | _, _, .cons _ t, n + 1 => t.drop_both n

theorem checkInductiveTypes.loopType.FVarNarrowCore.fullTargetEqs
    (H : checkInductiveTypes.loopType.FVarNarrowCore env Us scope runtime)
    (henv : env.WF) :
    ∀ {sources : List Expr} {narrow full : List VExpr},
      List.Forall₂ (TrExprS env Us scope) sources narrow →
      List.Forall₂ (TrExprS env Us runtime) sources full →
      List.Forall₂ (fun n f => env.IsDefEqU Us.length runtime.toCtx
        (n.lift' H.shift) f) narrow full
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hn tn, .cons hf tf =>
    .cons (H.fullTargetEq henv hn
      (hf.trExpr henv (H.context.symm henv.ordered).wf))
      (H.fullTargetEqs henv tn tf)

/-- Restrict the complete recursive index spine through the exact cached
target core.  This is the list-level equation certificate: all indices share
one non-contiguous weakening and one cached parameter/field/local context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.cachedCoreSemanticIndices
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
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowCore H.outVEnv Us
          scope F.semantic.current_context.mlctx.vlctx,
      ∃ localDomains narrowIndices,
        scope.fvars = F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse ++
            H.parameterSuffix.parameterDecls.fvars ∧
        scope.drop F.semantic.generated.localArgs.size = B.fieldScope ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
        (∀ {body target},
          TrExprS H.outVEnv Us scope body target →
          H.outVEnv.IsType Us.length scope.toCtx target →
          TrExprS H.outVEnv Us B.fieldScope
              (F.semantic.generated.current.lctx.mkForall
                F.semantic.generated.localArgs body)
              (VExpr.wrapForalls localDomains target) ∧
            H.outVEnv.IsType Us.length B.fieldScope.toCtx
              (VExpr.wrapForalls localDomains target)) ∧
        evidence.indices.length = F.telescope.indices.length ∧
        List.Forall₂ (TrExprS H.outVEnv Us scope)
          sourceIndices narrowIndices ∧
        List.Forall₂
          (fun narrow full => H.outVEnv.IsDefEqU Us.length
            F.semantic.current_context.mlctx.vlctx.toCtx
            (narrow.lift' Hscope.shift) full)
          narrowIndices evidence.indices ∧
        ChkEmbeds H.outVEnv Us.length
          F.semantic.current_context.chk.vlctx scope := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  rcases F.semanticMotiveTelescopeEvidence with ⟨binding, ⟨evidence⟩⟩
  have hrecInfo : selectedOwner < H.recInfos.size := by
    simpa [selectedOwner, H.generated.length] using F.entry_lt
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
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
  have Hindices := evidence.indices_translation
  rw [hsemantic] at Hindices
  have HindicesFinal := Lean4Lean.List.Forall₂.imp
    (fun _ _ Hindex => Hindex.mono H.constructorVEnv_le) Hindices
  rcases F.currentCachedNarrowCore B with
    ⟨scope, Hscope, hscope, hdrop, localDomains, hlocal,
      hcontext, Hreplay, hemb⟩
  have hscopeExact : scope.fvars = F.semantic.recent.fvars.reverse ++
      A.semantics.fieldsRecent.fvars.reverse ++
        H.parameterSuffix.parameterDecls.fvars := by
    rw [hscope, B.scope_fvars, A.parameterDecls_eq, List.append_assoc]
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
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨exposed₁, Hexposed₁, _⟩, _, _⟩ :=
    F.semantic.chkAgree
  rw [hsemantic] at Hexposed₁
  obtain ⟨exposed₂, Hexposed₂⟩ := hemb.trExprS H.outVEnvWF
    (Hexposed₁.mono H.constructorVEnv_le)
  obtain ⟨args₂, Hargs₂⟩ :=
    TrExprS.getAppArgsList_translations Hexposed₂
  have hsourceIndices : sourceIndices =
      F.semantic.generated.exposedType.getAppArgsList.drop
        stats.params.size :=
    Expr.getAppArgs_slice_toList _ _
  have HnarrowIndices : List.Forall₂ (TrExprS H.outVEnv Us scope)
      sourceIndices (args₂.drop stats.params.size) := by
    rw [hsourceIndices]
    exact Hargs₂.drop_both _
  let narrowIndices := args₂.drop stats.params.size
  have HindexEq := Hscope.fullTargetEqs H.outVEnvWF HnarrowIndices HindicesFinal
  exact ⟨binding, evidence, scope, Hscope, localDomains, narrowIndices,
    hscopeExact, hdrop, hlocal, hcontext, Hreplay, hlength,
    HnarrowIndices, HindexEq, hemb⟩

/-- Apply a translated function to the free variables of a lambda prefix
opened above its context.  The application is translated and typed by the
canonical variables, and its type is the remaining telescope. -/
theorem TrExprS.mkAppList_fvarPrefix {env : VEnv} {Us : List Name}
    (henv : env.WF) {Δ₀ : VLCtx} {f : Expr} {bF : VExpr}
    (hf : TrExprS env Us Δ₀ f bF) :
    ∀ (pre : VLCtx) {rest : List VExpr} {body : VExpr},
      (pre ++ Δ₀).WF env Us.length →
      (∀ e ∈ pre, ∃ fv deps d, e = (some (fv, deps), .vlam d)) →
      env.HasType Us.length Δ₀.toCtx bF
        (VExpr.wrapForalls ((VLCtx.toCtx pre).reverse ++ rest) body) →
      TrExprS env Us (pre ++ Δ₀)
          (Expr.mkAppList f ((VLCtx.fvars pre).reverse.map Expr.fvar))
          (VExpr.mkApps (bF.liftN pre.length)
            (recursorCanonicalVars pre.length)) ∧
        env.HasType Us.length (pre ++ Δ₀).toCtx
          (VExpr.mkApps (bF.liftN pre.length)
            (recursorCanonicalVars pre.length))
          (VExpr.wrapForalls rest body)
  | [], rest, body, _, _, hty => by
    simpa [Expr.mkAppList, VExpr.mkApps, VLCtx.toCtx, VLCtx.fvars] using
      And.intro hf hty
  | e :: pre, rest, body, hwf, hlams, hty => by
    obtain ⟨fv, deps, d, rfl⟩ := hlams e (by simp)
    have hlams' : ∀ e ∈ pre, ∃ fv deps d, e = (some (fv, deps), .vlam d) :=
      fun e he => hlams e (by simp [he])
    have hty' : env.HasType Us.length Δ₀.toCtx bF
        (VExpr.wrapForalls ((VLCtx.toCtx pre).reverse ++ (d :: rest)) body) := by
      simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using hty
    obtain ⟨htr, htyped⟩ :=
      TrExprS.mkAppList_fvarPrefix henv hf pre hwf.1 hlams' hty'
    let W : VLCtx.FVLift (pre ++ Δ₀)
        ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)) 0 1 0 :=
      .skip_fvar _ _ .refl
    have htrW := htr.weakFV henv.ordered W hwf
    have htyW := htyped.weakN henv.ordered W.toCtx
    have harg : TrExprS env Us ((some (fv, deps), .vlam d) :: (pre ++ Δ₀))
        (.fvar fv) (.bvar 0) := by
      apply TrExprS.fvar (A := d.liftN 1)
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift]
    have hargTy : env.HasType Us.length
        (VLCtx.toCtx ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)))
        (.bvar 0) (d.liftN 1) := by
      have hlookup : VLCtx.find?
          ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)) (.inr fv) =
          some (.bvar 0, d.liftN 1) := by
        simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
          VLocalDecl.value, VLocalDecl.type, VExpr.lift]
      exact hwf.find?_wf henv.ordered hlookup
    have hfnTy : env.HasType Us.length
        (VLCtx.toCtx ((some (fv, deps), .vlam d) :: (pre ++ Δ₀)))
        ((VExpr.mkApps (bF.liftN pre.length)
          (recursorCanonicalVars pre.length)).liftN 1)
        (.forallE (d.liftN 1) ((VExpr.wrapForalls rest body).liftN 1 1)) := by
      simpa [VExpr.wrapForalls, VExpr.liftN] using htyW
    have happ := TrExprS.app hfnTy hargTy htrW harg
    have happTy := VEnv.HasType.app hfnTy hargTy
    have hvars : VExpr.mkApps (bF.liftN (pre.length + 1))
        (recursorCanonicalVars (pre.length + 1)) =
        .app ((VExpr.mkApps (bF.liftN pre.length)
          (recursorCanonicalVars pre.length)).liftN 1) (.bvar 0) := by
      rw [recursorCanonicalVars_add pre.length 1, VExpr.mkApps_append,
        VExpr.liftN_mkApps]
      simp [recursorCanonicalVars, VExpr.mkApps, VExpr.liftN_liftN]
    refine ⟨?_, ?_⟩
    · simpa [Expr.mkAppList, List.reverse_cons, List.map_append,
        Expr.mkAppList_append, hvars] using happ
    · simpa [hvars, VExpr.instN_bvar0] using happTy

/-- Shared cached-target frame for every semantic argument of one recursive
call.  Locals and fields are closed from a single dependency-selected core;
the cached parameter suffix remains literal. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.cachedCoreSemanticCallArgumentFrame
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
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowCore H.outVEnv Us
          scope F.semantic.current_context.mlctx.vlctx,
      ∃ (fieldDomains localDomains narrowIndices : List VExpr)
          (narrowMajor narrowExposed : VExpr),
        scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
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
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.cachedCoreSemanticIndices B with
    ⟨binding, evidence, scope, Hscope, localDomains, narrowIndices,
      hscopeFVars, hdropLocal, hlocal, hscopeContext, Hreplay,
      hlength, Hindices, HindexEq, hemb⟩
  let sourceMajor := mkAppN A.rule.recursiveArgs[j]
    F.semantic.generated.localArgs
  have hmajorScope : sourceMajor.FVarsIn (· ∈ scope.fvars) := by
    dsimp only [sourceMajor]
    rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
        ⟨hjFVars, hfieldSource⟩
      rw [hfieldSource]
      have hfieldAll : A.rule.recursive_args_bound.fvars[j] ∈
          A.rule.all_args_bound.fvars :=
        A.rule.recursive_args_bound.fvars_subset_of_sublist
          A.rule.all_args_bound A.rule.recursive_args_sublist
          (List.getElem_mem hjFVars)
      have hfieldRecent : A.rule.recursive_args_bound.fvars[j] ∈
          A.semantics.fieldsRecent.fvars := by
        rw [BoundFVarArray.fvars_eq
          A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
          A.rule.all_args_bound rfl]
        exact hfieldAll
      rw [hscopeFVars]
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_reverse.mpr hfieldRecent))
    · intro arg harg
      have harg' : arg ∈
          F.semantic.generated.arguments_bound.fvars.map Expr.fvar := by
        simpa [F.semantic.generated.arguments_bound.expressions] using harg
      rcases List.mem_map.mp harg' with ⟨localFv, hlocalFv, rfl⟩
      have hlocalRecent : localFv ∈ F.semantic.recent.fvars := by
        rw [BoundFVarArray.fvars_eq
          F.semantic.recent.toFreshBoundFVarArray.toBoundFVarArray
          F.semantic.generated.arguments_bound.toBoundFVarArray rfl]
        exact hlocalFv
      rw [hscopeFVars]
      exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_reverse.mpr hlocalRecent))
  have hexposedScope : F.semantic.generated.exposedType.FVarsIn
      (· ∈ scope.fvars) := by
    apply F.semantic.exposed_scope.mono
    intro fv hfv
    rw [F.root_scope,
      A.semantics.fieldOpening.fvars_eq_bound
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
      at hfv
    rw [hscopeFVars, H.parameterSuffix.parameterDecls_fvars]
    rcases hfv with hlocalFv | hfield | hparam
    · exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_reverse.mpr hlocalFv))
    · exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_reverse.mpr hfield))
    · exact List.mem_append_right _ (List.mem_reverse.mpr hparam)
  have hsemantic : F.semantic.current_context.venv =
      R.context.venv :=
    F.semantic.recent.venv_eq.trans
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
  have HmajorFull := F.semantic.applied_field_translation
  have HexposedFull := F.semantic.exposed_translation
  rw [hsemantic] at HmajorFull HexposedFull
  have HmajorFinal := HmajorFull.mono H.constructorVEnv_le
  have HexposedFinal := HexposedFull.mono H.constructorVEnv_le
  have hmajorClosed : Closed sourceMajor 0 := by
    have h := HmajorFinal.closed
    rw [F.semantic.current_context.mlctx.noBV] at h
    exact h
  have hexposedClosed : Closed F.semantic.generated.exposedType 0 := by
    have h := HexposedFinal.closed
    rw [F.semantic.current_context.mlctx.noBV] at h
    exact h
  -- The major and its type, built from the checker contexts of the
  -- producer rather than restricted from the runtime context.
  obtain ⟨hnC, hagreeC, jC, hjC, ty₀, hdropC, hty₀, hty₀Ty, t₀,
    ⟨t₁, Ht₁, ht₁₀⟩, Ht₀Ty, hcl⟩ := F.semantic.chkAgree
  have hposFields : 0 < A.rule.allArgs.size := by
    have hlen := A.semantics.selection.fields_length
    have hne : A.semantics.fields ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    obtain ⟨cert, hcert⟩ := List.exists_mem_of_ne_nil _ hne
    have := A.semantics.selection.positions_lt cert hcert
    omega
  have henvO := H.outVEnvWF
  have hcurEnv : F.semantic.current_context.venv ≤ H.outVEnv := by
    rw [hsemantic]
    exact H.constructorVEnv_le
  have horigEnv : F.originContext.venv ≤ H.outVEnv := by
    rw [F.originRecent.venv_eq, A.semantics.context_venv, H.recursorEnv]
    exact H.constructorVEnv_le
  have hctxEnv : A.semantics.context.venv ≤ H.outVEnv := by
    rw [A.semantics.context_venv, H.recursorEnv]
    exact H.constructorVEnv_le
  have hfieldEnv : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldsRecent.venv_eq]
    exact hctxEnv
  have hchkCWF : F.semantic.current_context.chk.WF H.outVEnv Us :=
    F.semantic.current_context.check.wf.mono hcurEnv
  have hMcWF : A.semantics.context.chk.WF H.outVEnv Us :=
    A.semantics.context.check.wf.mono hctxEnv
  have hchkEq : F.originContext.chk = A.semantics.context.chk := F.originCheck
  have hjC' : jC ≤ A.semantics.context.chk.length := hchkEq ▸ hjC
  have keyDrop : ∀ (m m' : TypeChecker.MLCtx), m = m' → ∀ hj hj',
      m.dropN jC hj = m'.dropN jC hj' := by
    intro m m' h hj hj'
    subst h
    rfl
  have hbaseOrig := keyDrop _ _ hchkEq hjC hjC'
  rw [hbaseOrig] at hdropC hty₀ hty₀Ty hcl
  have halignFS : VLCtx.IsDefEq H.outVEnv Us.length B.fieldScope
      A.semantics.context.chk.vlctx :=
    (B.checkAlign hposFields).mono hfieldEnv
  have hembMc : ChkEmbeds H.outVEnv Us.length
      A.semantics.context.chk.vlctx B.fieldScope :=
    ⟨A.semantics.context.chk.vlctx, .refl, .refl,
      halignFS.symm henvO.ordered⟩
  have hembBase : ChkEmbeds H.outVEnv Us.length
      (A.semantics.context.chk.dropN jC hjC').vlctx B.fieldScope :=
    ChkEmbeds.of_fvLift
      (A.semantics.context.check.onlyLams.dropN_fvlift jC hjC').toFVLift'
      hembMc
  -- the exposed type in the checker context, and in the call scope
  have Ht₁' := Ht₁.mono hcurEnv
  have Ht₁Ty : H.outVEnv.IsType Us.length
      F.semantic.current_context.chk.vlctx.toCtx t₁ :=
    (Ht₀Ty.mono hcurEnv).defeqU_l henvO hchkCWF.tr.wf.toCtx
      (ht₁₀.mono hcurEnv).symm
  obtain ⟨narrowExposed, Hexposed⟩ := hemb.trExprS henvO Ht₁'
  have HexposedTy : H.outVEnv.IsType Us.length scope.toCtx narrowExposed :=
    hemb.isType henvO Ht₁' Hexposed Ht₁Ty
  -- the closed argument telescope of the field type
  have hxs : F.semantic.generated.localArgs.toList.reverse =
      (F.semantic.current_context.chk.fvarRevList
        F.semantic.generated.localArgs.size hnC).map Expr.fvar := by
    rw [← hagreeC.fvarRevList_eq F.semantic.recent.size_le hnC]
    exact F.semantic.recent.reverse_eq
  have hexpClosed : Closed F.semantic.generated.exposedType :=
    hexposedClosed
  have hsrcChk := F.semantic.current_context.check.wf.mkForall_eq
    F.semantic.generated.localArgs.size hnC hxs hexpClosed
  have hlocalArr : F.semantic.generated.localArgs =
      (((F.semantic.current_context.chk.fvarRevList
        F.semantic.generated.localArgs.size hnC).reverse).map
          Expr.fvar).toArray := by
    apply Array.ext'
    have h := congrArg List.reverse hxs
    simpa [List.map_reverse] using h
  have hmemChk : ∀ fv ∈ (F.semantic.current_context.chk.fvarRevList
      F.semantic.generated.localArgs.size hnC).reverse,
      ∃ d, F.semantic.generated.current.checkLCtx.find? fv = some d := by
    intro fv hfv
    rw [← F.semantic.current_context.check.lctx_eq]
    exact F.semantic.current_context.check.wf.tr.find?_eq_some.2
      ((TypeChecker.MLCtx.fvarRevList_prefix _).subset (List.mem_reverse.mp hfv))
  have hsub := F.semantic.current_context.checkSub.mkForall_eq hmemChk
    F.semantic.generated.exposedType
  rw [← hlocalArr] at hsub
  have hlctxChk : F.semantic.generated.current.checkLCtx =
      F.semantic.current_context.chk.lctx :=
    F.semantic.current_context.check.lctx_eq.symm
  rw [hlctxChk, hsrcChk] at hsub
  have HWbBoth := hchkCWF.mkForall_trS henvO Ht₁' Ht₁Ty
    F.semantic.generated.localArgs.size hnC
  rw [← hsub, hdropC] at HWbBoth
  obtain ⟨u₀, hu₀⟩ := Ht₀Ty.mono hcurEnv
  have ht₀₁ := (ht₁₀.mono hcurEnv).symm.of_l henvO hchkCWF.tr.wf.toCtx hu₀
  obtain ⟨_, hcongr⟩ := hchkCWF.mkForall'_congr ht₀₁
    F.semantic.generated.localArgs.size hnC
  rw [hdropC] at hcongr
  have hclW : H.outVEnv.IsDefEqU Us.length
      (A.semantics.context.chk.dropN jC hjC').vlctx.toCtx ty₀
      (F.semantic.current_context.chk.mkForall'
        F.semantic.generated.localArgs.size hnC t₁) :=
    (hcl.mono hcurEnv).trans henvO
      ((hMcWF.dropN jC hjC').tr.wf.toCtx) ⟨_, hcongr⟩
  -- the recursive field in the rule's checker context
  rcases A.rule.recursive_args_bound.getElem_eq_fvar j hj with
    ⟨hjFVars, hfieldSource⟩
  let fvF := A.rule.recursive_args_bound.fvars[j]
  have hfieldAll : fvF ∈ A.rule.all_args_bound.fvars :=
    A.rule.recursive_args_bound.fvars_subset_of_sublist
      A.rule.all_args_bound A.rule.recursive_args_sublist
      (List.getElem_mem hjFVars)
  have hfieldRecent : fvF ∈ A.semantics.fieldsRecent.fvars := by
    rw [BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl]
    exact hfieldAll
  have hmemMc : fvF ∈ A.semantics.context.chk.vlctx.fvars := by
    rw [← halignFS.fvars, B.scope_fvars]
    exact List.mem_append_left _ (List.mem_reverse.mpr hfieldRecent)
  obtain ⟨d, hd⟩ := hMcWF.tr.find?_eq_some.2 hmemMc
  have hdToList := hd
  rw [hMcWF.tr.1.find?_eq_find?_toList] at hdToList
  have hdmem : d ∈ A.semantics.context.chk.lctx.toList :=
    List.mem_of_find?_eq_some hdToList
  have hdfv : d.fvarId = fvF := by
    have h := List.find?_some hdToList
    exact (beq_iff_eq.mp h).symm
  obtain ⟨e, Aty, hfind, _, _, _, HAty⟩ := hMcWF.tr.find?_of_mem henvO hdmem
  rw [hdfv] at hfind
  have Hfv : TrExprS H.outVEnv Us A.semantics.context.chk.vlctx
      (.fvar fvF) e := TrExprS.fvar hfind
  have HfvTy : H.outVEnv.HasType Us.length
      A.semantics.context.chk.vlctx.toCtx e Aty :=
    hMcWF.tr.wf.find?_wf henvO.ordered hfind
  obtain ⟨bF, HbF⟩ := hembMc.trExprS henvO Hfv
  obtain ⟨Tf, HTf⟩ := hembMc.trExprS henvO HAty
  have HbFTy := hembMc.hasType henvO Hfv HbF HAty HTf HfvTy
  -- the field's declared type, read from both contexts
  have hdtype : d.type =
      (F.originRoot.lctx.get! (A.rule.recursiveArgs[j]).fvarId!).type := by
    have hd' : A.rule.root.checkLCtx.find? fvF = some d := by
      rw [← A.semantics.context.check.lctx_eq]
      exact hd
    obtain ⟨d', hd'main, hdeq⟩ := A.semantics.context.checkSub fvF d hd'
    have hfvRoot : fvF ∈ A.rule.root.lctx.fvars := by
      rw [← A.semantics.context.lctx_eq, A.semantics.context.mlctx_wf.tr.fvars_eq]
      have := A.semantics.fieldsRecent.toBoundFVarArray.members fvF hfieldRecent
      rw [← A.semantics.context.lctx_eq] at this
      rw [A.semantics.context.mlctx_wf.tr.fvars_eq] at this
      exact this
    have horigin : F.originRoot.lctx.find? fvF = some d' :=
      (F.originRecent.contextLE.declarations fvF hfvRoot).trans hd'main
    have e1 : ∀ x : LocalDecl, (x.setIndex 0).type = x.type := by
      intro x; cases x <;> rfl
    have hget : F.originRoot.lctx.get! fvF = d' := by
      simp only [LocalContext.get!, horigin]
    have hfid : (A.rule.recursiveArgs[j]).fvarId! = fvF := by
      rw [hfieldSource]; rfl
    rw [hfid, hget, ← e1 d', hdeq, e1]
  rw [hdtype] at HAty HTf
  -- the field type is the closed telescope, in the field scope
  have HWfs := Hreplay Hexposed HexposedTy
  have hTfW := hembBase.isDefEqU henvO (hty₀.mono horigEnv) HWbBoth.1 HTf
    HWfs.1 hclW
  have HbFW := HbFTy.defeqU_r henvO
    (halignFS.wf.toCtx) hTfW
  -- apply it to the call-local arguments
  have hscopeSplit : scope.take F.semantic.generated.localArgs.size ++
      B.fieldScope = scope := by
    rw [← hdropLocal]
    exact List.take_append_drop _ _
  have hpreCtx : (VLCtx.toCtx (scope.take
      F.semantic.generated.localArgs.size)).reverse = localDomains := by
    have hparts := congrArg VLCtx.toCtx hscopeSplit
    rw [VLCtx.toCtx_append, hscopeContext] at hparts
    have h := List.append_cancel_right hparts
    rw [h, List.reverse_reverse]
  have hlams : ∀ en ∈ scope.take F.semantic.generated.localArgs.size,
      ∃ fv deps dom, en = (some (fv, deps), .vlam dom) := by
    intro en hen
    have hen' := List.mem_of_mem_take hen
    have gen : ∀ {l₁ : List FVarId} {l₂ : VLCtx},
        List.Forall₂ (fun fv entry => ∃ deps type,
          entry = (some (fv, deps), .vlam type)) l₁ l₂ →
        ∀ en ∈ l₂, ∃ fv deps dom, en = (some (fv, deps), .vlam dom) := by
      intro l₁ l₂ h
      induction h with
      | nil => simp
      | @cons a en' _ _ hhd _ ih =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · obtain ⟨deps, dom, rfl⟩ := hhd
          exact ⟨a, deps, dom, rfl⟩
        · exact ih x hx
    exact gen Hscope.declarations en hen'
  have Happ := TrExprS.mkAppList_fvarPrefix henvO HbF
    (scope.take F.semantic.generated.localArgs.size) (rest := [])
    (body := narrowExposed) (by rw [hscopeSplit]; exact Hscope.wf) hlams
    (by simpa [hpreCtx] using HbFW)
  rw [hscopeSplit] at Happ
  have hlocalFVars : (VLCtx.fvars (scope.take
      F.semantic.generated.localArgs.size)).reverse =
      F.semantic.recent.fvars := by
    rw [Hscope.fvars_take, hscopeFVars]
    have hlen : F.semantic.recent.fvars.length =
        F.semantic.generated.localArgs.size := by
      rw [F.semantic.recent.toBoundFVarArray.length_fvars]
    rw [List.append_assoc, List.take_left' (by simp [hlen]),
      List.reverse_reverse]
  rw [hlocalFVars] at Happ
  have hsourceMajor : sourceMajor = Expr.mkAppList (.fvar fvF)
      (F.semantic.recent.fvars.map Expr.fvar) := by
    dsimp only [sourceMajor]
    have h1 : mkAppN A.rule.recursiveArgs[j] F.semantic.generated.localArgs =
        mkAppN (.fvar fvF) F.semantic.generated.localArgs :=
      congrArg (fun x => mkAppN x F.semantic.generated.localArgs) hfieldSource
    have hl : F.semantic.generated.localArgs.toList =
        F.semantic.recent.fvars.map Expr.fvar := by
      have key : ∀ (xs : Array Expr) (fvs : List FVarId),
          xs = (fvs.map Expr.fvar).toArray → xs.toList = fvs.map Expr.fvar := by
        intro xs fvs h; subst h; simp
      exact key _ _ F.semantic.recent.expressions
    rw [h1, Expr.mkAppN_eq_mkAppList, hl]
  have hnScope : F.semantic.generated.localArgs.size ≤ scope.length := by
    have h := congrArg List.length hscopeContext
    rw [Hscope.toCtx_length] at h
    simp [hlocal] at h
    omega
  have hmin : min F.semantic.generated.localArgs.size scope.length =
      F.semantic.generated.localArgs.size := Nat.min_eq_left hnScope
  let narrowMajor := VExpr.mkApps
    (bF.liftN F.semantic.generated.localArgs.size)
    (recursorCanonicalVars F.semantic.generated.localArgs.size)
  have Hmajor : TrExprS H.outVEnv Us scope sourceMajor narrowMajor := by
    rw [hsourceMajor]
    simpa [List.length_take, hmin] using Happ.1
  have Htyping : H.outVEnv.HasType Us.length scope.toCtx narrowMajor
      narrowExposed := by
    simpa [VExpr.wrapForalls, List.length_take, hmin] using Happ.2
  have HmajorEq : H.outVEnv.IsDefEqU Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.appliedFieldTarget (narrowMajor.lift' Hscope.shift) :=
    (Hscope.fullTargetEq henvO Hmajor
      (HmajorFinal.trExpr henvO (Hscope.context.symm henvO.ordered).wf)).symm
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hzero : TrExprS H.outVEnv Us scope
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have HzeroType : H.outVEnv.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  rcases Hreplay Hzero HzeroType with
    ⟨HlocalTemplate, HlocalTemplateType⟩
  let frontCount := F.semantic.generated.localArgs.size +
    A.rule.allArgs.size
  have hdropFront : scope.drop frontCount = parameterDecls := by
    rw [show frontCount = F.semantic.generated.localArgs.size +
        B.fieldDomains.length by simp [frontCount, B.fieldDomains_length],
      ← List.drop_drop, hdropLocal]
    change B.fieldScope.drop B.fieldDomains.length = parameterDecls
    rw [← B.front, B.scope_base, A.parameterDecls_eq]
  have hscopeParts : scope.take frontCount ++ parameterDecls = scope := by
    rw [← hdropFront]
    exact List.take_append_drop frontCount scope
  have hfrontFVars : (scope.fvars.take frontCount).reverse =
      A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars := by
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
    have hparts := congrArg VLCtx.fvars hscopeParts
    rw [VLCtx.fvars_append, hscopeFVars] at hparts
    have hprefix : VLCtx.fvars (scope.take frontCount) =
        F.semantic.recent.fvars.reverse ++
          A.semantics.fieldsRecent.fvars.reverse :=
      List.append_cancel_right hparts
    rw [← Hscope.fvars_take, hprefix, List.reverse_append, List.reverse_reverse,
      List.reverse_reverse, hlocalFVars, hfieldFVars]
  have hfrontDomains :
      (VLCtx.toCtx (scope.take frontCount)).reverse =
        B.fieldDomains ++ localDomains := by
    have hparts := congrArg VLCtx.toCtx hscopeParts
    rw [VLCtx.toCtx_append, hscopeContext] at hparts
    have hparts' : VLCtx.toCtx (scope.take frontCount) ++
        parameterDecls.toCtx =
          localDomains.reverse ++ B.fieldDomains.reverse ++
            parameterDecls.toCtx := by
      simpa [B.fieldScope_eq, parameterDecls, A.parameterDecls_eq,
        abstractForallContext_toCtx, List.append_assoc] using hparts
    have hprefix : VLCtx.toCtx (scope.take frontCount) =
        localDomains.reverse ++ B.fieldDomains.reverse := by
      exact List.append_cancel_right hparts'
    rw [hprefix, List.reverse_append, List.reverse_reverse,
      List.reverse_reverse]
  have closeSource : ∀ {source target},
      TrExprS H.outVEnv Us scope source target →
      TrExprS H.outVEnv Us
        (abstractForallContext (B.fieldDomains ++ localDomains)
          parameterDecls)
        (source.abstractList
          (A.rule.all_args_bound.fvars ++
            F.semantic.generated.arguments_bound.fvars)) target := by
    intro source target Hsource
    have Hclosed := Hscope.abstractPrefix H.outVEnvWF frontCount
      hdropFront Hsource
    rw [hfrontFVars] at Hclosed
    rw [hfrontDomains] at Hclosed
    exact Hclosed
  have closeSources : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂ (TrExprS H.outVEnv Us scope) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (B.fieldDomains ++ localDomains)
            parameterDecls))
        (sources.map fun source => source.abstractList
          (A.rule.all_args_bound.fvars ++
            F.semantic.generated.arguments_bound.fvars)) targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hhead _ ih => exact .cons (closeSource Hhead) ih
  have HindicesClosed := closeSources Hindices
  have HmajorClosed := closeSource Hmajor
  have HexposedClosed := closeSource Hexposed
  have hsourceShape : ∀ source : Expr,
      source.abstractList
          (A.rule.all_args_bound.fvars ++
            F.semantic.generated.arguments_bound.fvars) =
        (source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size := by
    intro source
    have hnodup : (A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars).Nodup := by
      rw [← hfrontFVars]
      exact List.nodup_reverse.mpr <|
        (Hscope.scopeWF H.outVEnvWF).fvars_nodup.sublist
          (List.take_sublist frontCount scope.fvars)
    have h := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.all_args_bound.fvars)
      (inner := F.semantic.generated.arguments_bound.fvars) (k := 0)
      hnodup
    simpa [F.semantic.generated.arguments_bound.length_fvars] using h.symm
  have HindicesClosed' := HindicesClosed
  simp only [List.map_map, Function.comp_def] at HindicesClosed'
  have hsourceFunction : (fun source : Expr => source.abstractList
      (A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars)) =
      (fun source : Expr => (source.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
          F.semantic.generated.localArgs.size) := by
    funext source
    exact hsourceShape source
  rw [hsourceFunction] at HindicesClosed'
  rw [hsourceShape] at HmajorClosed HexposedClosed
  have hlocalAbstract :
      F.semantic.generated.localArgs.map (fun arg => arg.abstractList
        F.semantic.generated.arguments_bound.fvars) =
      (List.ofFn (fun index :
          Fin F.semantic.generated.arguments_bound.fvars.length =>
        Expr.bvar
          (F.semantic.generated.arguments_bound.fvars.length - 1 - index)
        )).toArray := by
    calc
      _ = ((F.semantic.generated.arguments_bound.fvars.map Expr.fvar).toArray.map
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
    have hfieldClosed : A.rule.recursiveArgs[j].looseBVarRange' = 0 := by
      have hclosed := F.semantic.field_translation.closed
      rw [F.originContext.mlctx.noBV] at hclosed
      exact hclosed.looseBVarRange_zero
    calc
      sourceMajor.abstractList
          F.semantic.generated.arguments_bound.fvars =
        mkAppN
          (A.rule.recursiveArgs[j].abstractList
            F.semantic.generated.arguments_bound.fvars)
          (List.ofFn (fun index :
            Fin F.semantic.generated.arguments_bound.fvars.length =>
              Expr.bvar
                (F.semantic.generated.arguments_bound.fvars.length - 1 -
                  index))).toArray := by
        dsimp only [sourceMajor]
        rw [Expr.abstractList_mkAppN, hlocalAbstract]
      _ = F.semantic.generated.abstractedMajor := by
        rw [F.semantic.generated.abstractedMajor_eq_of_closed hfieldClosed,
          Expr.abstractN_eq_abstractList F.semantic.generated.arguments_bound.nodup _ 0
            (Nat.le_of_eq hfieldClosed)]
  rw [hmajorLocal] at HmajorClosed
  have HclosedCtx : OnCtx
      (abstractForallContext (B.fieldDomains ++ localDomains)
        parameterDecls).toCtx (H.outVEnv.IsType Us.length) := by
    have Hwf := (Hscope.scopeWF H.outVEnvWF).toCtx
    rw [hscopeContext, B.fieldScope_eq] at Hwf
    simpa [parameterDecls, A.parameterDecls_eq,
      List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using Hwf
  have HclosedTyping : H.outVEnv.HasType Us.length
      (abstractForallContext (B.fieldDomains ++ localDomains)
        parameterDecls).toCtx narrowMajor narrowExposed := by
    have hctx :
        (abstractForallContext (B.fieldDomains ++ localDomains)
          parameterDecls).toCtx = scope.toCtx := by
      rw [hscopeContext, B.fieldScope_eq]
      simp [parameterDecls, A.parameterDecls_eq,
        List.reverse_append, List.append_assoc,
        VLCtx.toCtx]
    rw [hctx]
    exact Htyping
  exact ⟨binding, evidence, scope, Hscope, B.fieldDomains, localDomains,
    narrowIndices, narrowMajor, narrowExposed, hscopeContext,
    B.fieldDomains_length, rfl, hlocal, HlocalTemplate,
    HlocalTemplateType, HclosedCtx, hlength,
    by simpa using HindicesClosed',
    by simpa [BoundGeneratedRecursiveCall.outerAbstractedMajor] using
      HmajorClosed,
    HexposedClosed, HclosedTyping, HindexEq, HmajorEq⟩

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
        A.semantics.parameterSuffix.parameterDecls).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
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
    exact H.constructorVEnv_le
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
        (B.forwardDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
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
    exact H.constructorVEnv_le
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
            (B.forwardDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
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
            (B.forwardDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
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

theorem VLCtx.FVLift.of_append_lams : ∀ (X : VLCtx) {Q : VLCtx},
    (∀ e ∈ X, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      VLCtx.FVLift Q (X ++ Q) 0 X.length 0
  | [], _, _ => .refl
  | e :: X, Q, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    have W := VLCtx.FVLift.of_append_lams X (Q := Q)
      (fun x hx => h x (by simp [hx]))
    exact .skip_fvar k (.vlam d) W

/-- The parameter declarations sit, up to conversion, at the bottom of any
generated scope that starts with the parameters; the generated binders above
them form a contiguous free-variable weakening. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalPrefixParameterBase
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    {outerScope : VLCtx}
    (Houter : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      outerScope H.recursorWF.mlctx.vlctx)
    (restBinders : List FVarId) (Trest : List VExpr)
    (houterFVars : outerScope.fvars = (H.params.fvars ++ restBinders).reverse)
    (HouterPrefix : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      outerScope.toCtx (T.params ++ Trest).reverse) :
    VLCtx.IsDefEq H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls
        (outerScope.drop Trest.length) ∧
      VLCtx.FVLift (outerScope.drop Trest.length)
        outerScope 0 Trest.length 0 := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let P := H.parameterSuffix.parameterDecls
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hPlams := VLCtx.lams_of_cached H.parameterSuffix.cached
  have hOlams := VLCtx.lams_of_declarations Houter.declarations
  have hPfvars : P.fvars = H.params.fvars.reverse := by
    rw [H.parameterSuffix.parameterDecls_fvars, H.params.exprArrayFVarIds]
  have hPlen : P.length = H.params.fvars.length := by
    rw [← VLCtx.fvars_length_of_lams hPlams, hPfvars, List.length_reverse]
  have hOlen : outerScope.length = (H.params.fvars ++ restBinders).length := by
    rw [← VLCtx.fvars_length_of_lams hOlams, houterFVars, List.length_reverse]
  have Hparams := H.finalRecursorParameterContextFor howner T
  rw [← H.parameterDecls] at Hparams
  have hTparams : T.params.length = H.params.fvars.length := by
    have := Hparams.length_eq
    rw [List.length_reverse, VLCtx.toCtx_length_of_lams hPlams] at this
    rw [this, hPlen]
  have hTlen := HouterPrefix.length_eq
  rw [VLCtx.toCtx_length_of_lams hOlams] at hTlen
  simp only [List.length_reverse, List.length_append] at hTlen
  let m := Trest.length
  have hm : m = restBinders.length := by
    simp only [m, List.length_append] at hOlen ⊢
    omega
  let Q : VLCtx := outerScope.drop m
  let X : VLCtx := outerScope.take m
  have hXQ : X ++ Q = outerScope := List.take_append_drop m outerScope
  have hXlams : ∀ e ∈ X, ∃ k d, e = (some k, VLocalDecl.vlam d) :=
    fun e he => hOlams e (List.mem_of_mem_take he)
  have hQlams : ∀ e ∈ Q, ∃ k d, e = (some k, VLocalDecl.vlam d) :=
    fun e he => hOlams e (List.mem_of_mem_drop he)
  have hXlen : X.length = m := by
    simp only [X, List.length_take]
    simp only [m, List.length_append] at hOlen ⊢
    omega
  have hQfvars : Q.fvars = P.fvars := by
    rw [VLCtx.fvars_drop_of_lams m hOlams, houterFVars, hPfvars, hm,
      List.reverse_append]
    exact List.drop_left' (by simp)
  have HQT : VEnv.IsDefEqCtx H.outVEnv Us.length [] Q.toCtx
      T.params.reverse := by
    have Hdrop := VEnv.IsDefEqCtx.dropHeads HouterPrefix m
    have hl : outerScope.toCtx.drop m = Q.toCtx := by
      rw [← hXQ, VLCtx.toCtx_append]
      apply List.drop_left'
      rw [VLCtx.toCtx_length_of_lams hXlams, hXlen]
    have hr : (T.params ++ Trest).reverse.drop m =
        T.params.reverse := by
      rw [List.reverse_append]
      apply List.drop_left'
      simp [m]
    rw [hl, hr] at Hdrop
    exact Hdrop
  have HQPctx := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF HQT Hparams
  have hnodup := H.recursorWF.mlctx_wf.fvars_nodup
  have hkeyRuntime : ∀ x ∈ Q.map Prod.fst,
      x ∈ H.recursorWF.mlctx.vlctx.map Prod.fst := by
    intro x hx
    have h1 : x ∈ outerScope.map Prod.fst :=
      (List.map_subset _ (List.drop_subset m outerScope)) hx
    have h2 := (VLCtx.FVLift'.keys_sublist Houter.lift).subset h1
    rwa [VLCtx.IsDefEq.keys_eq Houter.context] at h2
  have hkeyP : ∀ x ∈ P.map Prod.fst,
      x ∈ H.recursorWF.mlctx.vlctx.map Prod.fst := by
    intro x hx
    rw [H.parameterSuffix.context, List.map_append]
    exact List.mem_append_right _ hx
  have hsome : ∀ (L : VLCtx),
      (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      ∀ x ∈ L.map Prod.fst, x.isSome := by
    intro L hL x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, d, rfl⟩ := hL e he
    rfl
  have hkeys : Q.map Prod.fst = P.map Prod.fst :=
    VLCtx.keys_eq_of_fvars hnodup hkeyRuntime hkeyP (hsome Q hQlams)
      (hsome P hPlams) (by
        rw [VLCtx.keys_fvars_of_lams hQlams, VLCtx.keys_fvars_of_lams hPlams,
          hQfvars])
  have hQwf : VLCtx.WF H.outVEnv Us.length Q :=
    VLCtx.WF.append_right (A := X) (by rw [hXQ]; exact Houter.wf)
  have HQP : VLCtx.IsDefEq H.outVEnv Us.length Q P :=
    VLCtx.IsDefEq.ofKeysCtx hkeys
      (fun e he => let ⟨_, d, h⟩ := hQlams e he; ⟨_, d, h⟩)
      (fun e he => let ⟨_, d, h⟩ := hPlams e he; ⟨_, d, h⟩) hQwf HQPctx
  refine ⟨HQP.symm H.outVEnvWF.ordered, ?_⟩
  have W := VLCtx.FVLift.of_append_lams X (Q := Q) hXlams
  rw [hXQ, hXlen] at W
  exact W

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterParameterBase
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
    {outerScope : VLCtx}
    (Houter : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      outerScope H.recursorWF.mlctx.vlctx)
    (houterFVars : outerScope.fvars =
      (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars).reverse)
    (HouterPrefix : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      outerScope.toCtx (T.params ++ T.motives ++ T.minors).reverse) :
    VLCtx.IsDefEq H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls
        (outerScope.drop (T.motives ++ T.minors).length) ∧
      VLCtx.FVLift (outerScope.drop (T.motives ++ T.minors).length)
        outerScope 0 (T.motives ++ T.minors).length 0 :=
  A.finalPrefixParameterBase T Houter
    (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)
    (T.motives ++ T.minors) (by simpa [List.append_assoc] using houterFVars)
    (by simpa [List.append_assoc] using HouterPrefix)

/-- The installed selected minor's field domains agree, over the generated
prefix preceding that minor, with the parameter-scope translation of the
constructor fields.  The comparison passes through the checker context in
which the fields were opened: the minor's source binders are literally the
checker's field declarations, and the checker's closure of the constructor
tail agrees with the parameter-scope translation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalInstalledCheckedFieldLink
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size)
    (checkedDomains : List VExpr) (checkedResidual : VExpr)
    (hchecked : checkedDomains.length = A.rule.allArgs.size)
    (Hchecked : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual))
    (fieldDomains hypothesisDomains : List VExpr) (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hminorType :
      T.minors[recursorMinorOffset indTypes owner + i]! = VExpr.wrapForalls
        (fieldDomains ++ hypothesisDomains) targetResidual) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let base := T.params ++ T.motives ++ T.minors.take minorIdx
    VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix (T.motives ++ T.minors.take minorIdx).length
          checkedDomains.reverse ++ base.reverse)
      (fieldDomains.reverse ++ base.reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let n := A.rule.allArgs.size
  let Trest := T.motives ++ T.minors.take minorIdx
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  rcases A.finalSelectedMinorExactClosedTelescope hpositive with
    ⟨T₁, S, HS, scope, Hscope, narrowTarget, _fullTarget, _hfullTargetEq,
      hSfields, _hShyps, hparameterTail, hscope, _hscopeShift, _Hfull,
      _HfullEq, _hscopeSource, Hprefix₁, HabstractTyped, _Hclosed,
      Hinstalled₁⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparamsT, hmotivesT, hminorsT, _, _, _⟩
  have Hprefix : VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
      base.reverse := by
    simpa only [hparamsT, hmotivesT, hminorsT] using Hprefix₁
  have Hinstalled : Expr.ForallTelescopeTypeTranslation H.outVEnv Us
      (abstractForallContext base [])
      (S.origin.abstractList sourceBinders)
      (A.rule.allArgs.size + A.rule.recursiveArgs.size)
      T.minors[minorIdx]! := by
    simpa only [hparamsT, hmotivesT, hminorsT] using Hinstalled₁
  -- Narrow replay against the installed minor, over the selected prefix.
  rcases HabstractTyped.toWrapForalls with
    ⟨narrowDomains, _, narrowResidual, hnarrowLength, _, hnarrowTarget,
      _, _⟩
  rcases Hinstalled.toWrapForalls with
    ⟨installedDomains, _, installedResidual, hinstalledLength, _,
      hinstalledTarget, _, _⟩
  have hinstalledSplit : installedDomains.take n = fieldDomains := by
    have hwhole := hinstalledTarget.symm.trans hminorType
    have hsplit := List.take_append_drop n installedDomains
    rw [← hsplit, VExpr.wrapForalls_append] at hwhole
    exact VExpr.wrapForalls_prefix_domains_eq (by simp [n, hinstalledLength])
      hfields (by simpa [VExpr.wrapForalls_append] using hwhole)
  have HbaseSel : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (scope.toCtx.reverse).reverse base.reverse := by
    simpa using Hprefix
  have HnarrowInstalled :=
    Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
      H.outVEnvWF HbaseSel HabstractTyped Hinstalled
      narrowDomains installedDomains narrowResidual installedResidual
      hnarrowTarget hinstalledTarget hnarrowLength hinstalledLength
      n (by omega) (by omega) (by
        intro position hposition _hiNarrow _hiInstalled
          domainNarrow domainInstalled HbinderNarrow HbinderInstalled
        exact HbinderNarrow.unique HbinderInstalled)
  rw [hinstalledSplit, List.reverse_reverse] at HnarrowInstalled
  -- Environments and the minor's checker context.
  have hrootEnv : HS.semantic.rootWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.fieldsRecent.contextExtension.venv_eq,
      ← HS.semantic.hypothesesRecent.contextExtension.venv_eq,
      ← HS.semantic.extension.venv_eq, H.recursorEnv]
    exact H.constructorVEnv_le
  have hterminalEnv : HS.semantic.terminalWF.venv ≤ H.outVEnv := by
    rw [HS.semantic.fieldsRecent.venv_eq]
    exact hrootEnv
  obtain ⟨M, hMwf, _hchkM, hnM, hagM, hdropM, T₀, hT₀, t₀', _ht₀', hroot⟩ :=
    HS.semantic.fieldCheck
  rw [HS.parameterDecls_eq] at hdropM hT₀ hroot
  rw [hparameterTail] at hT₀
  have hSn : S.fields.size = n := hSfields
  -- The minor's source is the checker's field closure.
  have hZ := HS.semantic.hypothesesRecent.mkForallExact
    HS.semantic.motiveTranslation HS.semantic.motiveType
  have hfieldsMono :=
    HS.semantic.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
      HS.semantic.hypothesesRecent.contextLE
      (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp)
  have hZclosed : Closed
      (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp) := by
    simpa [TypeChecker.MLCtx.noBV] using hZ.1.closed
  have hterminalMk :
      HS.semantic.traversal.terminalContext.lctx.mkForall S.fields
          (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp) =
        HS.semantic.terminalWF.mlctx.mkForall S.fields.size
          HS.semantic.fieldsRecent.size_le
          (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp) := by
    rw [← HS.semantic.terminalWF.lctx_eq]
    exact HS.semantic.terminalWF.mlctx_wf.mkForall_eq _ _
      HS.semantic.fieldsRecent.reverse_eq hZclosed
  have hsourceM : S.sourceType = M.mkForall S.fields.size hnM
      (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp) := by
    rw [S.sourceType_eq, ← S.sourceContext_eq, hfieldsMono, hterminalMk]
    exact hagM.mkForall_eq _ _ _
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hc0 : checkedDomains = [] :=
      List.eq_nil_of_length_eq_zero (hchecked.trans hn0)
    have hf0 : fieldDomains = [] :=
      List.eq_nil_of_length_eq_zero (hfields.trans hn0)
    subst hc0 hf0
    have Hr := VEnv.IsDefEqCtx.refl (Hprefix.symm H.outVEnvWF.ordered).isType
    simp only [List.reverse_nil, liftContextPrefix, liftContextPrefixAt,
      List.nil_append]
    exact Hr
  have horigin : S.origin = M.mkForall S.fields.size hnM
      (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp) := by
    obtain ⟨d, Hd⟩ := hagM.binderAt_indep hnM 0 (by omega)
    have Hb := Hd (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp)
    rw [← hsourceM] at Hb
    rw [← S.consumed_eq, Hb.consumeTypeAnnotationsVerified_eq_self, hsourceM]
  -- The checker closure of the fields over a dummy body.
  have HMsort₀ := hMwf.mkForall_trS HS.semantic.terminalWF.checking.tr.wf
    (e := .sort .zero) (e' := .sort .zero) (.sort (by simp [VLevel.ofLevel]))
    ⟨_, VEnv.HasType.sort (by trivial)⟩ S.fields.size hnM
  rw [hdropM] at HMsort₀
  have HMsortTr := HMsort₀.1.mono hterminalEnv
  have HMsortType := HMsort₀.2.mono hterminalEnv
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at HMsortTr HMsortType
  let Mdoms := MLCtxForallDomains M S.fields.size hnM
  have hMdomsLen : Mdoms.length = n := (hagM.forallDomains_length hnM).trans hSn
  -- The parameter base of the selected scope.
  obtain ⟨HPQ, W⟩ := A.finalPrefixParameterBase T Hscope
    (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx)
    Trest (by simpa [sourceBinders, List.append_assoc] using hscope)
    (by simpa [Trest, base, List.append_assoc] using Hprefix)
  let m' := Trest.length
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
  have HPwf : VLCtx.WF H.outVEnv Us.length H.parameterSuffix.parameterDecls :=
    H.parameterSuffix.parameterWF.mono hrecBase
  have HscopeWF : VLCtx.WF H.outVEnv Us.length scope := Hscope.wf
  obtain ⟨Y₀, HY₀, HY₀eq⟩ := HMsortTr.defeqDFC' H.outVEnvWF HPQ
  have HQwf := (HPQ.symm H.outVEnvWF.ordered).wf
  have HY := HY₀.weakFV H.outVEnvWF.ordered W HscopeWF
  have HY₀type : H.outVEnv.IsType Us.length
      (VLCtx.toCtx (scope.drop Trest.length)) Y₀ := by
    rcases HMsortType with ⟨u, hu⟩
    have hQ : H.outVEnv.IsType Us.length (VLCtx.toCtx (scope.drop Trest.length))
        (VExpr.wrapForalls Mdoms (.sort .zero)) :=
      ⟨u, hu.defeqDFC H.outVEnvWF.ordered HPQ.defeqCtx⟩
    exact hQ.defeqU_l H.outVEnvWF HQwf.toCtx HY₀eq.symm
  rcases HY₀eq with ⟨_, HY₀eq'⟩
  have HYeq : H.outVEnv.IsDefEqU Us.length scope.toCtx (Y₀.liftN m' 0)
      ((VExpr.wrapForalls Mdoms (.sort .zero)).liftN m' 0) :=
    ⟨_, HY₀eq'.weakN H.outVEnvWF.ordered W.toCtx⟩
  have HYtype : H.outVEnv.IsType Us.length scope.toCtx (Y₀.liftN m' 0) := by
    rcases HY₀type with ⟨u, hu⟩
    have h := hu.weakN H.outVEnvWF.ordered W.toCtx
    exact ⟨u, h⟩
  have HYabs := Hscope.abstractAll H.outVEnvWF HY
  rw [hscope, List.reverse_reverse] at HYabs
  obtain ⟨rM, HMtel⟩ := hagM.forallTelescope hnM (W := .sort .zero) (k := 0)
    (.nil _)
  have HMtel' := HMtel.abstractList sourceBinders
  have HYtypeAbs : H.outVEnv.IsType Us.length
      (abstractForallContext scope.toCtx.reverse []).toCtx (Y₀.liftN m' 0) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HYtype
  have HMabsTyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    HMtel' HYabs HYtypeAbs
  rcases HMabsTyped.toWrapForalls with
    ⟨Ydoms, _, rY, hYlen, _, hYtarget, _, _⟩
  have HrefSel : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (scope.toCtx.reverse).reverse (scope.toCtx.reverse).reverse := by
    simpa using VEnv.IsDefEqCtx.refl HscopeWF.toCtx
  have HNY :=
    Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
      H.outVEnvWF HrefSel HabstractTyped HMabsTyped
      narrowDomains Ydoms narrowResidual rY
      hnarrowTarget hYtarget hnarrowLength hYlen
      n (by omega) (by omega) (by
        intro position hposition _hi₁ _hi₂ d₁ d₂ Hb₁ Hb₂
        obtain ⟨d, Hd⟩ := hagM.binderAt_indep hnM position (by omega)
        have E₁ := Hd (S.sourceFullContext.lctx.mkForall S.hypotheses
          S.motiveApp)
        rw [← horigin] at E₁
        have E₁' := E₁.abstractList sourceBinders 0
        have E₂' := (Hd (.sort .zero)).abstractList sourceBinders 0
        exact (Hb₁.unique E₁').trans (E₂'.unique Hb₂))
  have hYtake : Ydoms.take n = Ydoms := by
    rw [show n = Ydoms.length by simp [hYlen, hSn]]
    exact List.take_length
  rw [hYtake, List.reverse_reverse] at HNY
  rw [hYtarget, VExpr.liftN_wrapForalls] at HYeq
  have HYM := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    (VEnv.IsDefEqCtx.refl HscopeWF.toCtx)
    (by simp [hYlen, hMdomsLen, hSn]) HYeq
  rw [List.reverse_reverse] at HYM
  -- The checker domains agree with the checked constructor fields.
  have hT₀' := hT₀.mono hrootEnv
  have hroot' := hroot.mono hterminalEnv
  have Huniq := Hchecked.uniq H.outVEnvWF (.refl H.outVEnvWF HPwf) hT₀'
  have Hwrap := Huniq.trans H.outVEnvWF HPwf.toCtx hroot'
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at Hwrap
  have HCM := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    (VEnv.IsDefEqCtx.refl HPwf.toCtx) (hchecked.trans hMdomsLen.symm) Hwrap
  have HCMQ := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HPQ.symm H.outVEnvWF.ordered).defeqCtx HCM
  have hscopeLams := VLCtx.lams_of_declarations Hscope.declarations
  have hscopeLen : scope.length = (T.params ++ Trest).length := by
    have h := Hprefix.length_eq
    rw [VLCtx.toCtx_length_of_lams hscopeLams] at h
    simp [Trest, base] at h ⊢
    omega
  have hscopeSplit : scope.toCtx =
      (VLCtx.toCtx (scope.take m')) ++ (VLCtx.toCtx (scope.drop m')) := by
    rw [← VLCtx.toCtx_append, List.take_append_drop]
  have hXlen : (VLCtx.toCtx (scope.take m')).length = m' := by
    rw [VLCtx.toCtx_length_of_lams
      (fun e he => hscopeLams e (List.mem_of_mem_take he)), List.length_take]
    simp only [List.length_append] at hscopeLen
    omega
  have HCMS := VEnv.IsDefEqCtx.insertSameMiddle H.outVEnvWF.ordered
    checkedDomains.reverse (MLCtxForallDomains M S.fields.size hnM).reverse
    (VLCtx.toCtx (scope.take m')) (VLCtx.toCtx (scope.drop m')) HCMQ
    (by simp [hchecked, hMdomsLen, Mdoms]; rfl)
    (by rw [← hscopeSplit]; exact HscopeWF.toCtx)
  rw [hXlen] at HCMS
  simp only [List.append_assoc] at HCMS
  rw [← hscopeSplit] at HCMS
  have HNC := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (VEnv.IsDefEqCtx.transEmpty H.outVEnvWF HNY HYM)
    (HCMS.symm H.outVEnvWF.ordered)
  have Hlc := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (Hprefix.symm H.outVEnvWF.ordered) (HNC.symm H.outVEnvWF.ordered)
  have Hext := VEnv.IsDefEqCtx.extendSamePrefix
    (Hprefix.symm H.outVEnvWF.ordered)
    (Hlc.symm H.outVEnvWF.ordered).isType
  exact VEnv.IsDefEqCtx.transEmpty H.outVEnvWF Hlc
    (VEnv.IsDefEqCtx.transEmpty H.outVEnvWF Hext HnarrowInstalled)

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
  obtain ⟨HPQ, W⟩ := A.finalOuterParameterBase T Houter houterScope HouterPrefix
  obtain ⟨t, Ht, Hteq⟩ := HcheckedTail.defeqDFC' H.outVEnvWF HPQ
  have Ht' := Ht.weakFV H.outVEnvWF.ordered W Houter.wf
  rcases Hteq with ⟨_, Hteq₀⟩
  have Hteq' : H.outVEnv.IsDefEqU Us.length outerScope.toCtx
      (t.liftN inserted.length 0)
      ((VExpr.wrapForalls checkedDomains checkedResidual).liftN
        inserted.length 0) :=
    ⟨_, Hteq₀.weakN H.outVEnvWF.ordered W.toCtx⟩
  have Huniq := Ht'.uniq H.outVEnvWF (.refl H.outVEnvWF Houter.wf) HouterTail
  have Hwhole := Hteq'.symm.trans H.outVEnvWF Houter.wf.toCtx Huniq
  rw [VExpr.liftN_wrapForalls] at Hwhole
  have Hnatural := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    (VEnv.IsDefEqCtx.refl Houter.wf.toCtx)
    (by simp [hcheckedFields, houterFields]) Hwhole
  let equationFieldDomains :=
    (liftContextPrefix inserted.length checkedDomains.reverse).reverse
  have Hfull := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HouterPrefix.symm H.outVEnvWF.ordered) Hnatural
  exact ⟨equationFieldDomains, rfl, by
      simpa [equationFieldDomains, inserted, liftContextPrefix] using
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
            (B.forwardDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorTransportedFieldContext with
    ⟨S, HS, sourceDomains, sourceResidual, consumedDomains,
      consumedResidual, _hlocal, htail, hsource, hconsumed,
      Hsource, hconsumedTarget, HsourceConsumed⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
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
  rcases A.finalSelectedMinorSemanticSource with
    ⟨S, HS, _hlocal, htail⟩
  rcases HS.semantic.parameterTranslationAtSuffix with
    ⟨narrowTarget, Hnarrow₀⟩
  have hbaseEnv : HS.semantic.rootWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.fieldsRecent.contextExtension.venv_eq,
      ← HS.semantic.hypothesesRecent.contextExtension.venv_eq,
      ← HS.semantic.extension.venv_eq, H.recursorEnv]
    exact H.constructorVEnv_le
  have Hnarrow₁ := Hnarrow₀.mono hbaseEnv
  have Hnarrow : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      narrowTarget := by
    simpa only [HS.parameterDecls_eq, htail] using Hnarrow₁
  rcases TrExprS.forallTelescope_shape
      A.semantics.fieldOpening.telescope Hnarrow with
    ⟨narrowDomains, narrowResidual, hnarrowLength, hnarrowTarget⟩
  rw [hnarrowTarget] at Hnarrow
  refine ⟨S, HS, narrowDomains, narrowResidual, hnarrowLength, Hnarrow, ?_⟩
  have hrecBase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
  have HPwf : VLCtx.WF H.outVEnv Us.length H.parameterSuffix.parameterDecls :=
    H.parameterSuffix.parameterWF.mono hrecBase
  rcases Nat.eq_zero_or_pos A.rule.allArgs.size with h0 | hpos
  · have hnD : narrowDomains = [] :=
      List.eq_nil_of_length_eq_zero (hnarrowLength.trans h0)
    have hfD : B.fieldDomains = [] :=
      List.eq_nil_of_length_eq_zero (B.fieldDomains_length.trans h0)
    rw [hnD, hfD]
    exact VEnv.IsDefEqCtx.refl HPwf.toCtx
  have hfieldBaseEnv : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq, H.recursorEnv]
    exact H.constructorVEnv_le
  have hctxEnv : A.semantics.context.venv ≤ H.outVEnv := by
    rw [A.semantics.context_venv, H.recursorEnv]
    exact H.constructorVEnv_le
  obtain ⟨M, _hMwf, hchkM, hnM, hagM, hdropM, T₀, hT₀, t₀', _ht₀', hroot⟩ :=
    A.semantics.fieldCheck
  rw [A.parameterDecls_eq] at hT₀ hroot hdropM
  have hT₀' := hT₀.mono hfieldBaseEnv
  have hroot' := hroot.mono hctxEnv
  have Huniq := Hnarrow.uniq H.outVEnvWF (.refl H.outVEnvWF HPwf) hT₀'
  have Hwrap := Huniq.trans H.outVEnvWF HPwf.toCtx hroot'
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at Hwrap
  have HdomLen := hagM.forallDomains_length hnM
  have Hctx1 := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF
    (VEnv.IsDefEqCtx.refl HPwf.toCtx)
    (hnarrowLength.trans HdomLen.symm) Hwrap
  have hMsplit := hagM.toCtx_split hnM
  rw [hdropM] at hMsplit
  rw [← hMsplit] at Hctx1
  have Halign := (B.checkAlign hpos).mono hfieldBaseEnv
  rw [hchkM hpos] at Halign
  have HfieldCtx := Halign.defeqCtx
  rw [B.fieldScope_eq, abstractForallContext_toCtx, A.parameterDecls_eq]
    at HfieldCtx
  exact VEnv.IsDefEqCtx.transEmpty H.outVEnvWF Hctx1
    (HfieldCtx.symm H.outVEnvWF.ordered)

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
    exact H.constructorVEnv_le
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us, A.parameterDecls_eq] using
      HfieldCtx.drop B.fieldDomains.length
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
    exact H.constructorVEnv_le
  have Hchecked' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual) := by
    simpa only [← H.parameterDecls] using Hchecked
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us, A.parameterDecls_eq] using
      HfieldCtx.drop B.fieldDomains.length
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
    exact H.constructorVEnv_le
  have HparameterCtx : OnCtx H.parameterSuffix.parameterDecls.toCtx
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx := B.fieldContextWF
    rw [abstractForallContext_toCtx] at HfieldCtx
    simpa [Us, A.parameterDecls_eq] using
      HfieldCtx.drop B.fieldDomains.length
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
      ⟨fieldDomains, hfieldDomains, hfieldFront⟩, hcheckAlign⟩
  rcases A.semantics.fieldContextDefEqMono with
    ⟨_sourceDomains, _sourceResidual, forwardDomains, forwardResidual,
      _hsourceDomains, hforwardDomains, _Hsource, hforwardTarget,
      _Hcontexts⟩
  exact ⟨{
    fieldScope := fieldScope
    runtime := HfieldScope
    scope_fvars := hfieldScopeFVars
    scope_base := hfieldBase
    fieldDomains := fieldDomains
    fieldDomains_length := hfieldDomains
    front := hfieldFront
    forwardDomains := forwardDomains
    forwardResidual := forwardResidual
    forwardDomains_length := hforwardDomains
    forwardTarget := hforwardTarget
    checkAlign := hcheckAlign }⟩





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
