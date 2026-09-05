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
  VEnv.addProjections_le.trans H.installed.le

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

/-- Select exactly the producer-declared field/parameter dependencies from
the actual staged origin of a recursive call.  Ambient hypotheses generated
for earlier recursive fields are skipped by `narrowFVars`; the retained
translation evidence is derived from the origin context itself. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootNarrowScope
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
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.originContext.mlctx.vlctx,
        ∀ fv, fv ∈ scope.fvars ↔
          fv ∈ F.originContext.mlctx.vlctx.fvars ∧
            F.semantic.rootScope fv := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  classical
  rcases checkInductiveTypes.loopType.narrowFVars
      F.originContext.onlyLams F.originContext.checking.tr.wf
      F.originContext.mlctx_wf F.semantic.rootScope F.rootScope_up with
    ⟨scope, Hscope, hscope⟩
  have henv : F.originContext.venv ≤ H.outVEnv := by
    rw [F.originExtension.venv_eq, A.semantics.context_venv,
      H.recursorEnv]
    exact H.constructorVEnv_le
  refine ⟨scope, Hscope.mono henv, ?_⟩
  intro fv
  rw [hscope, List.mem_filter]
  simp

/-- Reconstruct the call-local lambda suffix above the dependency-selected
producer root.  Earlier induction hypotheses remain in the executable
origin but are skipped by the root `FVarNarrowScope`; only the freshly
generated higher-order arguments are replayed. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.localNarrowScope
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
    ∃ rootScope,
      ∃ Hroot : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us rootScope F.originContext.mlctx.vlctx,
        (∀ fv, fv ∈ rootScope.fvars ↔
          fv ∈ F.originContext.mlctx.vlctx.fvars ∧
            F.semantic.rootScope fv) ∧
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            scope.fvars = F.semantic.recent.fvars.reverse ++
              rootScope.fvars ∧
            scope.drop F.semantic.generated.localArgs.size = rootScope ∧
            ∃ localDomains : List VExpr,
              localDomains.length = F.semantic.generated.localArgs.size ∧
              scope.toCtx = localDomains.reverse ++ rootScope.toCtx ∧
              Hscope.shift = Hroot.shift.consN
                F.semantic.generated.localArgs.size ∧
              Hscope.expanded.toCtx =
                (liftForallDomains localDomains Hroot.shift).reverse ++
                  Hroot.expanded.toCtx ∧
              ∀ {body target},
                TrExprS H.outVEnv Us scope body target →
                H.outVEnv.IsType Us.length scope.toCtx target →
                TrExprS H.outVEnv Us rootScope
                    (F.semantic.generated.current.lctx.mkForall
                      F.semantic.generated.localArgs body)
                    (VExpr.wrapForalls localDomains target) ∧
                  H.outVEnv.IsType Us.length rootScope.toCtx
                    (VExpr.wrapForalls localDomains target) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.rootNarrowScope with ⟨rootScope, Hroot, hroot⟩
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨semanticLocalDomains, HlocalPrefix⟩
  have hbase : F.semantic.current_context.venv ≤ H.outVEnv := by
    rw [F.semantic.recent.venv_eq, F.originExtension.venv_eq,
      A.semantics.context_venv, H.recursorEnv]
    exact H.constructorVEnv_le
  have HcurrentWF : F.semantic.current_context.mlctx.WF H.outVEnv Us :=
    F.semantic.current_context.mlctx_wf.mono hbase
  have hlocalRev :
      F.semantic.current_context.mlctx.fvarRevList
          F.semantic.generated.localArgs.size HlocalPrefix.le =
        F.semantic.recent.fvars.reverse := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.fvarRevList_eq
  have hlocalRuntime :
      (F.semantic.current_context.mlctx.dropN
        F.semantic.generated.localArgs.size HlocalPrefix.le).vlctx =
          F.originContext.mlctx.vlctx := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.semantic.recent.drop_eq]
  let HrootAtDrop := Hroot.retargetRuntime hlocalRuntime.symm
  have Hup : IsFVarUpSet
      (fun fv => fv ∈
        F.semantic.current_context.mlctx.fvarRevList
            F.semantic.generated.localArgs.size HlocalPrefix.le ++
          rootScope.fvars)
      F.semantic.current_context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HcurrentWF.tr.wf.fvwf ?_).mp
      F.semantic.current_scope_up
    intro fv hfv
    rw [hlocalRev]
    constructor
    · intro hselected
      rcases hselected with hlocal | hrootSelected
      · exact List.mem_append_left _
          (List.mem_reverse.mpr hlocal)
      · exact List.mem_append_right _ <| (hroot fv).2
          ⟨F.rootScope_mem_originContext hrootSelected, hrootSelected⟩
    · intro hselected
      rcases List.mem_append.mp hselected with hlocal | hrootSelected
      · exact Or.inl (List.mem_reverse.mp hlocal)
      · exact Or.inr (hroot fv |>.1 hrootSelected).2
  rcases HlocalPrefix.extendFVarNarrowScope H.outVEnvWF
      HcurrentWF HrootAtDrop Hup with
    ⟨scope, Hscope, hscopeFVars, hscopeBase, localDomains,
      hlocalDomains, hscopeContext, hscopeShift, hscopeExpanded,
      Hreplay⟩
  have hsource : ∀ body,
      F.semantic.current_context.mlctx.mkForall
          F.semantic.generated.localArgs.size HlocalPrefix.le body =
        F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs body := by
    intro body
    rw [← F.semantic.current_context.lctx_eq]
    symm
    apply F.semantic.current_context.mlctx_wf.mkForall_eq
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    simpa only [hle] using F.semantic.recent.reverse_eq
  refine ⟨rootScope, Hroot, hroot, scope, Hscope, ?_, ?_,
    localDomains, hlocalDomains, hscopeContext, hscopeShift,
    hscopeExpanded, ?_⟩
  · simpa [hlocalRev] using hscopeFVars
  · simpa [HrootAtDrop,
      checkInductiveTypes.loopType.FVarNarrowScope.retargetRuntime] using
        hscopeBase
  · intro body target Hbody HbodyType
    rw [← hsource]
    exact Hreplay Hbody HbodyType

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
    declarations := Hdeclarations }

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
  rcases HlocalPrefix.extendFVarNarrowCore H.outVEnvWF HlocalWF
      HlocalBase HlocalUp with
    ⟨scope, Hscope, hscope, hdrop, localDomains, hlocal,
      hcontext, _hshift, Hreplay⟩
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
  exact ⟨scope, Hscope, by simpa [hlocalRev] using hscope,
    hdrop, localDomains, hlocal, hcontext, by
      intro body target Hbody HbodyType
      rw [hsource]
      simpa [HlocalBase,
        checkInductiveTypes.loopType.FVarNarrowCore.retargetRuntime] using
        Hreplay Hbody HbodyType⟩

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
          narrowIndices evidence.indices := by
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
      hcontext, Hreplay⟩
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
  have restrictIndices : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
          (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
          sources targets →
      sources ⊆ sourceIndices →
      ∃ narrowTargets,
        List.Forall₂ (TrExprS H.outVEnv Us scope) sources narrowTargets ∧
        List.Forall₂
          (fun narrow full => H.outVEnv.IsDefEqU Us.length
            F.semantic.current_context.mlctx.vlctx.toCtx
            (narrow.lift' Hscope.shift) full)
          narrowTargets targets := by
    intro sources targets Htranslated hsubset
    induction Htranslated with
    | nil => exact ⟨[], .nil, .nil⟩
    | @cons source target sources targets Hindex _ ih =>
      have hsource : source ∈ sourceIndices := hsubset List.mem_cons_self
      have Hsource := HsourceScope source hsource
      have HsourceNarrow : source.FVarsIn (· ∈ scope.fvars) := by
        apply Hsource.mono
        intro fv hfv
        rw [F.root_scope,
          A.semantics.fieldOpening.fvars_eq_bound
            A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
          at hfv
        rw [hscopeExact, H.parameterSuffix.parameterDecls_fvars]
        rcases hfv with hlocalFv | hfield | hparam
        · exact List.mem_append_left _
            (List.mem_append_left _ (List.mem_reverse.mpr hlocalFv))
        · exact List.mem_append_left _
            (List.mem_append_right _ (List.mem_reverse.mpr hfield))
        · exact List.mem_append_right _ (List.mem_reverse.mpr hparam)
      have hclosed : Closed source 0 := by
        have h := Hindex.closed
        rw [F.semantic.current_context.mlctx.noBV] at h
        exact h
      rcases Hscope.restrictEq H.outVEnvWF Hindex hclosed HsourceNarrow with
        ⟨narrowTarget, HnarrowTarget, HtargetEq⟩
      have htailSubset : sources ⊆ sourceIndices := by
        intro other hother
        exact hsubset (List.mem_cons_of_mem source hother)
      rcases ih htailSubset with ⟨narrowTargets, Hnarrow, Heq⟩
      exact ⟨narrowTarget :: narrowTargets,
        .cons HnarrowTarget Hnarrow, .cons HtargetEq.symm Heq⟩
  rcases restrictIndices HindicesFinal (List.Subset.refl sourceIndices) with
    ⟨narrowIndices, HnarrowIndices, HindexEq⟩
  exact ⟨binding, evidence, scope, Hscope, localDomains, narrowIndices,
    hscopeExact, hdrop, hlocal, hcontext, Hreplay, hlength,
    HnarrowIndices, HindexEq⟩

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
      hlength, Hindices, HindexEq⟩
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
  rcases Hscope.restrictEq H.outVEnvWF HmajorFinal hmajorClosed
      hmajorScope with ⟨narrowMajor, Hmajor, HmajorEq⟩
  rcases Hscope.restrictEq H.outVEnvWF HexposedFinal hexposedClosed
      hexposedScope with ⟨narrowExposed, Hexposed, _HexposedEq⟩
  have HfullMajorType : F.semantic.current_context.venv.HasType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.appliedFieldTarget F.semantic.exposedTarget :=
    F.semantic.applied_field_typing.defeqU_r
      F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm
  rw [hsemantic] at HfullMajorType
  have Htyping := Hscope.hasTypeOfFullPair H.outVEnvWF Hmajor Hexposed
    HmajorFinal HexposedFinal (HfullMajorType.mono H.constructorVEnv_le)
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
      _ = F.semantic.generated.abstractedMajor :=
        (F.semantic.generated.abstractedMajor_eq_of_closed
          hfieldClosed).symm
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
    ⟨outerScope, Houter, outerFields, outerResidual,
      ruleFields, ruleResidual, houterScope,
      houterShift, houterFields, HouterTail, _HouterType,
      HouterPrefix, hruleFields, hruleTarget, HouterSemantic⟩
  have hruleDomains : ruleFields = B.forwardDomains := by
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) hruleFields
      B.forwardDomains_length (by
        simpa using hruleTarget.symm.trans B.forwardTarget)
  rw [hruleDomains] at HouterSemantic
  have HselectedOuter := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HselectedNarrow (HouterSemantic.symm H.outVEnvWF.ordered)
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
    exact H.constructorVEnv_le
  rcases A.semantics.fieldContextDefEqMono with
    ⟨runtimeDomains, runtimeResidual, _consumedDomains, _consumedResidual,
      _hruntimeDomains, _hconsumedDomains, Hruntime₀,
      _hconsumedTarget, _Hcontexts⟩
  have Hruntime : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls runtimeDomains runtimeResidual) :=
    Hruntime₀.mono hbase
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
  rcases B.runtime.front.base with
    ⟨baseScope, baseExpanded, baseShift, hscopeBase,
      hexpandedBase, hshift, Wbase⟩
  have hbaseScope : baseScope = H.parameterSuffix.parameterDecls := by
    rw [← hscopeBase, B.scope_base, A.parameterDecls_eq]
  subst baseScope
  rcases B.semanticFieldContext with
    ⟨_hruleLength, _hsemanticContext, hfrontExpanded,
      _hexpandedContext, HfieldBase, _Hexpanded⟩
  have HbaseContext : VLCtx.IsDefEq H.outVEnv Us.length
      baseExpanded A.semantics.fieldRootContext.mlctx.vlctx := by
    rw [hfrontExpanded] at hexpandedBase
    have HfieldBase' := HfieldBase
    rw [hexpandedBase] at HfieldBase'
    exact HfieldBase'
  rw [hbaseScope] at Wbase
  have HnarrowWeak : TrExprS H.outVEnv Us baseExpanded
      A.semantics.parameterTail
      ((VExpr.wrapForalls narrowDomains narrowResidual).lift'
        baseShift) := by
    exact Hnarrow.weakFV' H.outVEnvWF.ordered Wbase HbaseContext.wf
  have hfieldBaseEnv : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq, H.recursorEnv]
    exact H.constructorVEnv_le
  rcases A.semantics.fieldContextDefEq with
    ⟨sourceDomains, sourceResidual, hsource, hparameterTarget,
      HsourceFields₀⟩
  have Hsource : TrExprS H.outVEnv Us
      A.semantics.fieldRootContext.mlctx.vlctx A.semantics.parameterTail
      (VExpr.wrapForalls sourceDomains sourceResidual) := by
    have Htr := A.semantics.parameterTranslation.mono hfieldBaseEnv
    simpa only [hparameterTarget] using Htr
  have Htarget := HnarrowWeak.uniq H.outVEnvWF HbaseContext Hsource
  rw [VExpr.lift'_wrapForalls_exact] at Htarget
  let liftedDomains := liftForallDomains narrowDomains baseShift
  have hliftedLength : liftedDomains.length = narrowDomains.length := by
    exact liftForallDomains_length narrowDomains baseShift
  have HbaseDefEq : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (VLCtx.toCtx baseExpanded)
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx :=
    HbaseContext.defeqCtx
  have HliftedSource := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF HbaseDefEq
      (hliftedLength.trans hnarrowLength |>.trans hsource.symm) Htarget
  have HsourceFields := HsourceFields₀.mono hfieldBaseEnv
  rcases B.semanticFieldContext with
    ⟨_hruleLength, _hsemanticContext, _hfrontExpanded,
      _hexpandedContext, _HfieldBase, Hexpanded⟩
  have HsourceExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HsourceFields (Hexpanded.symm H.outVEnvWF.ordered)
  have HliftedExpanded := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HliftedSource HsourceExpanded
  have hexpandedContext : B.runtime.expanded.toCtx =
      B.runtime.frontExpandedDomains.reverse ++ VLCtx.toCtx baseExpanded := by
    rw [B.runtime.front.expandedContext, hexpandedBase]
  rw [hexpandedContext] at HliftedExpanded
  have HsourceType := A.semantics.parameterType.mono hfieldBaseEnv
  have HrootWF : VLCtx.WF H.outVEnv Us.length
      A.semantics.fieldRootContext.mlctx.vlctx :=
    (A.semantics.fieldRootContext.mlctx_wf.mono hfieldBaseEnv).tr.wf
  have HparameterTranslation :=
    A.semantics.parameterTranslation.mono hfieldBaseEnv
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
    exact H.constructorVEnv_le
  have hfieldBase : A.semantics.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.semantics.fieldRootExtension.venv_eq]
    exact hbase
  let Hruntime := B.runtime.mono hfieldBase
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
    rw [B.scope_fvars, A.parameterDecls_eq,
      H.parameterSuffix.parameterDecls_fvars]
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
              A.semantics.parameterSuffix.parameterDecls.fvars =
          A.semantics.fieldsRecent.fvars.reverse ++
              A.semantics.parameterSuffix.parameterDecls.fvars := by
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
    rw [← A.parameterDecls_eq, ← B.fieldScope_eq]
    exact HtargetType
  exact ⟨target, by simpa only [A.parameterDecls_eq] using Hclosed,
    HtargetType'⟩

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
    forwardTarget := hforwardTarget }⟩





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
    (Hscope : checkInductiveTypes.loopType.FVarNarrowCore
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
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
  have Hmajor := F.semantic.applied_field_translation
  rw [hsemantic] at Hmajor
  have HmajorFinal := Hmajor.mono H.constructorVEnv_le
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
    (Hscope : checkInductiveTypes.loopType.FVarNarrowCore
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
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
  have Hfull := F.semantic.exposed_translation
  have HfullType : F.semantic.current_context.venv.IsType Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.exposedTarget :=
    VEnv.IsType.defeqU_l F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm F.semantic.terminal_type
  rw [hsemantic] at Hfull HfullType
  have HfullFinal := Hfull.mono H.constructorVEnv_le
  have HfullTypeFinal := HfullType.mono H.constructorVEnv_le
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
    (Hscope : checkInductiveTypes.loopType.FVarNarrowCore
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
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
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
    (HfullMajor.mono H.constructorVEnv_le)
    (HfullExposed.mono H.constructorVEnv_le)
    (HfullMajorType.mono H.constructorVEnv_le)
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
    (Hscope : checkInductiveTypes.loopType.FVarNarrowCore
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
      (F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans
        (H.recursorEnv))
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
    (HfullMajor.mono H.constructorVEnv_le)
    (HfullExposed.mono H.constructorVEnv_le)
    (HfullMajorType.mono H.constructorVEnv_le)
  exact ⟨narrowExposed, HnarrowExposed, Htyped⟩

/-- Package every semantic argument of a generated recursive call in one
dependency-selected scope.  Earlier recursive hypotheses may occur between
the retained locals and constructor fields in the executable context; the
`FVarNarrowScope` shift records those skips explicitly, so subsequent
equation assembly never has to reconstruct a fictitious contiguous front. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.selectedSemanticCallArgumentFrame
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
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
      ∃ rootScope,
      ∃ Hroot : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us rootScope F.originContext.mlctx.vlctx,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
      ∃ (localDomains narrowIndices : List VExpr)
          (narrowMajor narrowExposed : VExpr),
        rootScope.fvars = A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars ∧
        scope.fvars = F.semantic.recent.fvars.reverse ++ rootScope.fvars ∧
        scope.drop F.semantic.generated.localArgs.size = rootScope ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        scope.toCtx = localDomains.reverse ++ rootScope.toCtx ∧
        Hscope.shift = Hroot.shift.consN
          F.semantic.generated.localArgs.size ∧
        TrExprS H.outVEnv Us rootScope
          (F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs (.sort .zero))
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        H.outVEnv.IsType Us.length rootScope.toCtx
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        evidence.indices.length = F.telescope.indices.length ∧
        List.Forall₂ (TrExprS H.outVEnv Us scope)
          sourceIndices narrowIndices ∧
        TrExprS H.outVEnv Us scope
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs) narrowMajor ∧
        TrExprS H.outVEnv Us scope
          F.semantic.generated.exposedType narrowExposed ∧
        H.outVEnv.HasType Us.length scope.toCtx narrowMajor narrowExposed ∧
        List.Forall₂
          (fun narrow full => H.outVEnv.IsDefEqU Us.length
            F.semantic.current_context.mlctx.vlctx.toCtx
            (narrow.lift' Hscope.shift) full)
          narrowIndices evidence.indices ∧
        H.outVEnv.IsDefEqU Us.length
          F.semantic.current_context.mlctx.vlctx.toCtx
          F.semantic.appliedFieldTarget
          (narrowMajor.lift' Hscope.shift) ∧
        H.outVEnv.IsDefEqU Us.length
          F.semantic.current_context.mlctx.vlctx.toCtx
          (narrowExposed.lift' Hscope.shift) F.semantic.exposedTarget := by
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
  rcases F.currentNarrowScope with
    ⟨rootScope, Hroot, scope, Hscope, hroot, hscope, hdrop,
      localDomains, hlocal, hcontext, hshift, Hreplay⟩
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hzero : TrExprS H.outVEnv Us scope
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have HzeroType : H.outVEnv.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  rcases Hreplay Hzero HzeroType with
    ⟨HlocalTemplate, HlocalTemplateType⟩
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
  have narrowIndicesFor : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
          (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
          sources targets →
      sources ⊆ sourceIndices →
      ∃ narrowTargets,
        List.Forall₂ (TrExprS H.outVEnv Us scope) sources narrowTargets ∧
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
        hsubset List.mem_cons_self
      have Hsource := HsourceScope source hsource
      have HsourceNarrow : source.FVarsIn (· ∈ scope.fvars) := by
        apply Hsource.mono
        intro fv hfv
        rw [hscope, hroot,
          H.parameterSuffix.parameterDecls_fvars]
        have hopen : A.semantics.fieldOpening.fvars =
            A.semantics.fieldsRecent.fvars :=
          A.semantics.fieldOpening.fvars_eq_bound
            A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
        rcases hfv with hlocalFv | hrootFv
        · exact List.mem_append_left _ (List.mem_reverse.mpr hlocalFv)
        · rw [F.root_scope] at hrootFv
          rcases hrootFv with hfield | hparam
          · apply List.mem_append_right
            apply List.mem_append_left
            rw [← hopen]
            exact List.mem_reverse.mpr hfield
          · apply List.mem_append_right
            apply List.mem_append_right
            exact List.mem_reverse.mpr hparam
      have hclosed : Closed source 0 := by
        have h := Hindex.closed
        rw [F.semantic.current_context.mlctx.noBV] at h
        exact h
      rcases Hscope.restrictEq H.outVEnvWF Hindex hclosed HsourceNarrow with
        ⟨narrowTarget, HnarrowTarget, HtargetEq⟩
      have htailSubset : sources ⊆ sourceIndices := by
        intro other hother
        exact hsubset (List.mem_cons_of_mem source hother)
      rcases ih htailSubset with ⟨narrowTargets, Hnarrow, Heq⟩
      exact ⟨narrowTarget :: narrowTargets,
        .cons HnarrowTarget Hnarrow, .cons HtargetEq.symm Heq⟩
  rcases narrowIndicesFor HindicesFinal (List.Subset.refl sourceIndices) with
    ⟨narrowIndices, HnarrowIndices, HindexEq⟩
  have hscopeExact : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars := by
    rw [hscope, hroot, List.append_assoc]
  rcases F.narrowSemanticAppliedMajor scope Hscope.toCore hscopeExact with
    ⟨narrowMajor, HnarrowMajor, HmajorEq⟩
  rcases F.narrowSemanticAppliedMajorTypingFor scope Hscope.toCore hscopeExact
      HnarrowMajor with
    ⟨narrowExposed, HnarrowExposed, HnarrowTyping⟩
  rcases F.narrowSemanticExposedType scope Hscope.toCore hscopeExact with
    ⟨_otherExposed, _resultLevel, _HotherExposed, HexposedEq,
      _HotherType⟩
  have HnarrowExposedEq : H.outVEnv.IsDefEqU Us.length
      F.semantic.current_context.mlctx.vlctx.toCtx
      (narrowExposed.lift' Hscope.shift) F.semantic.exposedTarget := by
    have hsemantic : F.semantic.current_context.venv =
        R.context.venv :=
      F.semantic.recent.venv_eq.trans
        (F.originExtension.venv_eq.trans <|
          A.semantics.context_venv.trans
          (H.recursorEnv))
    have Hfull := F.semantic.exposed_translation
    rw [hsemantic] at Hfull
    exact Hscope.fullTargetEq H.outVEnvWF HnarrowExposed
      (Hfull.mono H.constructorVEnv_le |>.trExpr H.outVEnvWF
        (Hscope.context.symm H.outVEnvWF.ordered).wf)
  exact ⟨binding, evidence, rootScope, Hroot, scope, Hscope,
    localDomains, narrowIndices, narrowMajor, narrowExposed,
    hroot, hscope, hdrop, hlocal, hcontext, hshift,
    HlocalTemplate, HlocalTemplateType, hlength, HnarrowIndices, HnarrowMajor,
    HnarrowExposed, HnarrowTyping,
    HindexEq, HmajorEq, HnarrowExposedEq⟩

/-- Close the complete dependency-selected call scope and split its target
telescope after the common parameters.  This is the equation-facing form of
`selectedSemanticCallArgumentFrame`: its source abstractions are literally
the generated local/field/parameter abstractions, while its target domains
come from the one selected semantic scope rather than an unrelated replay. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.closedSelectedSemanticCallArgumentFrame
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
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
      ∃ (parameterDomains fieldDomains localDomains narrowIndices : List VExpr)
          (narrowMajor narrowExposed : VExpr),
        scope.toCtx.reverse = parameterDomains ++ fieldDomains ++
          localDomains ∧
        parameterDomains.length = stats.params.size ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (parameterDomains ++ fieldDomains) [])
          (((F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs (.sort .zero)).abstractList
              A.rule.all_args_bound.fvars).abstractList
                A.rule.params_bound.fvars A.rule.allArgs.size)
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext (parameterDomains ++ fieldDomains) []).toCtx
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        OnCtx
          (abstractForallContext
            (parameterDomains ++ fieldDomains ++ localDomains) []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        evidence.indices.length = F.telescope.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              (parameterDomains ++ fieldDomains ++ localDomains) []))
          (sourceIndices.map fun index =>
            ((index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                F.semantic.generated.localArgs.size).abstractList
                  A.rule.params_bound.fvars cutoff)
          narrowIndices ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDomains ++ fieldDomains ++ localDomains) [])
          ((F.semantic.generated.outerAbstractedMajor
            A.rule.all_args_bound.fvars).abstractList
              A.rule.params_bound.fvars cutoff) narrowMajor ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDomains ++ fieldDomains ++ localDomains) [])
          (((F.semantic.generated.exposedType.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.all_args_bound.fvars
              F.semantic.generated.localArgs.size).abstractList
                A.rule.params_bound.fvars cutoff) narrowExposed ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext
            (parameterDomains ++ fieldDomains ++ localDomains) []).toCtx
          narrowMajor narrowExposed ∧
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
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  rcases F.selectedSemanticCallArgumentFrame with
    ⟨binding, evidence, rootScope, Hroot, scope, Hscope,
      localDomains, narrowIndices, narrowMajor, narrowExposed,
      hroot, hscope, _hdrop, hlocal, hscopeContext, _hshift,
      HlocalTemplate, HlocalTemplateType, hlength,
      Hindices, Hmajor, Hexposed, Htyping, HindexEq, HmajorEq,
      _HexposedEq⟩
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
  have hparameterFVars : H.parameterSuffix.parameterDecls.fvars =
      A.rule.params_bound.fvars.reverse := by
    rw [H.parameterSuffix.parameterDecls_fvars,
      A.rule.params_bound.exprArrayFVarIds]
  have hscopeNames : scope.fvars.reverse =
      A.rule.params_bound.fvars ++ A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars := by
    rw [hscope, hroot, List.reverse_append, List.reverse_append,
      hlocalFVars, hfieldFVars, hparameterFVars,
      List.reverse_reverse]
    simp [List.append_assoc]
  have hscopeNamesNodup :
      (A.rule.params_bound.fvars ++ A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars).Nodup := by
    rw [← hscopeNames]
    exact List.nodup_reverse.mpr (Hscope.scopeWF H.outVEnvWF).fvars_nodup
  have hsourceShape : ∀ source : Expr,
      source.abstractList scope.fvars.reverse =
        ((source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff := by
    intro source
    have hallNodup :
        (A.rule.params_bound.fvars ++
          (A.rule.all_args_bound.fvars ++
            F.semantic.generated.arguments_bound.fvars)).Nodup := by
      simpa [List.append_assoc] using hscopeNamesNodup
    have hfieldsLocalsNodup :
        (A.rule.all_args_bound.fvars ++
          F.semantic.generated.arguments_bound.fvars).Nodup :=
      (List.nodup_append.mp hallNodup).2.1
    have hfirst := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.all_args_bound.fvars)
      (inner := F.semantic.generated.arguments_bound.fvars) (k := 0)
      hfieldsLocalsNodup
    have hsecond := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.params_bound.fvars)
      (inner := A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars) (k := 0)
      hallNodup
    have hlocalLength :
        F.semantic.generated.arguments_bound.fvars.length =
          F.semantic.generated.localArgs.size :=
      F.semantic.generated.arguments_bound.length_fvars
    have hfieldLength : A.rule.all_args_bound.fvars.length =
        A.rule.allArgs.size := A.rule.all_args_bound.length_fvars
    rw [hlocalLength] at hfirst
    rw [← hfirst] at hsecond
    simpa [cutoff, hscopeNames, hlocalLength, hfieldLength,
      Nat.add_comm, List.append_assoc] using hsecond.symm
  have closeSource : ∀ {source : Expr} {target : VExpr},
      TrExprS H.outVEnv Us scope source target →
      TrExprS H.outVEnv Us
        (abstractForallContext scope.toCtx.reverse [])
        (((source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff) target := by
    intro source target Hsource
    have Hclosed := Hscope.abstractAll H.outVEnvWF Hsource
    rw [hsourceShape source] at Hclosed
    exact Hclosed
  have closeSources : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂ (TrExprS H.outVEnv Us scope) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext scope.toCtx.reverse []))
        (sources.map fun source =>
          ((source.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.all_args_bound.fvars
              F.semantic.generated.localArgs.size).abstractList
                A.rule.params_bound.fvars cutoff)
        targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hhead _ ih => exact .cons (closeSource Hhead) ih
  have HclosedIndices := closeSources Hindices
  have HclosedMajor := closeSource Hmajor
  have HclosedExposed := closeSource Hexposed
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
    have hfieldClosed : A.rule.recursiveArgs[j].looseBVarRange' = 0 := by
      have hclosed := F.semantic.field_translation.closed
      rw [F.originContext.mlctx.noBV] at hclosed
      exact hclosed.looseBVarRange_zero
    calc
      sourceMajor.abstractList F.semantic.generated.arguments_bound.fvars =
          mkAppN
            (A.rule.recursiveArgs[j].abstractList
              F.semantic.generated.arguments_bound.fvars)
            (List.ofFn (fun index :
              Fin F.semantic.generated.arguments_bound.fvars.length =>
                Expr.bvar
                  (F.semantic.generated.arguments_bound.fvars.length - 1 -
                    index))).toArray := by
        unfold sourceMajor
        rw [Expr.abstractList_mkAppN, hlocalAbstract]
      _ = F.semantic.generated.abstractedMajor :=
        (F.semantic.generated.abstractedMajor_eq_of_closed
          hfieldClosed).symm
  rw [show mkAppN A.rule.recursiveArgs[j]
      F.semantic.generated.localArgs = sourceMajor from rfl,
    hmajorLocal] at HclosedMajor
  let rootDomains := rootScope.toCtx.reverse
  let parameterDomains := rootDomains.take stats.params.size
  let fieldDomains := rootDomains.drop stats.params.size
  have hrootLength : rootDomains.length =
      stats.params.size + A.rule.allArgs.size := by
    calc
      rootDomains.length = rootScope.toCtx.length := by simp [rootDomains]
      _ = rootScope.length := Hroot.toCtx_length
      _ = rootScope.fvars.length := Hroot.fvars_length.symm
      _ = rootScope.fvars.reverse.length := by simp
      _ = _ := by
        rw [hroot, List.reverse_append, hfieldFVars, hparameterFVars,
          List.reverse_reverse]
        simp [A.rule.params_bound.length_fvars,
          A.rule.all_args_bound.length_fvars, Nat.add_comm]
  have hparamsLE : stats.params.size ≤ rootDomains.length := by omega
  have hparameters : parameterDomains.length = stats.params.size := by
    simp [parameterDomains, List.length_take, Nat.min_eq_left hparamsLE]
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp only [fieldDomains, List.length_drop]
    rw [hrootLength]
    omega
  have hrootDomains : rootDomains = parameterDomains ++ fieldDomains :=
    (List.take_append_drop stats.params.size rootDomains).symm
  have hall : scope.toCtx.reverse =
      parameterDomains ++ fieldDomains ++ localDomains := by
    rw [hscopeContext, List.reverse_append, List.reverse_reverse,
      ← hrootDomains]
  have hrootContext :
      (abstractForallContext (parameterDomains ++ fieldDomains) []).toCtx =
        rootScope.toCtx := by
    rw [← hrootDomains]
    simp [rootDomains, abstractForallContext_toCtx, VLCtx.toCtx]
  have hcontext :
      (abstractForallContext
        (parameterDomains ++ fieldDomains ++ localDomains) []).toCtx =
        scope.toCtx := by
    rw [← hall]
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  have hrootNames : rootScope.fvars.reverse =
      A.rule.params_bound.fvars ++ A.rule.all_args_bound.fvars := by
    calc
      rootScope.fvars.reverse =
          (A.semantics.fieldsRecent.fvars.reverse ++
            H.parameterSuffix.parameterDecls.fvars).reverse := by rw [hroot]
      _ = H.parameterSuffix.parameterDecls.fvars.reverse ++
          A.semantics.fieldsRecent.fvars := by simp
      _ = A.rule.params_bound.fvars ++
          A.rule.all_args_bound.fvars := by
        rw [hparameterFVars, hfieldFVars, List.reverse_reverse]
  have hrootNamesNodup :
      (A.rule.params_bound.fvars ++ A.rule.all_args_bound.fvars).Nodup := by
    rw [← hrootNames]
    exact List.nodup_reverse.mpr
      (Hroot.scopeWF H.outVEnvWF).fvars_nodup
  let rawLocalForall := F.semantic.generated.current.lctx.mkForall
    F.semantic.generated.localArgs (.sort .zero)
  have HclosedLocalTemplate₀ := Hroot.abstractAll
    H.outVEnvWF HlocalTemplate
  have hlocalSource : rawLocalForall.abstractList rootScope.fvars.reverse =
      ((rawLocalForall.abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size) := by
    have happend := Expr.abstractList_after_inner
      (e := rawLocalForall) (outer := A.rule.params_bound.fvars)
      (inner := A.rule.all_args_bound.fvars) (k := 0) hrootNamesNodup
    simpa [hrootNames, A.rule.all_args_bound.length_fvars] using happend.symm
  have HclosedLocalTemplate : TrExprS H.outVEnv Us
      (abstractForallContext (parameterDomains ++ fieldDomains) [])
      (((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars).abstractList
            A.rule.params_bound.fvars A.rule.allArgs.size)
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    rw [← hrootDomains]
    simpa [rootDomains, rawLocalForall, hlocalSource] using
      HclosedLocalTemplate₀
  have HclosedLocalTemplateType : H.outVEnv.IsType Us.length
      (abstractForallContext (parameterDomains ++ fieldDomains) []).toCtx
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    rw [hrootContext]
    exact HlocalTemplateType
  have HclosedIndices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDomains ++ fieldDomains ++ localDomains) []))
      (sourceIndices.map fun index =>
        ((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff)
      narrowIndices := by
    rw [← hall]
    exact HclosedIndices
  have HclosedMajor' : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDomains ++ fieldDomains ++ localDomains) [])
      ((F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars cutoff) narrowMajor := by
    rw [← hall]
    simpa [BoundGeneratedRecursiveCall.outerAbstractedMajor] using HclosedMajor
  have HclosedExposed' : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDomains ++ fieldDomains ++ localDomains) [])
      (((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
          F.semantic.generated.localArgs.size).abstractList
            A.rule.params_bound.fvars cutoff) narrowExposed := by
    rw [← hall]
    exact HclosedExposed
  have HclosedCtx : OnCtx
      (abstractForallContext
        (parameterDomains ++ fieldDomains ++ localDomains) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    rw [hcontext]
    exact (Hscope.scopeWF H.outVEnvWF).toCtx
  have HclosedTyping : H.outVEnv.HasType Us.length
      (abstractForallContext
        (parameterDomains ++ fieldDomains ++ localDomains) []).toCtx
      narrowMajor narrowExposed := by
    rw [hcontext]
    exact Htyping
  refine ⟨binding, evidence, scope, Hscope, parameterDomains,
    fieldDomains, localDomains, narrowIndices, narrowMajor, narrowExposed, ?_,
    hparameters, hfields, hlocal, HclosedLocalTemplate,
    HclosedLocalTemplateType, HclosedCtx, hlength, ?_, ?_, ?_,
    HclosedTyping, HindexEq, HmajorEq⟩
  · exact hall
  · exact HclosedIndices'
  · exact HclosedMajor'
  · exact HclosedExposed'

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
