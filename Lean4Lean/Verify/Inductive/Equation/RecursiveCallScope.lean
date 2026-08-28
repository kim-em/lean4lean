import Lean4Lean.Verify.Inductive.Equation.RecursiveCallFrame

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The motive application checked while producing this exact recursive
call, transported only across the final constant-environment extension.
Unlike the former reconstruction through the completed recursor context,
this certificate remains in the literal call-local context where it was
proved. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.producerMotiveApplication
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
    let sourceMajor := mkAppN A.rule.recursiveArgs[j]
      F.semantic.generated.localArgs
    ∃ target,
      TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx
        (Expr.app
          (mkAppN H.recInfos[selectedOwner]!.motive sourceIndices)
          sourceMajor) target ∧
      H.outVEnv.IsType Us.length
        F.semantic.current_context.mlctx.vlctx.toCtx target := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    F.semantic.generated.exposedType.getAppArgs[stats.params.size:]
  let sourceMajor := mkAppN A.rule.recursiveArgs[j]
    F.semantic.generated.localArgs
  rcases F.motiveApplication with ⟨M⟩
  have hselectedOwner : selectedOwner < H.recInfos.size := by
    simpa [selectedOwner, H.generated.length] using F.entry_lt
  have hsemantic : F.semantic.current_context.venv =
      R.declared.venvCtors :=
    F.semantic.recent.venv_eq.trans <|
      F.originRecent.venv_eq.trans <|
        A.semantics.context_venv.trans <|
          H.recursorEnv.trans R.declared.contextVEnv
  have Htr := M.translation
  have Htype := M.typing
  rw [hsemantic] at Htr Htype
  refine ⟨M.target, ?_, Htype.mono H.installed.le⟩
  simpa [selectedOwner, sourceIndices, sourceMajor,
    Array.getElem!_eq_getD, Array.getD, hselectedOwner] using
      Htr.mono H.installed.le

/-- Recover the selected mutual family's canonical motive telescope in the
exact recursive-call context.  Both the motive binding and telescope lookup
come from the first-pass producer certificate retained by the rule; the only
context transport follows the literal prior-hypothesis and call-local suffixes
recorded by the executable traversal. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.semanticMotiveTelescopeEvidence
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
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ binding : RecursorMotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence
        F.semantic.current_context stats H.recInfos[selectedOwner]!
        binding F.semantic.generated.exposedType F.semantic.exposedTarget) := by
  let selectedOwner := F.semantic.generated.ownerIdx
  have hrecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  let Hext : RecursorContextExtension A.semantics.context
      F.semantic.current_context :=
    F.originExtension.trans F.semantic.recent.contextExtension
  have HexposedType : F.semantic.current_context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.exposedTarget :=
    VEnv.IsType.defeqU_l F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm F.semantic.terminal_type
  exact F.motiveLookup.evidence selectedOwner hrecInfo
    F.semantic.current_context Hext F.semantic.exposed_translation
    HexposedType F.semantic.validated

/-- Replay the constructor fields once above the cached parameter scope.
This rule-wide frame is independent of any particular recursive call; later
call-local narrowing reuses its exact field/parameter identifier order. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.narrowFieldRuntimeScope
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
    let parameterDecls := A.semantics.parameterSuffix.parameterDecls
    ∃ fieldScope,
      ∃ HfieldScope : checkInductiveTypes.loopType.NarrowRuntimeScope
          A.semantics.fieldRootContext.venv Us fieldScope
            A.semantics.context.mlctx.vlctx,
        fieldScope.fvars =
            A.semantics.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        fieldScope.drop HfieldScope.frontSourceDomains.length =
            parameterDecls ∧
        ∃ fieldDomains,
          fieldDomains.length = A.rule.allArgs.size ∧
          HfieldScope.frontSourceDomains = fieldDomains := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls := A.semantics.parameterSuffix.parameterDecls
  let Hparameter := A.semantics.parameterSuffix.runtimeScope
  rcases A.semantics.context.onlyLams.lamPrefix
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le with
    ⟨_runtimeFieldDomains, HfieldPrefix⟩
  have hfieldRuntime :
      (A.semantics.context.mlctx.dropN A.rule.allArgs.size
        HfieldPrefix.le).vlctx =
        A.semantics.fieldRootContext.mlctx.vlctx := by
    have hle : HfieldPrefix.le = A.semantics.fieldsRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle, A.semantics.fieldsRecent.drop_eq]
  let HfieldBase := Hparameter.retargetRuntime hfieldRuntime.symm
  have HfieldWF : A.semantics.context.mlctx.WF
      A.semantics.fieldRootContext.venv Us := by
    simpa only [Us, A.semantics.fieldsRecent.venv_eq] using
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
    rw [hfieldRev, A.semantics.parameterSuffix.parameterDecls_fvars]
    simp [parameterDecls]
  rcases HfieldPrefix.extendNarrowRuntimeScope
      A.semantics.fieldRootContext.checking.tr.wf HfieldWF HfieldBase
        HfieldUp with
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

/-- Every field-or-parameter variable selected by a generated recursive
call belongs to the completed rule-semantic context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScopeInContext
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
    ∀ fv,
      (fv ∈ A.semantics.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params) →
      fv ∈ A.semantics.context.mlctx.vlctx.fvars := by
  intro fv hfv
  rw [A.semantics.fieldsRecent.contextFVars]
  rcases hfv with hfield | hparam
  · apply List.mem_append_left
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
      at hfield
    exact List.mem_reverse.mpr hfield
  · apply List.mem_append_right
    rw [A.semantics.parameterSuffix.context, VLCtx.fvars_append]
    apply List.mem_append_right
    rw [A.semantics.parameterSuffix.parameterDecls_fvars]
    exact List.mem_reverse.mpr hparam

/-- The field/parameter selection remains dependency-closed at the literal
producer origin after all earlier recursive hypotheses allocated before this
call.  This is precisely where the retained `originRecent` trace is used. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originRootUp
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
    IsFVarUpSet
      (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      F.originContext.mlctx.vlctx := by
  apply F.originRecent.upsetRoot F.rootScopeInContext
  simpa only [A.semantics.fieldOpening.fvars_eq_bound
    A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] using
      A.semantics.fieldParameterUp

/-- Source-aware narrowing at the actual producer origin.  Earlier recursive
hypotheses are present in the executable context but absent from the selected
scope, so they are skipped by `narrowFVars` rather than identified with the
completed rule root. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originNarrowScope
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.originContext.mlctx.vlctx,
        scope.fvars = F.originContext.mlctx.vlctx.fvars.filter
          (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let P := fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params
  rcases checkInductiveTypes.loopType.narrowFVars
      F.originContext.onlyLams F.originContext.checking.tr.wf
      F.originContext.mlctx_wf P F.originRootUp with
    ⟨scope, Hscope, hscope⟩
  have henv : F.originContext.venv ≤ H.outVEnv := by
    have horigin : F.originContext.venv = H.recursorWF.venv :=
      F.originRecent.venv_eq.trans A.semantics.context_venv
    rw [horigin, H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  exact ⟨scope, Hscope.mono henv, hscope⟩

/-- Filtering the literal producer origin by the recursive call's declared
field/parameter scope removes every earlier generated hypothesis and retains
exactly the completed rule context's corresponding selection.  This is the
identifier-level fact that the former replay-compatibility premise was
standing in for. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originRootFilter_eq_rule
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
    F.originContext.mlctx.vlctx.fvars.filter
        (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
          fv ∈ ExprArrayFVarIds stats.params) =
      A.semantics.context.mlctx.vlctx.fvars.filter
        (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
          fv ∈ ExprArrayFVarIds stats.params) := by
  let P := fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params
  rw [F.originRecent.contextFVars, List.filter_append]
  have hprior : F.originRecent.fvars.reverse.filter P = [] := by
    apply List.filter_eq_nil_iff.2
    intro fv hfv hp
    apply F.originRecent.fresh fv (List.mem_reverse.mp hfv)
    rw [← A.semantics.context.lctx_eq,
      A.semantics.context.mlctx_wf.tr.fvars_eq]
    exact F.rootScopeInContext fv (by simpa [P] using hp)
  rw [hprior, List.nil_append]

/-- Exact identifier order of the dependency-selected origin root.  Earlier
hypotheses are absent; constructor fields remain newest-first and cached
parameters remain as the base suffix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originNarrowScopeExact
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.originContext.mlctx.vlctx,
        scope.fvars = A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.originNarrowScope with ⟨scope, Hscope, hscope⟩
  refine ⟨scope, Hscope, ?_⟩
  rw [hscope, F.originRootFilter_eq_rule]
  let P := fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params
  have hfieldSelected :
      A.semantics.fieldsRecent.fvars.reverse.filter P =
        A.semantics.fieldsRecent.fvars.reverse := by
    apply List.filter_eq_self.2
    intro fv hfv
    have hopen : A.semantics.fieldOpening.fvars =
        A.semantics.fieldsRecent.fvars :=
      A.semantics.fieldOpening.fvars_eq_bound
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    exact by
      change decide (P fv) = true
      simp only [decide_eq_true_eq]
      exact Or.inl (by rw [hopen]; exact List.mem_reverse.mp hfv)
  have hparameterSelected :
      A.semantics.parameterSuffix.parameterDecls.fvars.filter P =
        A.semantics.parameterSuffix.parameterDecls.fvars := by
    apply List.filter_eq_self.2
    intro fv hfv
    change decide (P fv) = true
    simp only [decide_eq_true_eq]
    apply Or.inr
    rw [A.semantics.parameterSuffix.parameterDecls_fvars] at hfv
    exact List.mem_reverse.mp hfv
  have hrootNodup :
      (A.semantics.parameterSuffix.ambientDecls.fvars ++
        A.semantics.parameterSuffix.parameterDecls.fvars).Nodup := by
    rw [← VLCtx.fvars_append,
      ← A.semantics.parameterSuffix.context]
    exact A.semantics.fieldRootContext.mlctx_wf.tr.wf.fvars_nodup
  have hambientSelected :
      A.semantics.parameterSuffix.ambientDecls.fvars.filter P = [] := by
    apply List.filter_eq_nil_iff.2
    intro fv hambient hp
    change decide (P fv) = true at hp
    simp only [decide_eq_true_eq] at hp
    rcases hp with hfield | hparam
    · have hopen : A.semantics.fieldOpening.fvars =
          A.semantics.fieldsRecent.fvars :=
        A.semantics.fieldOpening.fvars_eq_bound
          A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      apply A.semantics.fieldsRecent.fresh fv (by rwa [← hopen])
      rw [← A.semantics.fieldRootContext.lctx_eq,
        A.semantics.fieldRootContext.mlctx_wf.tr.fvars_eq,
        A.semantics.parameterSuffix.context, VLCtx.fvars_append]
      exact List.mem_append_left _ hambient
    · have hparam' :
          fv ∈ A.semantics.parameterSuffix.parameterDecls.fvars := by
        rw [A.semantics.parameterSuffix.parameterDecls_fvars]
        exact List.mem_reverse.mpr hparam
      exact (List.nodup_append.mp hrootNodup).2.2
        fv hambient fv hparam' rfl
  rw [A.semantics.fieldsRecent.contextFVars,
    A.semantics.parameterSuffix.context, VLCtx.fvars_append,
    List.filter_append, List.filter_append, hfieldSelected,
    hambientSelected, hparameterSelected, List.nil_append]
  rw [A.parameterDecls_eq]

/-- Extend the dependency-selected origin scope by exactly the call-local
higher-order arguments.  The resulting semantic context contains locals,
fields, and parameters, while every earlier generated induction hypothesis
remains only on the executable side of the FVar lift. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.currentNarrowScope
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ rootScope,
      ∃ Hroot : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us rootScope F.originContext.mlctx.vlctx,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
        rootScope.fvars = A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars ∧
        scope.fvars = F.semantic.recent.fvars.reverse ++ rootScope.fvars ∧
        scope.drop F.semantic.generated.localArgs.size = rootScope ∧
        ∃ localDomains : List VExpr,
          localDomains.length = F.semantic.generated.localArgs.size ∧
          scope.toCtx = localDomains.reverse ++ rootScope.toCtx ∧
          Hscope.shift = Hroot.shift.consN
            F.semantic.generated.localArgs.size ∧
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
  let P := fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params
  rcases F.originNarrowScopeExact with ⟨rootScope, Hroot, hroot⟩
  rcases F.semantic.current_context.onlyLams.lamPrefix
      F.semantic.generated.localArgs.size F.semantic.recent.size_le with
    ⟨_runtimeDomains, HlocalPrefix⟩
  have hlocalRuntime :
      (F.semantic.current_context.mlctx.dropN
        F.semantic.generated.localArgs.size HlocalPrefix.le).vlctx =
          F.originContext.mlctx.vlctx := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle, F.semantic.recent.drop_eq]
  let HlocalBase := Hroot.retargetRuntime hlocalRuntime.symm
  have henv : F.semantic.current_context.venv ≤ H.outVEnv := by
    have hcurrent : F.semantic.current_context.venv = H.recursorWF.venv :=
      F.semantic.recent.venv_eq.trans <|
        F.originRecent.venv_eq.trans A.semantics.context_venv
    rw [hcurrent, H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have HlocalWF : F.semantic.current_context.mlctx.WF H.outVEnv Us :=
    F.semantic.current_context.mlctx_wf.mono henv
  have hlocalRev : F.semantic.current_context.mlctx.fvarRevList
      F.semantic.generated.localArgs.size HlocalPrefix.le =
        F.semantic.recent.fvars.reverse := by
    have hle : HlocalPrefix.le = F.semantic.recent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact F.semantic.recent.fvarRevList_eq
  have hPbase : ∀ fv, P fv ↔ fv ∈ rootScope.fvars := by
    intro fv
    have hopen : A.semantics.fieldOpening.fvars =
        A.semantics.fieldsRecent.fvars :=
      A.semantics.fieldOpening.fvars_eq_bound
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    rw [hroot, List.mem_append,
      H.parameterSuffix.parameterDecls_fvars]
    simp [P, hopen]
  have HlocalUp : IsFVarUpSet
      (fun fv => fv ∈ F.semantic.current_context.mlctx.fvarRevList
          F.semantic.generated.localArgs.size HlocalPrefix.le ++
            rootScope.fvars)
      F.semantic.current_context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HlocalWF.tr.wf.fvwf ?_).mp
      F.semantic.current_scope_up
    intro fv _
    rw [F.root_scope, hlocalRev]
    simp only [List.mem_append, List.mem_reverse]
    exact or_congr Iff.rfl (hPbase fv)
  rcases HlocalPrefix.extendFVarNarrowScope H.outVEnvWF HlocalWF
      HlocalBase HlocalUp with
    ⟨scope, Hscope, hscope, hdrop, localDomains, hlocalDomains,
      hcontext, hshift, _hexpanded, Hreplay⟩
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
  refine ⟨rootScope, Hroot, scope, Hscope, hroot, ?_, hdrop,
    localDomains, hlocalDomains, hcontext, ?_, ?_⟩
  · simpa [hlocalRev] using hscope
  · simpa [HlocalBase,
      checkInductiveTypes.loopType.FVarNarrowScope.retargetRuntime] using
      hshift
  · intro body target Hbody HbodyType
    rw [hsource]
    simpa [HlocalBase,
      checkInductiveTypes.loopType.FVarNarrowScope.retargetRuntime] using
      Hreplay Hbody HbodyType

/-- Restrict the exact recursive-index payload retained by successful
inductive-application validation to the producer-selected local/field/
parameter scope.  The resulting targets weaken back to the validation
targets through the exact `FVarNarrowScope` lift; no motive replay or
cross-run alpha premise is involved. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowValidatedIndices
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[
        stats.params.size:]).toList
    ∃ fullIndices : List VExpr,
      fullIndices.length = F.telescope.indices.length ∧
      List.Forall₂
        (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
        sourceIndices fullIndices ∧
      ∃ rootScope,
      ∃ Hroot : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us rootScope F.originContext.mlctx.vlctx,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
      ∃ (localDomains : List VExpr) (narrowIndices : List VExpr),
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
        List.Forall₂ (TrExprS H.outVEnv Us scope)
          sourceIndices narrowIndices ∧
        List.Forall₂
          (fun narrow full => H.outVEnv.IsDefEqU Us.length
            F.semantic.current_context.mlctx.vlctx.toCtx
            (narrow.lift' Hscope.shift) full)
          narrowIndices fullIndices := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  rcases F.semantic.validated.indices_payload with
    ⟨_levels, _params, fullIndices, _hspine, _hparams,
      hindicesLength, Hindices, _Hfamily⟩
  have hselectedOwner : F.semantic.generated.ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have htranslated :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hsourceArity := checkPositivityStep.getIIndices.index_arity
    F.semantic.generated.owner_valid
  have hrecArity :=
    H.arities F.semantic.generated.ownerIdx hselectedOwner
  have hlength : fullIndices.length = F.telescope.indices.length := by
    rw [F.telescope.indices_length, hrecArity]
    simpa [AddInductive.getIIndices] using
      htranslated.symm.trans hsourceArity
  have hsemantic : F.semantic.current_context.venv =
      R.declared.venvCtors :=
    F.semantic.recent.venv_eq.trans <|
      F.originExtension.venv_eq.trans <|
        A.semantics.context_venv.trans <|
          H.recursorEnv.trans R.declared.contextVEnv
  rw [hsemantic] at Hindices
  have HindicesFinal := Lean4Lean.List.Forall₂.imp
    (fun _ _ Hindex => Hindex.mono H.installed.le) Hindices
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
        rcases hfv with hlocal | hrootSelected
        · exact List.mem_append_left _ (List.mem_reverse.mpr hlocal)
        · rw [F.root_scope] at hrootSelected
          rcases hrootSelected with hfield | hparam
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
  rcases hnarrow HindicesFinal (List.Subset.refl sourceIndices) with
    ⟨narrowIndices, Hnarrow, Heq⟩
  exact ⟨fullIndices, hlength, HindicesFinal, rootScope, Hroot,
    scope, Hscope, localDomains, narrowIndices, hroot, hscope, hdrop,
    hlocal, hcontext, hshift, HlocalTemplate, HlocalTemplateType,
    Hnarrow, Heq⟩

/-- First-class native narrowing frame for one generated recursive call.
All fields are determined by source-aware narrowing at the exact producer
origin; in particular, no completed-loop replay or context equality is an
input. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NativeNarrowFrame
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
    (F : A.RecursiveCallRecursorFrame j hj) where
  rootScope : VLCtx
  root : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    rootScope F.originContext.mlctx.vlctx
  scope : VLCtx
  current : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    scope F.semantic.current_context.mlctx.vlctx
  root_fvars : rootScope.fvars =
    F.originContext.mlctx.vlctx.fvars.filter
      (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
  scope_fvars : scope.fvars =
    F.semantic.recent.fvars.reverse ++ rootScope.fvars
  scope_drop : scope.drop F.semantic.generated.localArgs.size = rootScope
  localDomains : List VExpr
  localDomains_length : localDomains.length =
    F.semantic.generated.localArgs.size
  scope_context : scope.toCtx = localDomains.reverse ++ rootScope.toCtx
  shift : current.shift = root.shift.consN
    F.semantic.generated.localArgs.size
  forallReplay : ∀ {body target},
    TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        scope body target →
    H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        scope.toCtx target →
    TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        rootScope
        (F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs body)
        (VExpr.wrapForalls localDomains target) ∧
      H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        rootScope.toCtx (VExpr.wrapForalls localDomains target)

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.nativeNarrowFrame
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
    Nonempty F.NativeNarrowFrame := by
  rcases F.currentNarrowScope with
    ⟨rootScope, Hroot, scope, Hscope, hroot, hscope, hdrop,
      localDomains, hlocal, hcontext, hshift, Hreplay⟩
  exact ⟨{
    rootScope := rootScope
    root := Hroot
    scope := scope
    current := Hscope
    root_fvars := hroot
    scope_fvars := hscope
    scope_drop := hdrop
    localDomains := localDomains
    localDomains_length := hlocal
    scope_context := hcontext
    shift := hshift
    forallReplay := Hreplay }⟩

/-- Closing the exact call-local telescope in the dependency-selected origin
scope and then abstracting all constructor fields leaves only cached
parameter variables.  Earlier induction hypotheses never enter the selected
scope. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.fieldAbstractedNeutralLocalForallSourceScopeAtOrigin
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
    ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
      A.rule.all_args_bound.fvars).FVarsIn
        (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases F.currentNarrowScope with
    ⟨rootScope, _Hroot, scope, _Hscope, hroot, _hscope, _hdrop,
      localDomains, _hlocal, _hcontext, _hshift, Hreplay⟩
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
          (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params) := by
    apply Hneutral.fvarsIn.mono
    intro fv hfv
    rw [hroot, List.mem_append,
      H.parameterSuffix.parameterDecls_fvars] at hfv
    have hopen : A.semantics.fieldOpening.fvars =
        A.semantics.fieldsRecent.fvars :=
      A.semantics.fieldOpening.fvars_eq_bound
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    rcases hfv with hfield | hparam
    · exact Or.inl (by rw [hopen]; simpa using hfield)
    · exact Or.inr (by simpa using hparam)
  apply FVarsIn.abstractList_of
  apply HneutralScope.mono
  intro fv hfv
  rcases hfv with hfield | hparam
  · left
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
      at hfield
    have hfvars : A.semantics.fieldsRecent.fvars =
        A.rule.all_args_bound.fvars :=
      BoundFVarArray.fvars_eq
        A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
        A.rule.all_args_bound rfl
    simpa [hfvars] using hfield
  · exact Or.inr hparam

end VerifyInductive

end Lean4Lean
