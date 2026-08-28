import Lean4Lean.Verify.Inductive.Equation.RecursiveCallFrame

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

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
        rootScope.fvars = F.originContext.mlctx.vlctx.fvars.filter
          (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params) ∧
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
  rcases F.originNarrowScope with ⟨rootScope, Hroot, hroot⟩
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
    rw [hroot, List.mem_filter]
    constructor
    · intro hp
      have hp' : fv ∈ A.semantics.fieldOpening.fvars ∨
          fv ∈ ExprArrayFVarIds stats.params := by
        simpa [P] using hp
      have horigin : fv ∈ F.originContext.mlctx.vlctx.fvars := by
        rw [F.originRecent.contextFVars]
        exact List.mem_append_right _ (F.rootScopeInContext fv hp')
      exact ⟨horigin, by simpa using hp'⟩
    · intro h
      simpa [P] using h.2
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
    rw [hroot, List.mem_filter] at hfv
    simpa using hfv.2
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
