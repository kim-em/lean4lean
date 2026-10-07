import Lean4Lean.Verify.Inductive.CompletedEquationRecursiveCallFrame
import Lean4Lean.Verify.Inductive.Equation.RecursiveCallScope

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The motive application checked while producing this exact recursive
call, transported across the final constant-environment extension. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.producerMotiveApplication
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
      R.context.venv :=
    F.semantic.recent.venv_eq.trans <|
      F.originRecent.venv_eq.trans <|
        A.semantics.context_venv.trans <|
          H.recursorEnv
  have Htr := M.translation
  have Htype := M.typing
  rw [hsemantic] at Htr Htype
  refine ⟨M.target, ?_, Htype.mono
    (H.installed.le)⟩
  simpa [selectedOwner, sourceIndices, sourceMajor,
    Array.getElem!_eq_getD, Array.getD, hselectedOwner] using
      Htr.mono (H.installed.le)

/-- Recover the selected mutual family's canonical motive telescope in the
exact recursive-call context.  Both the motive binding and telescope lookup
come from the first-pass producer certificate retained by the rule; the only
context transport follows the literal prior-hypothesis and call-local suffixes
recorded by the executable traversal. -/
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
    let parameterDecls := A.semantics.parameterSuffix.parameterDecls
    ∃ fieldScope,
      ∃ HfieldScope : checkInductiveTypes.loopType.NarrowRuntimeScope
          A.semantics.fieldRootContext.venv Us fieldScope
            A.semantics.context.mlctx.vlctx,
        fieldScope.fvars =
            A.semantics.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        fieldScope.drop HfieldScope.frontSourceDomains.length =
            parameterDecls ∧
        (∃ fieldDomains,
          fieldDomains.length = A.rule.allArgs.size ∧
          HfieldScope.frontSourceDomains = fieldDomains) ∧
        (0 < A.rule.allArgs.size →
          VLCtx.IsDefEq A.semantics.fieldRootContext.venv Us.length
            fieldScope A.semantics.context.chk.vlctx) := by
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
  obtain ⟨M, hMwf, hchkM, hnM, hagree, hdrop, -⟩ := A.semantics.fieldCheck
  have hMwf' : M.WF A.semantics.fieldRootContext.venv Us := by
    simpa only [Us, A.semantics.fieldsRecent.venv_eq] using hMwf
  have hbaseAlign : VLCtx.IsDefEq A.semantics.fieldRootContext.venv Us.length
      parameterDecls (M.dropN A.rule.allArgs.size hnM).vlctx := by
    rw [hdrop]
    exact .refl A.semantics.fieldRootContext.checking.tr.wf HfieldBase.wf
  rcases HfieldPrefix.extendNarrowRuntimeScopeAligned
      A.semantics.fieldRootContext.checking.tr.wf HfieldWF HfieldBase
        HfieldUp hMwf' hnM hagree hbaseAlign with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      ⟨fieldDomains, hfieldDomains, hfieldFront⟩, halign⟩
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
    hfieldScopeFVars, hbase, ⟨fieldDomains, hfieldDomains, hfront⟩,
    fun hpos => by rw [hchkM hpos]; exact halign⟩

/-- Every field-or-parameter variable selected by a generated recursive
call belongs to the completed rule-semantic context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rootScopeInContext
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
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originRootUp
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
    IsFVarUpSet
      (fun fv => fv ∈ A.semantics.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      F.originContext.mlctx.vlctx := by
  apply F.originRecent.upsetRoot F.rootScopeInContext
  simpa only [A.semantics.fieldOpening.fvars_eq_bound
    A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] using
      A.semantics.fieldParameterUp

/-- Filtering the literal producer origin by the recursive call's declared
field/parameter scope removes every earlier generated hypothesis and retains
exactly the completed rule context's corresponding selection. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originRootFilter_eq_rule
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

end VerifyInductive

end Lean4Lean
