import Lean4Lean.Verify.Inductive.Equation.RecursiveCall

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem forall₂_trExprS_defeq
    (Henv : VEnv.WF env) (Hscope : VLCtx.WF env Us.length scope)
    (Hleft : List.Forall₂ (TrExprS env Us scope) sources left)
    (Hright : List.Forall₂ (TrExprS env Us scope) sources right) :
    List.Forall₂
      (fun leftTarget rightTarget =>
        env.IsDefEqU Us.length scope.toCtx leftTarget rightTarget)
      left right := by
  induction Hleft generalizing right with
  | nil =>
      cases Hright
      exact .nil
  | @cons source leftTarget sources leftTargets Hsource Hsources ih =>
      cases Hright with
      | cons HsourceRight HsourcesRight =>
        exact .cons
          (Hsource.uniq Henv (.refl Henv Hscope) HsourceRight)
          (ih HsourcesRight)

/-- Every prefix of a producer-selected scope consists only of lambda
declarations.  This is read directly from the narrowing certificate, rather
than from any contiguity claim about the executable context. -/
private theorem selectedLams_toCtx_take_length
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) fvars scope)
    (n : Nat) :
    (VLCtx.toCtx (scope.take n)).length = (scope.take n).length := by
  induction H generalizing n with
  | nil => simp [VLCtx.toCtx]
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.take_succ_cons, VLCtx.toCtx, List.length_cons]
      exact congrArg Nat.succ (ih n)

private theorem forall₂_takeBoth
    {R : α → β → Prop} (H : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction n generalizing xs ys with
  | zero => exact .nil
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons h Htail => exact .cons h (ih Htail)

private theorem forall₂_dropBoth
    {R : α → β → Prop} (H : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact H
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons _ Htail => exact ih Htail

private theorem selectedLams_fvars
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type)) fvars scope) :
    VLCtx.fvars scope = fvars := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simp only [VLCtx.fvars_cons_some, List.cons.injEq]
    exact ⟨trivial, ih⟩

private theorem selectedLams_fvars_take
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type)) fvars scope)
    (n : Nat) :
    VLCtx.fvars (scope.take n) = fvars.take n :=
  selectedLams_fvars (forall₂_takeBoth H n)

private theorem selectedLams_fvars_drop
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type)) fvars scope)
    (n : Nat) :
    VLCtx.fvars (scope.drop n) = fvars.drop n :=
  selectedLams_fvars (forall₂_dropBoth H n)

private theorem selectedLams_toCtx_take
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type)) fvars scope)
    (n : Nat) :
    VLCtx.toCtx (scope.take n) = (VLCtx.toCtx scope).take n := by
  induction H generalizing n with
  | nil => simp [VLCtx.toCtx]
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    cases n <;> simp [VLCtx.toCtx, ih]

/-- Close a selected declaration prefix outside an existing anonymous
telescope.  This is the staged form needed to close call locals before
constructor fields without ever making the selected scope contiguous in the
executable context. -/
private theorem fvarNarrow_abstractPrefixUnder
    (H : checkInductiveTypes.loopType.FVarNarrowScope
      env Us scope runtime)
    (henv : env.WF) (domains : List VExpr) (n : Nat)
    (hbase : scope.drop n = baseScope)
    (Htr : TrExprS env Us
      (abstractForallContext domains scope) source target) :
    TrExprS env Us
      (abstractForallContext
        ((VLCtx.toCtx (scope.take n)).reverse ++ domains) baseScope)
      (source.abstractList (scope.fvars.take n).reverse domains.length)
      target := by
  let scopePrefix := scope.take n
  let tail := scope.drop n
  have hscope : scopePrefix ++ tail = scope := by
    simpa [scopePrefix, tail] using (List.take_append_drop n scope).symm
  have Hprefix := forall₂_takeBoth H.declarations n
  have hprefixFVars : VLCtx.fvars scopePrefix = scope.fvars.take n :=
    selectedLams_fvars Hprefix
  have Htr' : TrExprS env Us
      (abstractForallContext domains (scopePrefix ++ tail)) source target := by
    simpa [hscope] using Htr
  have hnodup : (scope.fvars.take n).Nodup :=
    (H.scopeWF henv).fvars_nodup.sublist
      (List.take_sublist n scope.fvars)
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    Hprefix hnodup Htr'
  simpa [scopePrefix, tail, hprefixFVars, hbase] using Habstract

/-- Producer-origin semantic frame for the index spine of one generated
recursive call.  The executable context may contain earlier induction
hypotheses, so the retained semantic scope is deliberately an
`FVarNarrowScope`, not a contiguous runtime prefix. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame
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
  binding : RecursorMotiveBinding F.semantic.current_context
    H.recInfos[F.semantic.generated.ownerIdx]! H.elimLevel
  evidence : RecursorMotiveTelescopeEvidence F.semantic.current_context stats
    H.recInfos[F.semantic.generated.ownerIdx]! binding
    F.semantic.generated.exposedType F.semantic.exposedTarget
  rootScope : VLCtx
  rootNarrow : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) rootScope
    F.originContext.mlctx.vlctx
  scope : VLCtx
  narrow : checkInductiveTypes.loopType.FVarNarrowScope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope
    F.semantic.current_context.mlctx.vlctx
  localDomains : List VExpr
  narrowIndices : List VExpr
  narrowMajor : VExpr
  narrowExposed : VExpr
  root_fvars : rootScope.fvars =
    A.semantics.fieldsRecent.fvars.reverse ++
      H.parameterSuffix.parameterDecls.fvars
  scope_fvars : scope.fvars =
    F.semantic.recent.fvars.reverse ++ rootScope.fvars
  drop_locals : scope.drop F.semantic.generated.localArgs.size = rootScope
  local_length : localDomains.length = F.semantic.generated.localArgs.size
  scope_context : scope.toCtx = localDomains.reverse ++ rootScope.toCtx
  shift : narrow.shift = rootNarrow.shift.consN
    F.semantic.generated.localArgs.size
  local_template_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) rootScope
    (F.semantic.generated.current.lctx.mkForall
      F.semantic.generated.localArgs (.sort .zero))
    (VExpr.wrapForalls localDomains (.sort .zero))
  local_template_type : H.outVEnv.IsType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    rootScope.toCtx (VExpr.wrapForalls localDomains (.sort .zero))
  indices_length : evidence.indices.length = F.telescope.indices.length
  indices_translation : List.Forall₂
    (TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope)
    (F.semantic.generated.exposedType.getAppArgs[
      stats.params.size:]).toList narrowIndices
  indices_defeq : List.Forall₂
    (fun narrowIndex fullIndex => H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      F.semantic.current_context.mlctx.vlctx.toCtx
      (narrowIndex.lift' narrow.shift) fullIndex)
    narrowIndices evidence.indices
  major_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope
    (mkAppN A.rule.recursiveArgs[j] F.semantic.generated.localArgs)
    narrowMajor
  major_local_abstract :
    (mkAppN A.rule.recursiveArgs[j]
      F.semantic.generated.localArgs).abstractList
        F.semantic.generated.arguments_bound.fvars =
      F.semantic.generated.abstractedMajor
  exposed_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) scope
    F.semantic.generated.exposedType narrowExposed
  major_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length scope.toCtx
    narrowMajor narrowExposed
  major_defeq : H.outVEnv.IsDefEqU
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    F.semantic.current_context.mlctx.vlctx.toCtx
    F.semantic.appliedFieldTarget (narrowMajor.lift' narrow.shift)

/-- Assemble the non-contiguous index frame entirely from successful first-
and second-pass producer certificates. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.narrowIndexFrame
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
    (F : A.RecursiveCallRecursorFrame j hj) : Nonempty F.NarrowIndexFrame := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  rcases F.semanticMotiveTelescopeEvidence with ⟨binding, ⟨evidence⟩⟩
  rcases F.narrowValidatedIndices with
    ⟨fullIndices, hfullLength, Hfull, rootScope, Hroot, scope, Hscope,
      localDomains, narrowIndices, hrootFVars, hscopeFVars, hdrop,
      hlocal, hcontext, hshift, HlocalTemplate, HlocalTemplateType,
      Hnarrow, HnarrowFull⟩
  have hscopeExact : scope.fvars =
      F.semantic.recent.fvars.reverse ++
        A.semantics.fieldsRecent.fvars.reverse ++
          H.parameterSuffix.parameterDecls.fvars := by
    rw [hscopeFVars, hrootFVars]
    simp only [List.append_assoc]
  rcases F.narrowSemanticAppliedMajor scope Hscope hscopeExact with
    ⟨narrowMajor, HnarrowMajor, HmajorEq⟩
  rcases F.narrowSemanticAppliedMajorTypingFor scope Hscope hscopeExact
      HnarrowMajor with
    ⟨narrowExposed, HnarrowExposed, HnarrowTyping⟩
  have hcurrentBase : F.semantic.current_context.venv ≤ H.outVEnv := by
    rw [F.semantic.recent.venv_eq, F.originExtension.venv_eq,
      A.semantics.context_venv, H.recursorEnv,
      R.declared.contextVEnv]
    exact H.installed.le
  have HcurrentWF : VLCtx.WF H.outVEnv Us.length
      F.semantic.current_context.mlctx.vlctx :=
    (F.semantic.current_context.mlctx_wf.mono hcurrentBase).tr.wf
  have HevidenceFinal : List.Forall₂
      (TrExprS H.outVEnv Us F.semantic.current_context.mlctx.vlctx)
      sourceIndices evidence.indices :=
    Lean4Lean.List.Forall₂.imp
      (fun _ _ Hindex => Hindex.mono hcurrentBase)
      evidence.indices_translation
  have HfullEvidence : List.Forall₂
      (fun fullIndex evidenceIndex => H.outVEnv.IsDefEqU Us.length
        F.semantic.current_context.mlctx.vlctx.toCtx
        fullIndex evidenceIndex)
      fullIndices evidence.indices := by
    exact forall₂_trExprS_defeq H.outVEnvWF HcurrentWF Hfull
      HevidenceFinal
  have HnarrowEvidence : List.Forall₂
      (fun narrowIndex evidenceIndex => H.outVEnv.IsDefEqU Us.length
        F.semantic.current_context.mlctx.vlctx.toCtx
        (narrowIndex.lift' Hscope.shift) evidenceIndex)
      narrowIndices evidence.indices := by
    exact Lean4Lean.List.Forall₂.trans
      (fun _ _ _ Hleft Hright =>
        Hleft.trans H.outVEnvWF HcurrentWF.toCtx Hright)
      HnarrowFull HfullEvidence
  have hevidenceLength : evidence.indices.length =
      F.telescope.indices.length := by
    have hpair := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      HfullEvidence
    exact hpair.symm.trans hfullLength
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
  have hmajorLocal :
      (mkAppN A.rule.recursiveArgs[j]
        F.semantic.generated.localArgs).abstractList
          F.semantic.generated.arguments_bound.fvars =
        F.semantic.generated.abstractedMajor := by
    have hfieldClosed : A.rule.recursiveArgs[j].looseBVarRange' = 0 := by
      have hclosed := F.semantic.field_translation.closed
      rw [F.originContext.mlctx.noBV] at hclosed
      exact hclosed.looseBVarRange_zero
    calc
      (mkAppN A.rule.recursiveArgs[j]
        F.semantic.generated.localArgs).abstractList
          F.semantic.generated.arguments_bound.fvars =
          mkAppN
            (A.rule.recursiveArgs[j].abstractList
              F.semantic.generated.arguments_bound.fvars)
            (List.ofFn (fun index :
              Fin F.semantic.generated.arguments_bound.fvars.length =>
                Expr.bvar
                  (F.semantic.generated.arguments_bound.fvars.length - 1 -
                    index))).toArray := by
        rw [Expr.abstractList_mkAppN, hlocalAbstract]
      _ = F.semantic.generated.abstractedMajor :=
        (F.semantic.generated.abstractedMajor_eq_of_closed
          hfieldClosed).symm
  exact ⟨{
    binding := binding
    evidence := evidence
    rootScope := rootScope
    rootNarrow := Hroot
    scope := scope
    narrow := Hscope
    localDomains := localDomains
    narrowIndices := narrowIndices
    narrowMajor := narrowMajor
    narrowExposed := narrowExposed
    root_fvars := hrootFVars
    scope_fvars := hscopeFVars
    drop_locals := hdrop
    local_length := hlocal
    scope_context := hcontext
    shift := hshift
    local_template_translation := HlocalTemplate
    local_template_type := HlocalTemplateType
    indices_length := hevidenceLength
    indices_translation := Hnarrow
    indices_defeq := HnarrowEvidence
    major_translation := HnarrowMajor
    major_local_abstract := hmajorLocal
    exposed_translation := HnarrowExposed
    major_typing := HnarrowTyping
    major_defeq := HmajorEq }⟩

/-- The semantic call frame after closing call-local binders and then
constructor fields.  The remaining named scope contains only the producer-
selected parameters; earlier generated hypotheses were never selected. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.StagedFront
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
    {F : A.RecursiveCallRecursorFrame j hj}
    (N : F.NarrowIndexFrame) where
  parameterScope : VLCtx
  fieldDomains : List VExpr
  drop_fields : N.rootScope.drop A.rule.allArgs.size = parameterScope
  field_length : fieldDomains.length = A.rule.allArgs.size
  parameter_fvars : parameterScope.fvars =
    A.rule.params_bound.fvars.reverse
  field_context :
    (abstractForallContext fieldDomains parameterScope).toCtx =
      N.rootScope.toCtx
  full_context :
    (abstractForallContext (fieldDomains ++ N.localDomains)
      parameterScope).toCtx = N.scope.toCtx
  context_wf : OnCtx
    (abstractForallContext (fieldDomains ++ N.localDomains)
      parameterScope).toCtx
    (H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)
  indices_translation : List.Forall₂
    (TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (fieldDomains ++ N.localDomains)
        parameterScope))
    ((F.semantic.generated.exposedType.getAppArgs[
      stats.params.size:]).toList.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size)
    N.narrowIndices
  major_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext (fieldDomains ++ N.localDomains)
      parameterScope)
    (F.semantic.generated.outerAbstractedMajor
      A.rule.all_args_bound.fvars) N.narrowMajor
  exposed_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext (fieldDomains ++ N.localDomains)
      parameterScope)
    ((F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size) N.narrowExposed
  major_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext (fieldDomains ++ N.localDomains)
      parameterScope).toCtx N.narrowMajor N.narrowExposed
  local_template_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext fieldDomains parameterScope)
    ((F.semantic.generated.current.lctx.mkForall
      F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars)
    (VExpr.wrapForalls N.localDomains (.sort .zero))
  local_template_type : H.outVEnv.IsType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext fieldDomains parameterScope).toCtx
    (VExpr.wrapForalls N.localDomains (.sort .zero))

/-- Build the staged local/field closure from the exact selected producer
scope. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.stageFront
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
    {F : A.RecursiveCallRecursorFrame j hj}
    (N : F.NarrowIndexFrame) : Nonempty N.StagedFront := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let localCount := F.semantic.generated.localArgs.size
  let fieldCount := A.rule.allArgs.size
  let parameterScope := N.rootScope.drop fieldCount
  let fieldDomains := (VLCtx.toCtx (N.rootScope.take fieldCount)).reverse
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
  have hlocalLength : F.semantic.generated.arguments_bound.fvars.length =
      localCount := by
    simpa [localCount] using
      F.semantic.generated.arguments_bound.length_fvars
  have hfieldLength : A.rule.all_args_bound.fvars.length = fieldCount := by
    simpa [fieldCount] using A.rule.all_args_bound.length_fvars
  have hlocalPrefixFVars :
      (N.scope.fvars.take localCount).reverse =
        F.semantic.generated.arguments_bound.fvars := by
    rw [N.scope_fvars, hlocalFVars]
    rw [show localCount =
      F.semantic.generated.arguments_bound.fvars.length by
        exact hlocalLength.symm]
    simp
  have hfieldPrefixFVars :
      (N.rootScope.fvars.take fieldCount).reverse =
        A.rule.all_args_bound.fvars := by
    rw [N.root_fvars, hfieldFVars]
    rw [show fieldCount = A.rule.all_args_bound.fvars.length by
      exact hfieldLength.symm]
    simp
  have hlocalDomains :
      (VLCtx.toCtx (N.scope.take localCount)).reverse =
        N.localDomains := by
    have htake := selectedLams_toCtx_take N.narrow.declarations localCount
    rw [N.scope_context] at htake
    have hprefix :
        (N.localDomains.reverse ++ N.rootScope.toCtx).take localCount =
          N.localDomains.reverse := by
      rw [show localCount = N.localDomains.length by
        simpa [localCount] using N.local_length.symm]
      simp
    rw [hprefix] at htake
    simpa using congrArg List.reverse htake
  have hfieldDomains : fieldDomains.length = fieldCount := by
    dsimp only [fieldDomains]
    rw [List.length_reverse,
      selectedLams_toCtx_take_length N.rootNarrow.declarations,
      List.length_take]
    have hle : fieldCount ≤ N.rootScope.length := by
      rw [← N.rootNarrow.fvars_length, N.root_fvars, hfieldFVars]
      simp only [List.length_append, List.length_reverse]
      omega
    rw [Nat.min_eq_left hle]
  have hparameterFVars : VLCtx.fvars parameterScope =
      A.rule.params_bound.fvars.reverse := by
    dsimp only [parameterScope]
    rw [selectedLams_fvars_drop N.rootNarrow.declarations,
      N.root_fvars, hfieldFVars]
    rw [show fieldCount = A.rule.all_args_bound.fvars.reverse.length by
      simp [fieldCount, hfieldLength]]
    simp [H.parameterSuffix.parameterDecls_fvars,
      A.rule.params_bound.exprArrayFVarIds]
  have hfieldContext :
      (abstractForallContext fieldDomains parameterScope).toCtx =
        N.rootScope.toCtx := by
    rw [abstractForallContext_toCtx]
    dsimp only [fieldDomains, parameterScope]
    rw [List.reverse_reverse, ← VLCtx.toCtx_append]
    exact congrArg VLCtx.toCtx
      (List.take_append_drop fieldCount N.rootScope)
  have hfullContext :
      (abstractForallContext (fieldDomains ++ N.localDomains)
        parameterScope).toCtx = N.scope.toCtx := by
    rw [abstractForallContext_toCtx, List.reverse_append,
      N.scope_context]
    have hfieldContext' :
        fieldDomains.reverse ++ VLCtx.toCtx parameterScope =
          N.rootScope.toCtx := by
      simpa [abstractForallContext_toCtx] using hfieldContext
    rw [List.append_assoc, hfieldContext']
  have hrootBase : N.rootScope.drop fieldCount = parameterScope := rfl
  have closeLocal : ∀ {source target},
      TrExprS H.outVEnv Us N.scope source target →
      TrExprS H.outVEnv Us
        (abstractForallContext N.localDomains N.rootScope)
        (source.abstractList
          F.semantic.generated.arguments_bound.fvars) target := by
    intro source target Hsource
    have Hclosed := N.narrow.abstractPrefix H.outVEnvWF localCount
      N.drop_locals Hsource
    rw [hlocalPrefixFVars, hlocalDomains] at Hclosed
    exact Hclosed
  have closeFields : ∀ {source target},
      TrExprS H.outVEnv Us
        (abstractForallContext N.localDomains N.rootScope) source target →
      TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ N.localDomains)
          parameterScope)
        (source.abstractList A.rule.all_args_bound.fvars
          N.localDomains.length) target := by
    intro source target Hsource
    have Hclosed := fvarNarrow_abstractPrefixUnder N.rootNarrow
      H.outVEnvWF N.localDomains fieldCount hrootBase Hsource
    rw [hfieldPrefixFVars] at Hclosed
    simpa [fieldDomains] using Hclosed
  have closeSources : ∀ {sources targets},
      List.Forall₂ (TrExprS H.outVEnv Us N.scope) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ N.localDomains)
            parameterScope))
        (sources.map fun source =>
          (source.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.all_args_bound.fvars
              F.semantic.generated.localArgs.size)
        targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | @cons source target sources targets Hsource _ ih =>
      have Hclosed := closeFields (closeLocal Hsource)
      rw [N.local_length] at Hclosed
      exact .cons Hclosed ih
  have Hindices := closeSources N.indices_translation
  have Hmajor := closeFields (closeLocal N.major_translation)
  have Hexposed := closeFields (closeLocal N.exposed_translation)
  rw [N.local_length] at Hmajor Hexposed
  rw [N.major_local_abstract] at Hmajor
  have HlocalTemplate := fvarNarrow_abstractPrefixUnder N.rootNarrow
    H.outVEnvWF [] fieldCount hrootBase N.local_template_translation
  rw [hfieldPrefixFVars] at HlocalTemplate
  have HlocalTemplate' : TrExprS H.outVEnv Us
      (abstractForallContext fieldDomains parameterScope)
      ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars)
      (VExpr.wrapForalls N.localDomains (.sort .zero)) := by
    simpa [fieldDomains] using HlocalTemplate
  have HcontextWF : OnCtx
      (abstractForallContext (fieldDomains ++ N.localDomains)
        parameterScope).toCtx (H.outVEnv.IsType Us.length) := by
    rw [hfullContext]
    exact (N.narrow.scopeWF H.outVEnvWF).toCtx
  have Htyping : H.outVEnv.HasType Us.length
      (abstractForallContext (fieldDomains ++ N.localDomains)
        parameterScope).toCtx N.narrowMajor N.narrowExposed := by
    rw [hfullContext]
    exact N.major_typing
  have HlocalType : H.outVEnv.IsType Us.length
      (abstractForallContext fieldDomains parameterScope).toCtx
      (VExpr.wrapForalls N.localDomains (.sort .zero)) := by
    rw [hfieldContext]
    exact N.local_template_type
  exact ⟨{
    parameterScope := parameterScope
    fieldDomains := fieldDomains
    drop_fields := rfl
    field_length := hfieldDomains
    parameter_fvars := hparameterFVars
    field_context := hfieldContext
    full_context := hfullContext
    context_wf := HcontextWF
    indices_translation := Hindices
    major_translation := by
      simpa [BoundGeneratedRecursiveCall.outerAbstractedMajor] using Hmajor
    exposed_translation := Hexposed
    major_typing := Htyping
    local_template_translation := HlocalTemplate'
    local_template_type := HlocalType }⟩

/-- The producer-selected parameter scope closed outside the staged field and
local telescope.  Its target domains need not be syntactically identical to
an independently translated parameter cache; the subsequent canonical-
prefix proof relates them by definitional equality. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.StagedFront.ParameterClosed
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
    {F : A.RecursiveCallRecursorFrame j hj}
    {N : F.NarrowIndexFrame} (S : N.StagedFront) where
  parameterDomains : List VExpr
  parameter_domains : parameterDomains = S.parameterScope.toCtx.reverse
  context_wf : OnCtx
    (abstractForallContext
      (parameterDomains ++ S.fieldDomains ++ N.localDomains) []).toCtx
    (H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)
  indices_translation : List.Forall₂
    (TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (parameterDomains ++ S.fieldDomains ++ N.localDomains) []))
    ((F.semantic.generated.exposedType.getAppArgs[
      stats.params.size:]).toList.map fun index =>
        ((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars
              (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
    N.narrowIndices
  major_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (parameterDomains ++ S.fieldDomains ++ N.localDomains) [])
    ((F.semantic.generated.outerAbstractedMajor
      A.rule.all_args_bound.fvars).abstractList
        A.rule.params_bound.fvars
        (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
    N.narrowMajor
  exposed_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (parameterDomains ++ S.fieldDomains ++ N.localDomains) [])
    (((F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size).abstractList
          A.rule.params_bound.fvars
          (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
    N.narrowExposed
  major_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext
      (parameterDomains ++ S.fieldDomains ++ N.localDomains) []).toCtx
    N.narrowMajor N.narrowExposed
  local_template_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext (parameterDomains ++ S.fieldDomains) [])
    (((F.semantic.generated.current.lctx.mkForall
      F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size)
    (VExpr.wrapForalls N.localDomains (.sort .zero))
  local_template_type : H.outVEnv.IsType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext (parameterDomains ++ S.fieldDomains) []).toCtx
    (VExpr.wrapForalls N.localDomains (.sort .zero))

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.StagedFront.closeParameters
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
    {F : A.RecursiveCallRecursorFrame j hj}
    {N : F.NarrowIndexFrame} (S : N.StagedFront) :
    Nonempty S.ParameterClosed := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDomains := S.parameterScope.toCtx.reverse
  have HparameterDeclsRaw := forall₂_dropBoth N.rootNarrow.declarations
    A.rule.allArgs.size
  have hparameterNames :
      N.rootScope.fvars.drop A.rule.allArgs.size =
        A.rule.params_bound.fvars.reverse := by
    calc
      N.rootScope.fvars.drop A.rule.allArgs.size =
          VLCtx.fvars (N.rootScope.drop A.rule.allArgs.size) :=
        (selectedLams_fvars HparameterDeclsRaw).symm
      _ = VLCtx.fvars S.parameterScope :=
        congrArg VLCtx.fvars S.drop_fields
      _ = A.rule.params_bound.fvars.reverse := S.parameter_fvars
  have HparameterDecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type))
      A.rule.params_bound.fvars.reverse S.parameterScope := by
    rw [← S.drop_fields, ← hparameterNames]
    exact HparameterDeclsRaw
  have hparamsNodup : A.rule.params_bound.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr <|
      (List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have closeParameter : ∀ {domains source target},
      TrExprS H.outVEnv Us
        (abstractForallContext domains S.parameterScope) source target →
      TrExprS H.outVEnv Us
        (abstractForallContext (parameterDomains ++ domains) [])
        (source.abstractList A.rule.params_bound.fvars domains.length)
        target := by
    intro domains source target Hsource
    have Hclosed := TrExprS.abstractFVarLambdaSuffix
      HparameterDecls hparamsNodup Hsource
    simpa [parameterDomains] using Hclosed
  have closeSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (S.fieldDomains ++ N.localDomains)
            S.parameterScope)) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDomains ++ S.fieldDomains ++ N.localDomains) []))
        (sources.map fun source => source.abstractList
          A.rule.params_bound.fvars
          (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
        targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | @cons source target sources targets Hsource _ ih =>
      have Hclosed := closeParameter Hsource
      have hfrontLength : (S.fieldDomains ++ N.localDomains).length =
          F.semantic.generated.localArgs.size + A.rule.allArgs.size := by
        simp [S.field_length, N.local_length, Nat.add_comm]
      rw [hfrontLength] at Hclosed
      have Hclosed' : TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDomains ++ S.fieldDomains ++ N.localDomains) [])
          (source.abstractList A.rule.params_bound.fvars
            (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
          target := by
        simpa [List.append_assoc] using Hclosed
      exact List.Forall₂.cons Hclosed' ih
  have Hindices₀ := closeSources S.indices_translation
  have Hindices : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDomains ++ S.fieldDomains ++ N.localDomains) []))
      ((F.semantic.generated.exposedType.getAppArgs[
        stats.params.size:]).toList.map fun index =>
          ((index.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.all_args_bound.fvars
              F.semantic.generated.localArgs.size).abstractList
                A.rule.params_bound.fvars
                (F.semantic.generated.localArgs.size + A.rule.allArgs.size))
      N.narrowIndices := by
    simpa [List.map_map, Function.comp_def] using Hindices₀
  have Hmajor := closeParameter S.major_translation
  have Hexposed := closeParameter S.exposed_translation
  have hfrontLength : (S.fieldDomains ++ N.localDomains).length =
      F.semantic.generated.localArgs.size + A.rule.allArgs.size := by
    simp [S.field_length, N.local_length, Nat.add_comm]
  rw [hfrontLength] at Hmajor Hexposed
  have HlocalTemplate := closeParameter S.local_template_translation
  rw [S.field_length] at HlocalTemplate
  have hfullContext :
      (abstractForallContext
        (parameterDomains ++ S.fieldDomains ++ N.localDomains) []).toCtx =
      (abstractForallContext (S.fieldDomains ++ N.localDomains)
        S.parameterScope).toCtx := by
    simp [parameterDomains, abstractForallContext_toCtx,
      List.reverse_append, List.append_assoc, VLCtx.toCtx]
  have hfieldContext :
      (abstractForallContext (parameterDomains ++ S.fieldDomains) []).toCtx =
      (abstractForallContext S.fieldDomains S.parameterScope).toCtx := by
    simp [parameterDomains, abstractForallContext_toCtx,
      List.reverse_append, List.append_assoc, VLCtx.toCtx]
  have HcontextWF : OnCtx
      (abstractForallContext
        (parameterDomains ++ S.fieldDomains ++ N.localDomains) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    rw [hfullContext]
    exact S.context_wf
  have Htyping : H.outVEnv.HasType Us.length
      (abstractForallContext
        (parameterDomains ++ S.fieldDomains ++ N.localDomains) []).toCtx
      N.narrowMajor N.narrowExposed := by
    rw [hfullContext]
    exact S.major_typing
  have HlocalType : H.outVEnv.IsType Us.length
      (abstractForallContext (parameterDomains ++ S.fieldDomains) []).toCtx
      (VExpr.wrapForalls N.localDomains (.sort .zero)) := by
    rw [hfieldContext]
    exact S.local_template_type
  exact ⟨{
    parameterDomains := parameterDomains
    parameter_domains := rfl
    context_wf := HcontextWF
    indices_translation := Hindices
    major_translation := by simpa [List.append_assoc] using Hmajor
    exposed_translation := by simpa [List.append_assoc] using Hexposed
    major_typing := Htyping
    local_template_translation := HlocalTemplate
    local_template_type := HlocalType }⟩

/-- Close exactly the selected call-local and constructor-field prefix of a
non-contiguous index frame.  The older suffix is the producer-selected
parameter scope; skipped earlier hypotheses never become equation binders. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.ClosedFront
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
    {F : A.RecursiveCallRecursorFrame j hj}
    (N : F.NarrowIndexFrame) where
  parameterScope : VLCtx
  frontDomains : List VExpr
  drop_front : N.scope.drop
    (A.rule.allArgs.size + F.semantic.generated.localArgs.size) = parameterScope
  front_length : frontDomains.length =
    A.rule.allArgs.size + F.semantic.generated.localArgs.size
  front_fvars :
    (N.scope.fvars.take
      (A.rule.allArgs.size + F.semantic.generated.localArgs.size)).reverse =
      A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars
  context_eq :
    (abstractForallContext frontDomains parameterScope).toCtx = N.scope.toCtx
  indices_translation : List.Forall₂
    (TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext frontDomains parameterScope))
    ((F.semantic.generated.exposedType.getAppArgs[
      stats.params.size:]).toList.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size)
    N.narrowIndices
  major_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext frontDomains parameterScope)
    (F.semantic.generated.outerAbstractedMajor
      A.rule.all_args_bound.fvars) N.narrowMajor
  exposed_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext frontDomains parameterScope)
    ((F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size) N.narrowExposed
  major_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext frontDomains parameterScope).toCtx
    N.narrowMajor N.narrowExposed

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.NarrowIndexFrame.closeFront
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
    {F : A.RecursiveCallRecursorFrame j hj}
    (N : F.NarrowIndexFrame) : Nonempty N.ClosedFront := by
  let frontLength := A.rule.allArgs.size +
    F.semantic.generated.localArgs.size
  let parameterScope := N.scope.drop frontLength
  let frontDomains := (VLCtx.toCtx (N.scope.take frontLength)).reverse
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
  have hlocalLength : F.semantic.generated.arguments_bound.fvars.length =
      F.semantic.generated.localArgs.size :=
    F.semantic.generated.arguments_bound.length_fvars
  have hfieldLength : A.rule.all_args_bound.fvars.length =
      A.rule.allArgs.size := A.rule.all_args_bound.length_fvars
  have hfrontFVars :
      (N.scope.fvars.take frontLength).reverse =
        A.rule.all_args_bound.fvars ++
          F.semantic.generated.arguments_bound.fvars := by
    rw [N.scope_fvars, N.root_fvars, hlocalFVars, hfieldFVars]
    rw [show frontLength =
        F.semantic.generated.arguments_bound.fvars.length +
          A.rule.all_args_bound.fvars.length by
      simp [frontLength, hlocalLength, hfieldLength, Nat.add_comm]]
    simp [List.take_append]
    rw [List.take_of_length_le (by simp)]
    simp
  have hfrontLE : frontLength ≤ N.scope.length := by
    rw [← N.narrow.fvars_length, N.scope_fvars, N.root_fvars,
      hlocalFVars, hfieldFVars]
    simp only [List.length_append, List.length_reverse]
    omega
  have hfrontDomains : frontDomains.length = frontLength := by
    dsimp only [frontDomains]
    rw [List.length_reverse,
      selectedLams_toCtx_take_length N.narrow.declarations,
      List.length_take,
      Nat.min_eq_left hfrontLE]
  have hctx :
      (abstractForallContext frontDomains parameterScope).toCtx =
        N.scope.toCtx := by
    rw [abstractForallContext_toCtx]
    dsimp only [frontDomains, parameterScope]
    rw [List.reverse_reverse, ← VLCtx.toCtx_append]
    exact congrArg VLCtx.toCtx
      (List.take_append_drop frontLength N.scope)
  have hprefixNodup :
      (A.rule.all_args_bound.fvars ++
        F.semantic.generated.arguments_bound.fvars).Nodup := by
    rw [← hfrontFVars]
    exact List.nodup_reverse.mpr <|
      (N.narrow.scopeWF H.outVEnvWF).fvars_nodup.sublist
        (List.take_sublist frontLength N.scope.fvars)
  have hsourceShape : ∀ source : Expr,
      source.abstractList (N.scope.fvars.take frontLength).reverse =
        (source.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size := by
    intro source
    have Habstract := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.all_args_bound.fvars)
      (inner := F.semantic.generated.arguments_bound.fvars) (k := 0)
      hprefixNodup
    rw [hlocalLength] at Habstract
    simpa [hfrontFVars] using Habstract.symm
  have closeSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams) N.scope)
        sources targets →
      List.Forall₂
        (TrExprS H.outVEnv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext frontDomains parameterScope))
        (sources.map fun source =>
          (source.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.all_args_bound.fvars
              F.semantic.generated.localArgs.size)
        targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | @cons source target sources targets Hsource _ ih =>
      have Hclosed := N.narrow.abstractPrefix H.outVEnvWF frontLength rfl
        Hsource
      rw [hsourceShape source] at Hclosed
      exact .cons Hclosed ih
  have Hindices := closeSources N.indices_translation
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
  have Hmajor := N.narrow.abstractPrefix H.outVEnvWF frontLength rfl
    N.major_translation
  have Hexposed := N.narrow.abstractPrefix H.outVEnvWF frontLength rfl
    N.exposed_translation
  rw [hsourceShape, hmajorLocal] at Hmajor
  rw [hsourceShape] at Hexposed
  have Htyping : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext frontDomains parameterScope).toCtx
      N.narrowMajor N.narrowExposed := by
    rw [hctx]
    exact N.major_typing
  exact ⟨{
    parameterScope := parameterScope
    frontDomains := frontDomains
    drop_front := rfl
    front_length := hfrontDomains
    front_fvars := hfrontFVars
    context_eq := hctx
    indices_translation := Hindices
    major_translation := by
      simpa [BoundGeneratedRecursiveCall.outerAbstractedMajor] using Hmajor
    exposed_translation := Hexposed
    major_typing := Htyping }⟩

end VerifyInductive

end Lean4Lean
