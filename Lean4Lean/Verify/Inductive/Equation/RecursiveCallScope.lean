import Lean4Lean.Verify.Inductive.Equation.RecursiveCallFrame

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopType

/-- The proof-relevant core of a dependency-selected scope.  Unlike
`FVarNarrowScope`, this certificate does not retain source declaration names
and domains; equation assembly needs the checked embedding, declaration
shape, and target context, but closes its already-abstracted source terms
directly.  Omitting source provenance lets the certificate reuse the exact
cached parameter/field targets rather than choosing a second translation. -/
structure FVarNarrowCore (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  declarations : List.Forall₂
    (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), .vlam type))
    scope.fvars scope
  wf : scope.WF env Us.length

def FVarNarrowCore.mono {env env' : VEnv} (henv : env ≤ env')
    (H : FVarNarrowCore env Us scope runtime) :
    FVarNarrowCore env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf.mono henv

def FVarNarrowScope.toCore
    (H : FVarNarrowScope env Us scope runtime) :
    FVarNarrowCore env Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context
  upset := H.upset
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf

def FVarNarrowCore.retargetRuntime
    (H : FVarNarrowCore env Us scope runtime) (h : runtime = runtime') :
    FVarNarrowCore env Us scope runtime' where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := by cases h; exact H.context
  upset := by cases h; exact H.upset
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf

theorem FVarNarrowCore.scopeWF
    (H : FVarNarrowCore env Us scope runtime) (_henv : env.WF) :
    scope.WF env Us.length := H.wf

theorem FVarNarrowCore.fvars_length
    (H : FVarNarrowCore env Us scope runtime) :
    scope.fvars.length = scope.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.declarations

private theorem coreDeclarations_toCtx_length
    {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) fvars scope) :
    scope.toCtx.length = scope.length := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simp [VLCtx.toCtx, ih]

theorem FVarNarrowCore.toCtx_length
    (H : FVarNarrowCore env Us scope runtime) :
    scope.toCtx.length = scope.length :=
  coreDeclarations_toCtx_length H.declarations

theorem FVarNarrowCore.fullTargetEq
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

private theorem coreNamedDeclarations_fvars
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) xs ys) :
    VLCtx.fvars ys = xs := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simpa [VLCtx.fvars] using ih

private theorem coreForall₂_take
    {R : α → β → Prop} (H : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction n generalizing xs ys with
  | zero => exact .nil
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons h Htail => exact .cons h (ih Htail)

theorem FVarNarrowCore.fvars_take
    (H : FVarNarrowCore env Us scope runtime) (n : Nat) :
    VLCtx.fvars (scope.take n) = scope.fvars.take n :=
  coreNamedDeclarations_fvars (coreForall₂_take H.declarations n)

theorem FVarNarrowCore.abstractPrefix
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF) (n : Nat)
    (hbase : scope.drop n = baseScope)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext (VLCtx.toCtx (scope.take n)).reverse baseScope)
      (source.abstractList (scope.fvars.take n).reverse) target := by
  let scopePrefix := scope.take n
  let tail := scope.drop n
  have hscope : scopePrefix ++ tail = scope := by
    simpa [scopePrefix, tail] using (List.take_append_drop n scope).symm
  have Hprefix := coreForall₂_take H.declarations n
  have hprefixFVars : VLCtx.fvars scopePrefix = scope.fvars.take n :=
    coreNamedDeclarations_fvars Hprefix
  have Htr' : TrExprS env Us
      (abstractForallContext [] (scopePrefix ++ tail)) source target := by
    simpa [abstractForallContext, hscope] using Htr
  have hnodup : (scope.fvars.take n).Nodup :=
    (H.scopeWF henv).fvars_nodup.sublist
      (List.take_sublist n scope.fvars)
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    (domains := []) Hprefix hnodup Htr'
  simpa [scopePrefix, tail, hprefixFVars, hbase] using Habstract

theorem FVarNarrowCore.abstractAll
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList scope.fvars.reverse) target := by
  have Htr' : TrExprS env Us
      (abstractForallContext [] scope) source target := by
    simpa [abstractForallContext] using Htr
  have hnodup := (H.scopeWF henv).fvars_nodup
  simpa using TrExprS.abstractFVarLambdaSuffix
    H.declarations hnodup Htr'

def FVarNarrowCore.withIndex
    (H : FVarNarrowCore env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u))
    (htype : env.IsType Us.length scope.toCtx indexType) :
    FVarNarrowCore env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := H.noBV
  declarations := .cons ⟨deps, indexType, rfl⟩ H.declarations
  wf := by
    refine ⟨H.wf, ?_, htype⟩
    rintro _ _ ⟨⟩
    refine ⟨fun hmem => ?_, hdeps⟩
    have hsub : scope.fvars ⊆ runtime.fvars := by
      rw [← H.context.fvars]
      exact H.lift.fvars_sublist.subset
    exact (hnewRuntime.2.1 _ _ rfl).1 (hsub hmem)

def FVarNarrowCore.skipIndex
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hskip : fv ∉ scope.fvars) :
    FVarNarrowCore env Us scope
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded := (some (fv, deps), .vlam runtimeType) :: H.expanded
  shift := H.shift.skipN 1
  lift := H.lift.skip_fvar (fv, deps) (.vlam runtimeType)
  context := by
    have Htype : env.IsType Us.length H.expanded.toCtx runtimeType :=
      hnewRuntime.2.2.defeqDFC henv.ordered
        (H.context.defeqCtx.symm henv.ordered)
    rcases Htype with ⟨level, Htype⟩
    exact .cons H.context (by
      have hfresh := hnewRuntime.2.1
      simpa [H.context.fvars] using hfresh)
      (VLocalDecl.IsDefEq.refl henv H.context.wf.toCtx
        ⟨level, Htype⟩)
  upset := by
    refine ⟨H.upset, ?_⟩
    intro hmem
    exact False.elim (hskip hmem)
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf

end checkInductiveTypes.loopType

theorem MLCtxLamPrefix.skipFVarNarrowCore
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF) (Hwf : runtime.WF env Us)
    (Hbase : Nonempty
      (checkInductiveTypes.loopType.FVarNarrowCore env Us
        baseScope (runtime.dropN n H.le).vlctx))
    (hskip : ∀ fv ∈ runtime.fvarRevList n H.le,
      fv ∉ baseScope.fvars) :
    Nonempty (checkInductiveTypes.loopType.FVarNarrowCore env Us
      baseScope runtime.vlctx) := by
  induction H with
  | nil runtime => exact Hbase
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, _hfresh, _Htype, _HtypeType⟩
    have htailSkip : ∀ other ∈ tail.fvarRevList n Hprefix.le,
        other ∉ baseScope.fvars := by
      intro other hother
      exact hskip other (by simp [TypeChecker.MLCtx.fvarRevList, hother])
    rcases ih HtailWF Hbase htailSkip with ⟨Htail⟩
    have hhead : fv ∉ baseScope.fvars :=
      hskip fv (by simp [TypeChecker.MLCtx.fvarRevList])
    exact ⟨Htail.skipIndex henv HruntimeWF hhead⟩

/-- `extendFVarNarrowCore` when the recent prefix was also opened in a checker
context embedded in the base scope.  Each retained domain is the checker
translation weakened along the embedding, so no runtime translation is
restricted. -/
theorem MLCtxLamPrefix.extendFVarNarrowCoreEmbedded
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF) (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FVarNarrowCore env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx)
    {chk : TypeChecker.MLCtx} (hchkWF : chk.WF env Us)
    (hn : n ≤ chk.length) (hagree : MLCtxTopAgree runtime chk n)
    (hbaseEmb : ChkEmbeds env Us.length (chk.dropN n hn).vlctx baseScope) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowCore env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop n = baseScope ∧
        ∃ newDomains : List VExpr,
          newDomains.length = n ∧
          scope.toCtx = newDomains.reverse ++ baseScope.toCtx ∧
          Hscope.shift = Hbase.shift.consN n ∧
          (∀ {body target},
            TrExprS env Us scope body target →
            env.IsType Us.length scope.toCtx target →
            TrExprS env Us baseScope
                (runtime.mkForall n H.le body)
                (VExpr.wrapForalls newDomains target) ∧
              env.IsType Us.length baseScope.toCtx
                (VExpr.wrapForalls newDomains target)) ∧
          ChkEmbeds env Us.length chk.vlctx scope := by
  induction H generalizing chk with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, [], rfl, by simp,
      by simp [Lift.consN], by
        intro body target Hbody HbodyType
        simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls] using
          And.intro Hbody HbodyType,
      by simpa using hbaseEmb⟩
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    cases hagree with
    | @vlam _ chkTail _ hagreeTail _ _ _ _ t₂ _ =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    rcases hchkWF with ⟨hchkTailWF, _hfreshC, Htype₀, Htype₀Type⟩
    have hcurrentFresh : fv ∉ tail.vlctx.fvars :=
      HtailWF.tr.find?_eq_none.1 hfresh
    have htailUp : IsFVarUpSet
        (fun fv' =>
          fv' ∈ tail.fvarRevList n Hprefix.le ++ baseScope.fvars)
        tail.vlctx := by
      apply (IsFVarUpSet.congr HtailWF.tr.wf.fvwf ?_).mp hup.1
      intro fv' hfv'
      constructor
      · intro h
        rcases List.mem_cons.mp h with hcurrent | h
        · exact False.elim (hcurrentFresh (hcurrent ▸ hfv'))
        · exact h
      · exact List.mem_cons_of_mem _
    have hnTail : n ≤ chkTail.length := by simpa using hn
    rcases ih HtailWF Hbase htailUp hchkTailWF hnTail hagreeTail
        (by simpa using hbaseEmb) with
      ⟨tailScope, HtailScope, htailScopeFVars, htailBase,
        tailDomains, htailDomains, htailContext, htailShift,
        HtailReplay, hembTail⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars :=
      hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim
          (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    obtain ⟨narrowType, HnarrowType⟩ := hembTail.trExprS henv Htype₀
    have HnarrowIsType : env.IsType Us.length tailScope.toCtx narrowType :=
      hembTail.isType henv Htype₀ HnarrowType Htype₀Type
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' := HtypeType.defeqDFC henv.ordered
          (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex HruntimeWF hdeps Hdomain HnarrowIsType
    have hfreshScope : fv ∉ tailScope.fvars := by
      intro hmem
      have hsub : tailScope.fvars ⊆ tail.vlctx.fvars := by
        rw [← HtailScope.context.fvars]
        exact HtailScope.lift.fvars_sublist.subset
      exact hcurrentFresh (hsub hmem)
    refine ⟨_, Hnext, ?_, ?_, tailDomains ++ [narrowType], ?_, ?_,
      ?_, ?_, ?_⟩
    · simp [htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · simpa using htailBase
    · simp [htailDomains]
    · change narrowType :: tailScope.toCtx = _
      rw [htailContext]
      simp [List.reverse_append, List.append_assoc]
    · change HtailScope.shift.consN 1 = Hbase.shift.consN (n + 1)
      rw [htailShift]
      simp [Lift.consN]
    · intro body target Hbody HbodyType
      have HdomainType : env.IsType Us.length tailScope.toCtx narrowType :=
        HnarrowIsType
      have W : VLCtx.Abstract tailScope fv (.vlam narrowType) 0 0
          ((some (fv, type.fvarsList), .vlam narrowType) :: tailScope)
          ((none, .vlam narrowType) :: tailScope) := .zero
      have Hbody' : TrExprS env Us
          ((none, .vlam narrowType) :: tailScope)
          (body.abstract1 fv) target := by
        apply TrExprS.abstract W
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowCore.withIndex] using Hbody
      have HbodyType' : env.IsType Us.length
          (narrowType :: tailScope.toCtx) target := by
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowCore.withIndex,
          VLCtx.toCtx] using HbodyType
      have Hone : TrExprS env Us tailScope
          (.forallE name type (body.abstract1 fv) bi)
          (.forallE narrowType target) :=
        .forallE HdomainType HbodyType' HnarrowType Hbody'
      have HoneType : env.IsType Us.length tailScope.toCtx
          (.forallE narrowType target) :=
        VEnv.IsType.forallE HdomainType HbodyType'
      have Hclosed := HtailReplay Hone HoneType
      simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls_append,
        VExpr.wrapForalls] using Hclosed
    · exact hembTail.cons henv hfreshScope Htype₀ HnarrowType HnarrowIsType

/-- Skip a producer-retained hypothesis suffix above an exact target scope.
The target declarations are preserved definitionally; only the executable
weakening records the skipped hypotheses. -/
theorem RecursorRecentBoundFVarArray.skipFVarNarrowCore
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot Rcurrent xs)
    (Hbase : Nonempty
      (checkInductiveTypes.loopType.FVarNarrowCore
        Rroot.venv recLparams baseScope Rroot.mlctx.vlctx))
    (hbase : baseScope.fvars ⊆ Rroot.mlctx.vlctx.fvars) :
    Nonempty (checkInductiveTypes.loopType.FVarNarrowCore
      Rcurrent.venv recLparams baseScope Rcurrent.mlctx.vlctx) := by
  rcases Rcurrent.onlyLams.lamPrefix xs.size H.size_le with
    ⟨_domains, Hprefix⟩
  have Hbase' : Nonempty
      (checkInductiveTypes.loopType.FVarNarrowCore
        Rcurrent.venv recLparams baseScope
          (Rcurrent.mlctx.dropN xs.size Hprefix.le).vlctx) := by
    have hle : Hprefix.le = H.size_le := Subsingleton.elim _ _
    rw [hle, H.drop_eq]
    simpa only [H.venv_eq] using Hbase
  have hskip : ∀ fv ∈
      Rcurrent.mlctx.fvarRevList xs.size Hprefix.le,
      fv ∉ baseScope.fvars := by
    intro fv hfv hselected
    have hle : Hprefix.le = H.size_le := Subsingleton.elim _ _
    rw [hle, H.fvarRevList_eq] at hfv
    exact H.fresh fv (List.mem_reverse.mp hfv) (by
      rw [← Rroot.lctx_eq, Rroot.mlctx_wf.tr.fvars_eq]
      exact hbase hselected)
  exact Hprefix.skipFVarNarrowCore Rcurrent.checking.tr.wf
    Rcurrent.mlctx_wf Hbase' hskip

/-- The motive application checked while producing this exact recursive
call, transported across the final constant-environment extension. -/
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
      (R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries :=
    F.semantic.recent.venv_eq.trans <|
      F.originRecent.venv_eq.trans <|
        A.semantics.context_venv.trans <|
          H.recursorEnv_legacy.trans R.declared.contextVEnv
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

/-- Filtering the literal producer origin by the recursive call's declared
field/parameter scope removes every earlier generated hypothesis and retains
exactly the completed rule context's corresponding selection. -/
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

end VerifyInductive

end Lean4Lean
