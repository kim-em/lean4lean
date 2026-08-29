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

theorem FVarNarrowCore.scopeWF
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF) :
    scope.WF env Us.length := H.lift.wf henv H.context.wf

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

theorem FVarNarrowCore.restrict
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (htr : TrExprS env Us runtime source target)
    (hclosed : Closed source 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) source) :
    ∃ target', TrExprS env Us scope source target' :=
  htr.weakFV'_inv henv H.lift (H.context.symm henv.ordered)
    hclosed hfvars

theorem FVarNarrowCore.restrictEq
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (htr : TrExprS env Us runtime e e') (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ narrow', TrExprS env Us scope e narrow' ∧
      env.IsDefEqU Us.length runtime.toCtx e'
        (narrow'.lift' H.shift) := by
  rcases H.restrict henv htr hclosed hfvars with ⟨narrow', hnarrow⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  exact ⟨narrow', hnarrow,
    htr.uniq henv (H.context.symm henv.ordered) hweak⟩

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

theorem FVarNarrowCore.hasTypeOfFullPair
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (hnarrowTerm : TrExprS env Us scope term termNarrow)
    (hnarrowType : TrExprS env Us scope type typeNarrow)
    (hfullTerm : TrExprS env Us runtime term termFull)
    (hfullType : TrExprS env Us runtime type typeFull)
    (htype : env.HasType Us.length runtime.toCtx termFull typeFull) :
    env.HasType Us.length scope.toCtx termNarrow typeNarrow := by
  have htermTarget := H.fullTargetEq henv hnarrowTerm
    (hfullTerm.trExpr henv (H.context.symm henv.ordered).wf)
  have htypeTarget := H.fullTargetEq henv hnarrowType
    (hfullType.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htermTarget.symm
  have hliftTyped' := hliftTyped.defeqU_r henv hruntimeWF htypeTarget.symm
  have hexpanded := hliftTyped'.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

theorem FVarNarrowCore.hasTypeOfFull
    (H : FVarNarrowCore env Us scope runtime) (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExprS env Us runtime e full')
    (htype : env.HasType Us.length runtime.toCtx full' (.sort u)) :
    env.HasType Us.length scope.toCtx narrow' (.sort u) := by
  have htarget := H.fullTargetEq henv hnarrow
    (hfull.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htarget.symm
  have hexpanded := hliftTyped.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

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
      (indexType.lift' H.shift) runtimeType (.sort u)) :
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

theorem MLCtxLamPrefix.extendFVarNarrowCore
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF) (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FVarNarrowCore env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowCore env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop n = baseScope ∧
        ∃ newDomains : List VExpr,
          newDomains.length = n ∧
          scope.toCtx = newDomains.reverse ++ baseScope.toCtx ∧
          Hscope.shift = Hbase.shift.consN n ∧
          ∀ {body target},
            TrExprS env Us scope body target →
            env.IsType Us.length scope.toCtx target →
            TrExprS env Us baseScope
                (runtime.mkForall n H.le body)
                (VExpr.wrapForalls newDomains target) ∧
              env.IsType Us.length baseScope.toCtx
                (VExpr.wrapForalls newDomains target) := by
  induction H with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, [], rfl, by simp,
      by simp [Lift.consN], by
        intro body target Hbody HbodyType
        simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls] using
          And.intro Hbody HbodyType⟩
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
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
    rcases ih HtailWF Hbase htailUp with
      ⟨tailScope, HtailScope, htailScopeFVars, htailBase,
        tailDomains, htailDomains, htailContext, htailShift,
        HtailReplay⟩
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
    have hclosed : Closed type 0 := by
      have h := Htype.closed
      rw [tail.noBV] at h
      exact h
    have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
      apply fvarsIn_iff.mpr
      exact ⟨hdeps, Htype.fvarsIn.mono fun _ _ => trivial⟩
    rcases HtailScope.restrict henv Htype hclosed htypeFVars with
      ⟨narrowType, HnarrowType⟩
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
    let Hnext := HtailScope.withIndex HruntimeWF hdeps Hdomain
    refine ⟨_, Hnext, ?_, ?_, tailDomains ++ [narrowType], ?_, ?_,
      ?_, ?_⟩
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
      have HnextWF := Hnext.scopeWF henv
      have HdomainType : env.IsType Us.length tailScope.toCtx narrowType := by
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowCore.withIndex,
          VLocalDecl.WF] using HnextWF.2.2
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
      localDomains, hlocal, hcontext, hshift, _Hreplay⟩
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
    hlocal, hcontext, hshift, Hnarrow, Heq⟩

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
