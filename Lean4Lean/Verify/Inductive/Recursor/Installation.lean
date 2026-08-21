import Lean4Lean.Verify.Inductive.Recursor.Generation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

theorem MLCtxLamPrefix.forallDomains
    (H : MLCtxLamPrefix c n domains) :
    MLCtxForallDomains c n H.le = domains := by
  induction H with
  | nil => simp [MLCtxForallDomains]
  | cons H ih =>
    simp only [MLCtxForallDomains]
    change MLCtxForallDomains _ _ H.le ++ [_] = _
    rw [ih]

theorem MLCtxLamPrefix.mkForall'
    (H : MLCtxLamPrefix c n domains) (body : VExpr) :
    c.mkForall' n H.le body = VExpr.wrapForalls domains body := by
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, H.forallDomains]

/-- Every bounded prefix of an all-lambda checker context has an exact
`MLCtxLamPrefix` certificate.  This packages the structural induction needed
when a later proof must replay a retained recent suffix one declaration at a
time. -/
theorem MLCtxOnlyLams.lamPrefix
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    ∃ domains, MLCtxLamPrefix c n domains := by
  induction n generalizing c with
  | zero => exact ⟨[], .nil c⟩
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      rcases ih H.tail_vlam (Nat.le_of_succ_le_succ hn) with
        ⟨domains, Hprefix⟩
      exact ⟨domains ++ [type'], Hprefix.cons⟩
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Replace the selected base of an up-set beneath an exact recent lambda
prefix.  Every recent declaration is already selected by `Q`; if `Q` is
contained in the enlarged predicate `P`, the dependency obligations for the
recent prefix can be reused while the dropped suffix is discharged by an
independent `P` up-set. -/
theorem MLCtxLamPrefix.isFVarUpSet_of_base
    (H : MLCtxLamPrefix runtime n domains)
    (Hfull : IsFVarUpSet Q runtime.vlctx)
    (Hbase : IsFVarUpSet P (runtime.dropN n H.le).vlctx)
    (hrecent : ∀ fv ∈ runtime.fvarRevList n H.le, Q fv)
    (hmono : ∀ fv, Q fv → P fv) :
    IsFVarUpSet P runtime.vlctx := by
  induction H with
  | nil runtime => simpa using Hbase
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    refine ⟨ih Hfull.1 Hbase ?_, ?_⟩
    · intro other hother
      apply hrecent other
      exact List.mem_cons_of_mem _ hother
    · intro _ dep hdep
      apply hmono dep
      exact Hfull.2 (hrecent fv (by simp
        [TypeChecker.MLCtx.fvarRevList])) dep hdep

/-- Replay an exact recent all-lambda prefix on top of an already narrowed
base scope.  The up-set premise says precisely that every retained recent
declaration depends only on older retained declarations or the base scope.
The resulting `NarrowRuntimeScope` remembers the whole recent prefix in its
`front`, so it can subsequently be closed while exposing the original base
weakening. -/
theorem MLCtxLamPrefix.extendNarrowRuntimeScope
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF)
    (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.NarrowRuntimeScope env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop Hscope.frontSourceDomains.length =
          baseScope.drop Hbase.frontSourceDomains.length ∧
        ∃ newDomains,
          newDomains.length = n ∧
          Hscope.frontSourceDomains =
            Hbase.frontSourceDomains ++ newDomains := by
  induction H with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, [], rfl, by simp⟩
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
        tailDomains, htailDomains, htailFront⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars := by
      exact hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    have hclosed : Closed type 0 := by
      have h := Htype.closed
      rw [tail.noBV] at h
      exact h
    have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
      apply fvarsIn_iff.mpr
      refine ⟨hdeps, ?_⟩
      exact Htype.fvarsIn.mono fun _ _ => trivial
    rcases HtailScope.restrict henv Htype hclosed htypeFVars with
      ⟨narrowType, HnarrowType⟩
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' :=
      HtypeType.defeqDFC henv.ordered
        (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex
      HruntimeWF
      hdeps Hdomain
    refine ⟨_, Hnext, ?_, ?_, tailDomains ++ [narrowType], ?_, ?_⟩
    · simp [Hnext, htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · dsimp [Hnext, checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex]
      simpa only [List.length_append, List.length_singleton,
        List.drop_succ_cons] using htailBase
    · simp [htailDomains]
    · dsimp [Hnext, checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex]
      rw [htailFront]
      simp [List.append_assoc]

/-- Replay an exact recent all-lambda prefix above a dependency-selected,
possibly non-contiguous free-variable scope.  Unlike
`extendNarrowRuntimeScope`, the base has no distinguished contiguous front;
the result therefore records the newly translated domains directly and
retains the literal named semantic declarations introduced by the source
checker. -/
theorem MLCtxLamPrefix.extendFVarNarrowScope
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF)
    (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FVarNarrowScope env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop n = baseScope ∧
        ∃ newDomains : List VExpr,
          newDomains.length = n ∧
          scope.toCtx = newDomains.reverse ++ baseScope.toCtx ∧
          Hscope.shift = Hbase.shift.consN n ∧
          Hscope.expanded.toCtx =
            (liftForallDomains newDomains Hbase.shift).reverse ++
              Hbase.expanded.toCtx ∧
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
      by simp [Lift.consN], by simp [liftForallDomains], by
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
        htailExpanded, HtailReplay⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars := by
      exact hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    have hclosed : Closed type 0 := by
      have h := Htype.closed
      rw [tail.noBV] at h
      exact h
    have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
      apply fvarsIn_iff.mpr
      refine ⟨hdeps, ?_⟩
      exact Htype.fvarsIn.mono fun _ _ => trivial
    rcases HtailScope.restrict henv Htype hclosed htypeFVars with
      ⟨narrowType, HnarrowType⟩
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' :=
      HtypeType.defeqDFC henv.ordered
        (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex HruntimeWF hdeps name bi type
      HnarrowType Hdomain
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
    · change narrowType.lift' HtailScope.shift ::
        HtailScope.expanded.toCtx = _
      rw [htailExpanded, liftForallDomains_append, htailShift]
      simp [liftForallDomains, htailDomains, List.reverse_append,
        List.append_assoc]
    · intro body target Hbody HbodyType
      have HnextWF := Hnext.scopeWF henv
      have HdomainType : env.IsType Us.length tailScope.toCtx narrowType := by
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowScope.withIndex,
          VLocalDecl.WF] using HnextWF.2.2
      have W : VLCtx.Abstract tailScope fv (.vlam narrowType) 0 0
          ((some (fv, type.fvarsList), .vlam narrowType) :: tailScope)
          ((none, .vlam narrowType) :: tailScope) := .zero
      have Hbody' : TrExprS env Us
          ((none, .vlam narrowType) :: tailScope)
          (body.abstract1 fv) target := by
        apply TrExprS.abstract W
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowScope.withIndex] using
          Hbody
      have HbodyType' : env.IsType Us.length
          (narrowType :: tailScope.toCtx) target := by
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarNarrowScope.withIndex,
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

/-- Strengthening of `extendNarrowRuntimeScope` which retains the strict
translation used for every narrowed binder domain.  The ordinary runtime
scope only remembers the resulting verifier domains and their weakening;
that is sufficient for executable checking, but a later comparison with an
independently generated dependent telescope needs the complete source
translation.  Replaying an arbitrary translated residual packages exactly
that missing evidence as a translated forall telescope. -/
theorem MLCtxLamPrefix.extendNarrowRuntimeScopeForallReplay
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF)
    (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.NarrowRuntimeScope env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.NarrowRuntimeScope env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop Hscope.frontSourceDomains.length =
          baseScope.drop Hbase.frontSourceDomains.length ∧
        ∃ newDomains,
          newDomains.length = n ∧
          Hscope.frontSourceDomains =
            Hbase.frontSourceDomains ++ newDomains ∧
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
    refine ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, [], rfl, by simp, ?_⟩
    intro body target Hbody HbodyType
    simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls] using
      And.intro Hbody HbodyType
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
        tailDomains, htailDomains, htailFront, HtailReplay⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars := by
      exact hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    have hclosed : Closed type 0 := by
      have h := Htype.closed
      rw [tail.noBV] at h
      exact h
    have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
      apply fvarsIn_iff.mpr
      refine ⟨hdeps, ?_⟩
      exact Htype.fvarsIn.mono fun _ _ => trivial
    rcases HtailScope.restrict henv Htype hclosed htypeFVars with
      ⟨narrowType, HnarrowType⟩
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' :=
      HtypeType.defeqDFC henv.ordered
        (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex HruntimeWF hdeps Hdomain
    refine ⟨_, Hnext, ?_, ?_, tailDomains ++ [narrowType], ?_, ?_, ?_⟩
    · simp [Hnext, htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · dsimp [Hnext, checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex]
      simpa only [List.length_append, List.length_singleton,
        List.drop_succ_cons] using htailBase
    · simp [htailDomains]
    · dsimp [Hnext, checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex]
      rw [htailFront]
      simp [List.append_assoc]
    · intro body target Hbody HbodyType
      have HnextWF := Hnext.scopeWF henv
      have HdomainType : env.IsType Us.length tailScope.toCtx narrowType := by
        simpa [Hnext,
          checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex,
          VLocalDecl.WF] using
          HnextWF.2.2
      have W : VLCtx.Abstract tailScope fv (.vlam narrowType) 0 0
          ((some (fv, type.fvarsList), .vlam narrowType) :: tailScope)
          ((none, .vlam narrowType) :: tailScope) := .zero
      have Hbody' : TrExprS env Us
          ((none, .vlam narrowType) :: tailScope)
          (body.abstract1 fv) target := by
        apply TrExprS.abstract W
        simpa [Hnext,
          checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex] using
          Hbody
      have HbodyType' : env.IsType Us.length
          (narrowType :: tailScope.toCtx) target := by
        simpa [Hnext,
          checkInductiveTypes.loopType.NarrowRuntimeScope.withIndex,
          VLCtx.toCtx] using
          HbodyType
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

/-- Production-side installation of a list of kernel constants. This small
reference function is used only to state the staging invariant; the executable
inductive checker continues to build the same environments directly. -/
def addConstants : Environment → List ConstantInfo → Environment
  | env, [] => env
  | env, ci :: cis => addConstants (env.add ci) cis

/-- A certificate that a list of production constants and abstract constants
are installed in lockstep. Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AddConstants.append
    (H₁ : AddConstants safety env venv entries middleEnv middleVEnv)
    (H₂ : AddConstants safety middleEnv middleVEnv rest outEnv outVEnv) :
    AddConstants safety env venv (entries ++ rest) outEnv outVEnv := by
  induction H₁ with
  | nil => exact H₂
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact .cons hn hnprim htr hwf hadd hdelta (ih H₂)

theorem AddConstants.hasPrimitives
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Hprimitives : venv.HasPrimitives) : outVEnv.HasPrimitives := by
  induction H with
  | nil => exact Hprimitives
  | cons _hn hnprim _htr _hwf hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnonprim :
        Kernel.Environment.primitives.contains ci.name = false := by
      cases h : Kernel.Environment.primitives.contains ci.name <;>
        simp_all
    exact ih (Lean4Lean.VEnv.HasPrimitives.addConst Hprimitives
      hnonprim hadd)

/-- Replay a lockstep constant installation in a larger abstract source
environment.  The production trace and generated constants are unchanged;
translations and typing are weakened monotonically, and the resulting target
extends the original abstract target. -/
theorem AddConstants.rebase
    (H : AddConstants checkSafety prodEnv base entries outProd outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    ∃ largerOut,
      AddConstants safety prodEnv largerBase entries outProd largerOut ∧
      outBase ≤ largerOut := by
  induction H generalizing largerBase with
  | nil => exact ⟨largerBase, .nil, hbase⟩
  | cons hn hnprim htr hwf hadd hdelta _Htail ih =>
    rename_i baseHead ci ci' baseNext rest outProd outBase prodHead
    have hexists : ∃ largerNext,
        largerBase.addConst ci.name ci'.toVConstant = some largerNext := by
      unfold VEnv.addConst
      cases hfind : largerBase.constants ci.name with
      | none => simp
      | some existing =>
        exfalso
        rcases Hvalid.tr.find?_iff.mpr ⟨existing, hfind⟩ with
          ⟨source, hsource, _⟩
        rw [hn] at hsource
        contradiction
    rcases hexists with ⟨largerNext, hlargerAdd⟩
    have htrLarger :
        TrConstVal safety largerBase ci ci' :=
      ⟨(htr.1.sf_mono hsafety).mono hbase, htr.2⟩
    have hwfLarger : ci'.toVConstant.WF largerBase := hwf.mono hbase
    have HvalidNext : CheckingEnv.Valid safety (prodHead.add ci)
        largerNext :=
      Hvalid.add hn hnprim htrLarger.1 hwfLarger hlargerAdd hdelta
    have hnext : baseNext ≤ largerNext :=
      VEnv.addConst_mono hbase hadd hlargerAdd
    rcases ih HvalidNext hnext with ⟨largerOut, Htail, hout⟩
    exact ⟨largerOut,
      .cons hn hnprim htrLarger hwfLarger hlargerAdd hdelta Htail, hout⟩

/-- A lockstep installation checked at a stronger visibility level is also a
valid installation trace for every weaker observer.  The installed abstract
constants and all freshness/typing facts are unchanged. -/
def AddConstants.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : AddConstants checkSafety prodEnv venv entries outEnv outVEnv) :
    AddConstants safety prodEnv venv entries outEnv outVEnv := by
  induction H with
  | nil => exact .nil
  | cons hn hnprim htr hwf hadd hdelta _Htail ih =>
    exact .cons hn hnprim ⟨htr.1.sf_mono hsafety, htr.2⟩ hwf hadd
      hdelta ih

theorem AddConstants.prod_eq
    (H₁ : AddConstants safety₁ prodEnv venv₁ entries outEnv₁ outVEnv₁)
    (H₂ : AddConstants safety₂ prodEnv venv₂ entries outEnv₂ outVEnv₂) :
    outEnv₁ = outEnv₂ := by
  induction H₁ generalizing venv₂ outEnv₂ outVEnv₂ with
  | nil =>
    cases H₂
    rfl
  | cons _hn _hnprim _htr _hwf _hadd _hdelta _Htail ih =>
    cases H₂ with
    | cons _ _ _ _ _ _ Htail₂ => exact ih Htail₂

theorem AddConstants.quotInit_eq
    (H : AddConstants safety prodEnv venv entries outEnv outVEnv) :
    outEnv.quotInit = prodEnv.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

/-- Combine translations from an original strong-safety trace with the
freshness/install equations of a replayed trace.  This permits the replayed
abstract target to be viewed at any observer safety supported by the
original trace, even when that observer is stronger than the safety index at
which the replay itself was constructed. -/
theorem AddConstants.reindex
    (H : AddConstants checkSafety prodEnv base entries outEnv outBase)
    (Hlarger : AddConstants targetSafety prodEnv largerBase entries
      outEnv largerOut)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase) :
    AddConstants safety prodEnv largerBase entries outEnv largerOut := by
  induction H generalizing largerBase largerOut with
  | nil =>
    cases Hlarger
    exact .nil
  | cons hn hnprim htr hwf hadd hdelta _Htail ih =>
    cases Hlarger with
    | cons hnL hnprimL _htrL _hwfL haddL hdeltaL HtailL =>
      exact .cons hnL hnprimL
        ⟨(htr.1.sf_mono hsafety).mono hbase, htr.2⟩
        (hwf.mono hbase) haddL hdeltaL
        (ih HtailL (VEnv.addConst_mono hbase hadd haddL))

/-- Lockstep installation preserves concrete/abstract alignment.  This is
the production-map component of `AddInduct`; it follows from the executable
staging trace and need not be supplied by a later compilation proof. -/
theorem AddConstants.aligned
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Haligned : Aligned safety env.constants venv) :
    Aligned safety outEnv.constants outVEnv := by
  induction H with
  | nil => exact Haligned
  | cons hn _hnprim htr _hwf hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Haligned.map_wf.find?'_eq_find?]
      exact hn
    exact ih (Haligned.const hnMap htr.1 hadd rfl)

/-- If every newly installed production constant is hidden from an observer,
the observer's abstract environment is unchanged across the whole lockstep
installation. -/
theorem AddConstants.trEnvIgnore
    (H : AddConstants checkSafety prodEnv venv entries outEnv outVEnv)
    (hhidden : ∀ entry ∈ entries, ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv := by
  induction H with
  | nil => exact htr
  | cons hn _hnprim _hentry _hwf _hadd _hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← htr.map_wf.find?'_eq_find?]
      exact hn
    have htrHead : TrEnv' observerSafety
        (envHead.constants.insert ci.name ci) quotInit observerEnv :=
      TrEnv'.ignore hnMap (hhidden (ci, ci') (by simp)) htr
    exact ih (fun entry hentry => hhidden entry (by simp [hentry])) htrHead

/-- Constants introduced by an inductive staging trace have no delta value,
so every delta-bearing entry in the final production map was already present
in the source map. -/
theorem AddConstants.deltaConservative
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (Halign : Aligned safety env.constants venv) :
    ∀ {name ci}, outEnv.constants.find? name = some ci →
      ci.deltaValue?.isSome → env.constants.find? name = some ci := by
  induction H with
  | nil => intro name ci hfind _; exact hfind
  | cons hn _hnprim htr _hwf hadd hdelta _Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    intro name found hfind hfoundDelta
    have hnMap : envHead.constants.find? ci.name = none := by
      rw [← Halign.map_wf.find?'_eq_find?]
      exact hn
    have Halign' : Aligned safety
        (envHead.constants.insert ci.name ci) venvNext :=
      Halign.const hnMap htr.1 hadd rfl
    have hnext : (envHead.constants.insert ci.name ci).find? name = some found :=
      ih Halign' hfind hfoundDelta
    rw [Halign.map_wf.find?_insert] at hnext
    split at hnext
    · cases hnext
      simp [hdelta] at hfoundDelta
    · exact hnext

theorem aligned_addDefEqs
    (H : Aligned safety C venv) (rules : List VDefEq) :
    Aligned safety C (venv.addDefEqRules rules) := by
  induction rules generalizing venv with
  | nil => exact H
  | cons rule rules ih =>
    exact ih H.defeq

theorem hasPrimitives_addDefEqs
    {venv : VEnv} (H : venv.HasPrimitives) (rules : List VDefEq) :
    (venv.addDefEqRules rules).HasPrimitives := by
  induction rules generalizing venv with
  | nil => exact H
  | cons rule rules ih => exact ih H.addDefEq

theorem CheckingEnv.exists_addConst
    (H : CheckingEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) :
    ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci =>
    exfalso
    rcases H.find?_iff.mpr ⟨ci, hfind⟩ with ⟨source, hsource, _⟩
    rw [hn] at hsource
    contradiction

/-- A successful executable installation fold yields the lockstep production
/ abstract staging certificate. Translation and typing may be proved in an
earlier environment and are transported through the already installed
prefix. -/
theorem AddConstants.ofDeclareInductiveTypeInfos
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv ≤ venv)
    (hadd : venv.addConstVals values = some outVEnv)
    (hnprim : ∀ info ∈ infos,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv =>
        AddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    simp [AddInductive.declareInductiveTypeInfos, VEnv.addConstVals] at hadd ⊢
    subst outVEnv
    exact Except.WF.pure .nil
  | @cons info ci' infos values Hentry _ ih =>
    have hname : info.name = ci'.name := Hentry.1.2
    cases hnext : venv.addConst ci'.name ci'.toVConstant with
    | none => simp [VEnv.addConstVals, hnext] at hadd
    | some nextVEnv =>
      have hrest : nextVEnv.addConstVals values = some outVEnv := by
        simpa [VEnv.addConstVals, hnext] using hadd
      have hnprimHead := hnprim info (by simp)
      have hnprimTail : ∀ info ∈ infos,
          ¬ Kernel.Environment.primitives.contains info.name := by
        intro info hinfo
        exact hnprim info (by simp [hinfo])
      rw [AddInductive.declareInductiveTypeInfos]
      exact (checkName.WF Hvalid.tr.map_wf info.name allowPrimitive).bind
        fun _ hchecked => by
          have hn : env.find? info.name = none := hchecked.1
          have htr : TrConstVal safety venv (.inductInfo info) ci' :=
            Hentry.1.mono hle
          have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [hname] using hnext
          have HnextValid : CheckingEnv.Valid safety
              (env.add (.inductInfo info)) nextVEnv :=
            Hvalid.add hn hnprimHead htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih HnextValid hnextLe hrest hnprimTail).mono fun outEnv Hrest => by
            simpa using AddConstants.cons (ci := .inductInfo info)
              (ci' := ci') hn hnprimHead htr hwf haddHead rfl Hrest

/-- The inner production constructor fold installs a translated constructor
list in lockstep with its abstract constants.  Constructor metadata is kept
parametric because only the source name, type, level parameters, and safety
participate in the translation relation. -/
inductive ConstructorListEntries
    (mkInfo : Nat → Constructor → ConstructorVal) :
    Nat → List Constructor → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorListEntries mkInfo start [] []
  | cons : ConstructorListEntries mkInfo (start + 1) ctors entries →
      ConstructorListEntries mkInfo start (ctor :: ctors)
        ((.ctorInfo (mkInfo start ctor), value) :: entries)

/-- Family-major source alignment of the complete constructor-entry batch. -/
inductive ConstructorTypeEntries
    (mkInfo : InductiveType → Nat → Constructor → ConstructorVal) :
    List InductiveType → List (ConstantInfo × VConstVal) → Prop
  | nil : ConstructorTypeEntries mkInfo [] []
  | cons : ConstructorListEntries (mkInfo owner) 0 owner.ctors head →
      ConstructorTypeEntries mkInfo owners tail →
      ConstructorTypeEntries mkInfo (owner :: owners) (head ++ tail)

theorem ConstructorListEntries.findSource
    {initial : Nat}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    (hctor : ctor ∈ ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.type = ctor.type ∧
      info.levelParams = lparams ∧ info.isUnsafe = isUnsafe := by
  cases H with
  | nil => simp at hctor
  | cons Htail =>
    rename_i tail tailEntries headValue
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact ⟨AddInductive.constructorInfo stats lparams isUnsafe owner
        initial ctor, headValue, by simp,
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo]⟩
    · rcases Htail.findSource htail with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, by simp [hmem], hname, htype, hlevels, hunsafe⟩

theorem ConstructorTypeEntries.findSource
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (howner : owner ∈ types) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.type = ctor.type ∧
      info.levelParams = lparams ∧ info.isUnsafe = isUnsafe := by
  induction H generalizing owner with
  | nil => simp at howner
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at howner
    rcases howner with rfl | htailOwner
    · rcases Hhead.findSource hctor with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, List.mem_append_left _ hmem, hname, htype,
        hlevels, hunsafe⟩
    · rcases ih htailOwner hctor with
        ⟨info, value, hmem, hname, htype, hlevels, hunsafe⟩
      exact ⟨info, value, List.mem_append_right _ hmem, hname, htype,
        hlevels, hunsafe⟩

theorem AddConstants.ofConstructorList
    {env : Environment} {venv sourceEnv : VEnv}
    {ctors : List Constructor} {values : List VConstVal}
    (mkInfo : Nat → Constructor → ConstructorVal)
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun ctor ci' => TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
      ctors values)
    (hle : sourceEnv ≤ venv)
    (hlevelParams : ∀ i ctor, (mkInfo i ctor).levelParams = lparams)
    (hname : ∀ i ctor, (mkInfo i ctor).name = ctor.name)
    (htype : ∀ i ctor, (mkInfo i ctor).type = ctor.type)
    (hvisible : ∀ i ctor, safety ≤
      (if (mkInfo i ctor).isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ ctor ∈ ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    (ctors.foldlM (init := (start, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo cidx ctor)))).WF
      fun result => ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
        entries.map Prod.snd = values ∧
        AddConstants safety env venv entries result.2 outVEnv ∧
        ConstructorListEntries mkInfo start ctors entries ∧
        (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
          ∃ info : ConstructorVal,
            entry.1 = ConstantInfo.ctorInfo info) ∧
        (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
          ∀ (value : InductiveVal),
          entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing start env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons ctor ci' ctors values Hentry _ ih =>
    have hnprimHead := hnprim ctor (by simp)
    have hnprimTail : ∀ ctor ∈ ctors,
        ¬ Kernel.Environment.primitives.contains ctor.name := by
      intro ctor hctor
      exact hnprim ctor (by simp [hctor])
    rw [List.foldlM_cons]
    simpa using (checkName.WF Hvalid.tr.map_wf ctor.name allowPrimitive).bind
      fun _ hchecked => by
          rcases Lean4Lean.VerifyInductive.CheckingEnv.exists_addConst
              Hvalid.tr hchecked.1 ci'.toVConstant with
            ⟨nextVEnv, hnext⟩
          let info := mkInfo start ctor
          have htrSource : TrSourceConst venv lparams ctor.name ctor.type ci' :=
            ⟨Hentry.uvars, Hentry.name, Hentry.type.mono hle,
              Hentry.wf.mono hle⟩
          have htr : TrConstVal safety venv (.ctorInfo info) ci' :=
            Lean4Lean.VerifyInductive.TrSourceConst.ctorInfo htrSource
              (hlevelParams start ctor)
              (hname start ctor) (htype start ctor) (hvisible start ctor)
          have hwf : ci'.toVConstant.WF venv := Hentry.wf.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [info, hname start ctor, Hentry.name] using hnext
          have hfindInfo : env.find? info.name = none := by
            rw [hname start ctor]
            exact hchecked.1
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains info.name := by
            rw [hname start ctor]
            exact hnprimHead
          have HnextValid : CheckingEnv.Valid safety
              (env.add (.ctorInfo info)) nextVEnv :=
            Hvalid.add hfindInfo hnprimInfo htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih (start := start + 1) HnextValid hnextLe
            hnprimTail).mono
            fun result Hrest => by
              rcases Hrest with
                ⟨outVEnv, entries, hvalues, Hinstalled, Haligned,
                  hctor, hnind⟩
              have hvalues' :
                  (((.ctorInfo info, ci') :: entries).map Prod.snd) =
                    ci' :: values := by simp [hvalues]
              have Hinstalled' := AddConstants.cons
                (ci := .ctorInfo info) (ci' := ci') hfindInfo hnprimInfo
                htr hwf haddHead rfl Hinstalled
              exact ⟨outVEnv, (.ctorInfo info, ci') :: entries,
                hvalues', Hinstalled', .cons Haligned, by
                  intro entryInfo entryValue hentry
                  simp only [List.mem_cons] at hentry
                  rcases hentry with hhead | htail
                  · exact ⟨info, congrArg Prod.fst hhead⟩
                  · exact hctor (entryInfo, entryValue) htail, by
                  intro entryInfo entryValue hentry value
                  simp only [List.mem_cons, Prod.mk.injEq] at hentry
                  rcases hentry with ⟨rfl, rfl⟩ | htail
                  · simp
                  · exact hnind (entryInfo, entryValue) htail value⟩

/-- The outer mutual-family fold concatenates the independently verified
constructor batches in the same family-major order as
`VInductDecl.constructorConstants`. -/
theorem AddConstants.ofConstructorTypes
    {env : Environment} {venv sourceEnv : VEnv}
    {types : List InductiveType} {targets : List VInductiveType}
    (mkInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun source target => List.Forall₂
        (fun ctor ci' =>
          TrSourceConst sourceEnv lparams ctor.name ctor.type ci')
        source.ctors target.ctors)
      types targets)
    (hle : sourceEnv ≤ venv)
    (hlevelParams : ∀ owner i ctor,
      (mkInfo owner i ctor).levelParams = lparams)
    (hname : ∀ owner i ctor, (mkInfo owner i ctor).name = ctor.name)
    (htype : ∀ owner i ctor, (mkInfo owner i ctor).type = ctor.type)
    (hvisible : ∀ owner i ctor, safety ≤
      (if (mkInfo owner i ctor).isUnsafe then
        DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ owner ∈ types, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    (types.foldlM (init := env) fun
        (env : Environment) (owner : InductiveType) => do
      let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
          (state : Nat × Environment) (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
      pure env).WF fun outEnv =>
        ∃ outVEnv : VEnv,
          ∃ entries : List (ConstantInfo × VConstVal),
          entries.map Prod.snd =
            targets.flatMap (fun target : VInductiveType => target.ctors) ∧
          AddConstants safety env venv entries outEnv outVEnv ∧
          ConstructorTypeEntries mkInfo types entries ∧
          (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
            ∃ info : ConstructorVal,
              entry.1 = ConstantInfo.ctorInfo info) ∧
          (∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
            ∀ (value : InductiveVal),
            entry.1 ≠ ConstantInfo.inductInfo value) := by
  induction Hentries generalizing env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, [], rfl, .nil, .nil, by simp, by simp⟩
  | @cons owner target types targets Hhead _ ih =>
    have hnprimHead : ∀ ctor ∈ owner.ctors,
        ¬ Kernel.Environment.primitives.contains ctor.name := by
      intro ctor hctor
      exact hnprim owner (by simp) ctor hctor
    have hnprimTail : ∀ owner ∈ types, ∀ ctor ∈ owner.ctors,
        ¬ Kernel.Environment.primitives.contains ctor.name := by
      intro owner howner ctor hctor
      exact hnprim owner (by simp [howner]) ctor hctor
    rw [List.foldlM_cons]
    let Hinner := AddConstants.ofConstructorList
      (start := 0) (allowPrimitive := allowPrimitive)
      (mkInfo owner) Hvalid Hhead hle
      (hlevelParams owner) (hname owner) (htype owner) (hvisible owner)
      hnprimHead
    simpa using Hinner.bind fun result Hresult => by
      rcases Hresult with
        ⟨middleVEnv, headEntries, hheadValues, HheadInstalled,
          HheadAligned, hheadCtor, hheadNind⟩
      have validInstalled : ∀ {priorEnv nextEnv : Environment}
          {priorVEnv nextVEnv : VEnv} {entries},
          AddConstants safety priorEnv priorVEnv entries nextEnv nextVEnv →
          CheckingEnv.Valid safety priorEnv priorVEnv →
          CheckingEnv.Valid safety nextEnv nextVEnv := by
        intro priorEnv nextEnv priorVEnv nextVEnv entries Hinstalled Hprior
        induction Hinstalled with
        | nil => exact Hprior
        | cons hn hnprim htr hwf hadd hdelta _ ih =>
          exact ih (Hprior.add hn hnprim htr.1 hwf hadd hdelta)
      have HnextValid : CheckingEnv.Valid safety result.2 middleVEnv := by
        exact validInstalled HheadInstalled Hvalid
      have installedLe : ∀ {priorEnv nextEnv : Environment}
          {priorVEnv nextVEnv : VEnv} {entries},
          AddConstants safety priorEnv priorVEnv entries nextEnv nextVEnv →
          priorVEnv ≤ nextVEnv := by
        intro priorEnv nextEnv priorVEnv nextVEnv entries Hinstalled
        induction Hinstalled with
        | nil => exact VEnv.LE.rfl
        | cons _ _ _ _ hadd _ _ ih =>
          exact (VEnv.addConst_le hadd).trans ih
      have hnextLe : sourceEnv ≤ middleVEnv :=
        hle.trans (installedLe HheadInstalled)
      exact (ih HnextValid hnextLe hnprimTail).mono
        fun outEnv Htail => by
          rcases Htail with
            ⟨finalVEnv, tailEntries, htailValues, HtailInstalled,
              HtailAligned, htailCtor, htailNind⟩
          have hvalues : (headEntries ++ tailEntries).map Prod.snd =
              (target :: targets).flatMap
                (fun target : VInductiveType => target.ctors) := by
            simp [hheadValues, htailValues]
          exact ⟨finalVEnv, headEntries ++ tailEntries, hvalues,
            HheadInstalled.append HtailInstalled,
            .cons HheadAligned HtailAligned, by
              intro entryInfo entryValue hentry
              rcases List.mem_append.mp hentry with hhead | htail
              · exact hheadCtor (entryInfo, entryValue) hhead
              · exact htailCtor (entryInfo, entryValue) htail, by
              intro entryInfo entryValue hentry value
              rcases List.mem_append.mp hentry with hhead | htail
              · exact hheadNind (entryInfo, entryValue) hhead value
              · exact htailNind (entryInfo, entryValue) htail value⟩

theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.production
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    addConstants env (entries.map Prod.fst) = outEnv := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa [addConstants] using ih

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConstVals (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConstVals]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConstVals, ← htr.2, hadd]
    exact ih

theorem AddConstants.existsEntryOfValue
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalue : value ∈ entries.map Prod.snd) :
    ∃ info, (info, value) ∈ entries := by
  rcases List.mem_map.mp hvalue with ⟨⟨info, entryValue⟩, hentry, heq⟩
  simp only at heq
  subst entryValue
  exact ⟨info, hentry⟩

inductive InductiveHeaderEntries :
    List InductiveVal → List (ConstantInfo × VConstVal) → Prop
  | nil : InductiveHeaderEntries [] []
  | cons : InductiveHeaderEntries infos entries →
      InductiveHeaderEntries (info :: infos)
        ((.inductInfo info, value) :: entries)

theorem InductiveHeaderEntries.ofZip
    (hlength : infos.length = values.length) :
    InductiveHeaderEntries infos
      (List.zip (infos.map (fun info => .inductInfo info)) values) := by
  induction infos generalizing values with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons value values => simp at hlength
  | cons info infos ih =>
    cases values with
    | nil => simp at hlength
    | cons value values =>
      simp only [List.length_cons] at hlength
      exact .cons (ih (by omega))

theorem InductiveHeaderEntries.findInfo
    (H : InductiveHeaderEntries infos entries) (hinfo : info ∈ infos) :
    ∃ value, (.inductInfo info, value) ∈ entries := by
  cases H with
  | nil => simp at hinfo
  | cons Htail =>
    rename_i tail entries headValue
    simp only [List.mem_cons] at hinfo
    rcases hinfo with rfl | htail
    · exact ⟨headValue, by simp⟩
    · rcases Htail.findInfo htail with ⟨value, hmem⟩
      exact ⟨value, by simp [hmem]⟩

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConstVals_le H.abstract

/-- Refinement of the explicit production recursor loop, parameterized only
by translation of each generated recursor telescope. Everything else—rule
coverage and state, source name checking, abstract extension, installation
order, and owner indexing—is discharged by the loop induction. -/
theorem AddInductive.declareRecursors.loop.WF
    {sourceVEnv currentVEnv envTypes envCtors : VEnv}
    {decl : VInductDecl}
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (numMinors numMotives : Nat) (all : List Name)
    (k isUnsafe : Bool) (allowPrimitive : Bool)
    (dIdx : Nat) (hdone : dIdx ≤ indTypes.size)
    (env : Environment)
    (Hvalid : CheckingEnv.Valid c.safety env currentVEnv)
    (hle : sourceVEnv ≤ currentVEnv)
    (Htranslate : ∀ owner (howner : owner < indTypes.size)
      (rules : List RecursorRule),
      ∃ recursor : VConstVal,
        TrConstVal c.safety sourceVEnv
          (.recInfo (AddInductive.declareRecursors.recursorInfo stats
            indTypes elimLevel recInfos numMinors numMotives all c.lctx k
            isUnsafe lparams owner rules)) recursor ∧
        recursor.toVConstant.WF sourceVEnv)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors.loop stats indTypes elimLevel recInfos
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) numMinors
      numMotives all c.lctx k isUnsafe lparams allowPrimitive dIdx env
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          out.2 = recursorMinorOffset indTypes indTypes.size ∧
          Nonempty (GeneratedRecursorsRange c.safety sourceVEnv lparams
            elimLevel c stats indTypes recInfos dIdx entries) ∧
          AddConstants c.safety env currentVEnv entries out.1 outVEnv := by
  rw [AddInductive.declareRecursors.loop]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have Hrules := Hcard.mkRecRulesAtOffsetWF Hdecl elimLevel dIdx hidx c
      Hc Hbindings Hparams hnoalias
    exact Hrules.bind fun generated Hgenerated => by
      let info := AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams dIdx generated.1
      have hinfoName : info.name = Lean.mkRecName indTypes[dIdx]!.name := rfl
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.instMonadLift, ReaderT.instMonadLift, StateT.lift, bind,
        StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      have hnormalize :
          ((env.checkName info.name allowPrimitive).bind fun a =>
            Except.pure (a, generated.2)).bind (fun checked =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) checked.2 c) =
          (env.checkName info.name allowPrimitive).bind (fun _ =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) generated.2 c) := by
        cases env.checkName info.name allowPrimitive <;> rfl
      rw [hnormalize]
      have Hname := checkName.WF Hvalid.tr.map_wf info.name allowPrimitive
      exact Hname.bind fun _ Hchecked => by
          rcases Htranslate dIdx hidx generated.1 with
            ⟨recursor, HtrSource, HwfSource⟩
          rcases CheckingEnv.exists_addConst Hvalid.tr Hchecked.1
              recursor.toVConstant with ⟨nextVEnv, hadd⟩
          have Htr : TrConstVal c.safety currentVEnv (.recInfo info) recursor :=
            HtrSource.mono hle
          have Hwf : recursor.toVConstant.WF currentVEnv :=
            HwfSource.mono hle
          have hname : info.name = recursor.name := Htr.2
          have haddInfo :
              currentVEnv.addConst info.name recursor.toVConstant =
                some nextVEnv := by
            simpa [hname] using hadd
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains
                (ConstantInfo.recInfo info).name := by
            simpa [ConstantInfo.name, ConstantInfo.toConstantVal, info,
              AddInductive.declareRecursors.recursorInfo] using hnprim dIdx hidx
          have HnextValid : CheckingEnv.Valid c.safety
              (env.add (.recInfo info)) nextVEnv :=
            Hvalid.add Hchecked.1 hnprimInfo Htr.1 Hwf haddInfo rfl
          have hnextLe : sourceVEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddInfo)
          have Htail := AddInductive.declareRecursors.loop.WF Hcard Hdecl c Hc
            Hbindings Hparams hnoalias numMinors numMotives all k
            isUnsafe allowPrimitive (dIdx + 1) (by omega)
            (env.add (.recInfo info)) HnextValid hnextLe Htranslate hnprim
          rw [Hgenerated.2]
          exact Htail.mono fun out Hout => by
            rcases Hout with
              ⟨outVEnv, entries, hstate, ⟨Hrange⟩, Hinstalled⟩
            let entry : ConstantInfo × VConstVal := (.recInfo info, recursor)
            have Hentry : GeneratedRecursorEntry c.safety sourceVEnv lparams
                elimLevel c stats indTypes recInfos dIdx entry := by
              exact GeneratedRecursorEntry.ofRecursorInfo c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos numMinors
                numMotives all k isUnsafe dIdx generated.1 recursor HtrSource
                Hgenerated.1
            have Hrange' : GeneratedRecursorsRange c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hrange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero => simpa [entry] using Hentry
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using Hrange.entry i hi'
            have Hinstalled' : AddConstants c.safety env currentVEnv
                (entry :: entries) out.1 outVEnv := by
              exact AddConstants.cons Hchecked.1
                hnprimInfo Htr Hwf haddInfo rfl Hinstalled
            exact ⟨outVEnv, entry :: entries, hstate, ⟨Hrange'⟩, Hinstalled'⟩
  · rw [dif_neg hidx]
    have heq : dIdx = indTypes.size := by omega
    subst dIdx
    exact Except.WF.pure ⟨currentVEnv, [], rfl, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩,
      .nil⟩
termination_by indTypes.size - dIdx

/-- Semantic refinement of the production recursor loop.  In addition to
the ordinary generated-entry and installation certificates, every recursor
entry retains the classifier/call trace of each generated iota rule. -/
theorem AddInductive.declareRecursors.loop.semanticWF
    {sourceVEnv currentVEnv envTypes envCtors : VEnv}
    {decl : VInductDecl}
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    {recLparams : List Name} {depth : Nat}
    (c : AddInductive.Context) (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          RecursorParamPrefix stats 0 ctor.type tail ∧
          Nonempty
            (CheckedConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (numMinors numMotives : Nat) (all : List Name)
    (k isUnsafe : Bool) (allowPrimitive : Bool)
    (dIdx : Nat) (hdone : dIdx ≤ indTypes.size)
    (env : Environment)
    (Hvalid : CheckingEnv.Valid c.safety env currentVEnv)
    (hle : sourceVEnv ≤ currentVEnv)
    (Htranslate : ∀ owner (howner : owner < indTypes.size)
      (rules : List RecursorRule),
      ∃ recursor : VConstVal,
        TrConstVal c.safety sourceVEnv
          (.recInfo (AddInductive.declareRecursors.recursorInfo stats
            indTypes elimLevel recInfos numMinors numMotives all c.lctx k
            isUnsafe lparams owner rules)) recursor ∧
        recursor.toVConstant.WF sourceVEnv)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors.loop stats indTypes elimLevel recInfos
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) numMinors
      numMotives all c.lctx k isUnsafe lparams allowPrimitive dIdx env
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          out.2 = recursorMinorOffset indTypes indTypes.size ∧
          Nonempty (GeneratedRecursorsRange c.safety sourceVEnv lparams
            elimLevel c stats indTypes recInfos dIdx entries) ∧
          Nonempty (GeneratedRecursorRuleSemanticsRange R decl stats
            indTypes recInfos elimLevel dIdx entries) ∧
          AddConstants c.safety env currentVEnv entries out.1 outVEnv := by
  rw [AddInductive.declareRecursors.loop]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have Hrules := Hcard.mkRecRulesAtOffsetSemanticWF Hdecl elimLevel dIdx
      hidx R Hstats hwhnf hconsume hlit hctx hproj Hbindings Hparams
      hnoalias hparameterUp (Hseed dIdx hidx)
    exact Hrules.bind fun generated Hgenerated => by
      let info := AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams dIdx generated.1
      have hinfoName : info.name = Lean.mkRecName indTypes[dIdx]!.name := rfl
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.instMonadLift, ReaderT.instMonadLift, StateT.lift, bind,
        StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      have hnormalize :
          ((env.checkName info.name allowPrimitive).bind fun a =>
            Except.pure (a, generated.2)).bind (fun checked =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) checked.2 c) =
          (env.checkName info.name allowPrimitive).bind (fun _ =>
              AddInductive.declareRecursors.loop stats indTypes elimLevel
                recInfos (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) numMinors numMotives all c.lctx
                k isUnsafe lparams allowPrimitive (dIdx + 1)
                (AddInductive.addConstant env (.recInfo info)) generated.2 c) := by
        cases env.checkName info.name allowPrimitive <;> rfl
      rw [hnormalize]
      have Hname := checkName.WF Hvalid.tr.map_wf info.name allowPrimitive
      exact Hname.bind fun _ Hchecked => by
          rcases Htranslate dIdx hidx generated.1 with
            ⟨recursor, HtrSource, HwfSource⟩
          rcases CheckingEnv.exists_addConst Hvalid.tr Hchecked.1
              recursor.toVConstant with ⟨nextVEnv, hadd⟩
          have Htr : TrConstVal c.safety currentVEnv (.recInfo info) recursor :=
            HtrSource.mono hle
          have Hwf : recursor.toVConstant.WF currentVEnv :=
            HwfSource.mono hle
          have hname : info.name = recursor.name := Htr.2
          have haddInfo :
              currentVEnv.addConst info.name recursor.toVConstant =
                some nextVEnv := by
            simpa [hname] using hadd
          have hnprimInfo :
              ¬ Kernel.Environment.primitives.contains
                (ConstantInfo.recInfo info).name := by
            simpa [ConstantInfo.name, ConstantInfo.toConstantVal, info,
              AddInductive.declareRecursors.recursorInfo] using hnprim dIdx hidx
          have HnextValid : CheckingEnv.Valid c.safety
              (env.add (.recInfo info)) nextVEnv :=
            Hvalid.add Hchecked.1 hnprimInfo Htr.1 Hwf haddInfo rfl
          have hnextLe : sourceVEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddInfo)
          have Htail := AddInductive.declareRecursors.loop.semanticWF Hcard
            Hdecl c R Hstats hwhnf hconsume hlit hctx hproj Hbindings
            Hparams hnoalias hparameterUp Hseed numMinors numMotives all k isUnsafe
            allowPrimitive (dIdx + 1) (by omega)
            (env.add (.recInfo info)) HnextValid hnextLe Htranslate hnprim
          rw [Hgenerated.2]
          exact Htail.mono fun out Hout => by
            rcases Hout with
              ⟨outVEnv, entries, hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
                Hinstalled⟩
            let entry : ConstantInfo × VConstVal := (.recInfo info, recursor)
            have Hentry : GeneratedRecursorEntry c.safety sourceVEnv lparams
                elimLevel c stats indTypes recInfos dIdx entry := by
              exact GeneratedRecursorEntry.ofRecursorInfo c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos numMinors
                numMotives all k isUnsafe dIdx generated.1 recursor HtrSource
                Hgenerated.1.bound
            have Hrange' : GeneratedRecursorsRange c.safety sourceVEnv
                lparams elimLevel c stats indTypes recInfos dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hrange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero => simpa [entry] using Hentry
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using Hrange.entry i hi'
            have HsemRange' : GeneratedRecursorRuleSemanticsRange R decl
                stats indTypes recInfos elimLevel dIdx
                (entry :: entries) := by
              refine {
                covered := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    HsemRange.covered
                entry := ?_ }
              intro i hi
              cases i with
              | zero =>
                exact ⟨info, by simp [entry], by
                  simpa [info, AddInductive.declareRecursors.recursorInfo]
                    using Hgenerated.1⟩
              | succ i =>
                have hi' : i < entries.length := by simpa using hi
                simpa [Nat.add_assoc, Nat.add_comm 1 i] using
                  HsemRange.entry i hi'
            have Hinstalled' : AddConstants c.safety env currentVEnv
                (entry :: entries) out.1 outVEnv := by
              exact AddConstants.cons Hchecked.1
                hnprimInfo Htr Hwf haddInfo rfl Hinstalled
            exact ⟨outVEnv, entry :: entries, hstate, ⟨Hrange'⟩,
              ⟨HsemRange'⟩, Hinstalled'⟩
  · rw [dif_neg hidx]
    have heq : dIdx = indTypes.size := by omega
    subst dIdx
    exact Except.WF.pure ⟨currentVEnv, [], rfl, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩, ⟨
      { covered := by simpa [Hcard.records] using
          (show indTypes.size = recInfos.size from by
            have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              Hdecl
            have hsize : indTypes.size = decl.types.length := by
              simpa using htypes
            rw [hsize, ← Hcard.records])
        entry := by intro i hi; simp at hi }⟩,
      .nil⟩
termination_by indTypes.size - dIdx

/-- Public recursor-declaration boundary. The executable setup is reduced to
the verified indexed loop, yielding both the complete generated-recursors
certificate and lockstep production/abstract installation. -/
theorem AddInductive.declareRecursors.bindingWF
    {envTypes envCtors : VEnv} {decl : VInductDecl}
    {currentVEnv : VEnv}
    (k : Bool)
    (Hvalid : CheckingEnv.Valid c.safety c.env currentVEnv)
    (Hcontext : BindingContextWF c)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv c.lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety currentVEnv c.lparams
            elimLevel c stats indTypes recInfos entries) ∧
          AddConstants c.safety c.env currentVEnv entries outEnv
            outVEnv := by
  unfold AddInductive.declareRecursors
  simp only [getLCtx, readThe, read, ReaderT.read]
  simp only [readThe, read, ReaderT.read, bind, ReaderT.bind]
  have Hcheck :
      (AddInductive.declareRecursors.checkRecursorTypes stats indTypes
        elimLevel recInfos (recInfos.flatMap (·.minors)).size
        (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
        c.lctx k (c.safety != .safe) c.lparams 0 c).WF fun _ =>
          RecursorTypeTranslations currentVEnv c.lparams elimLevel c
            stats indTypes recInfos := by
    simpa using
      (AddInductive.declareRecursors.checkRecursorTypes.recursorTypeTranslationsWF
        Hvalid hnotPartial stats indTypes elimLevel recInfos
        (recInfos.flatMap (·.minors)).size
        (recInfos.map (·.motive)).size
        (indTypes.map (·.name)).toList c.lctx k (c.safety != .safe)
        c.lparams)
  refine Hcheck.bind fun _ Htypes => ?_
  have Hloop := AddInductive.declareRecursors.loop.WF (elimLevel := elimLevel)
    Hcard Hdecl c
    Hcontext Hbindings Hparams hnoalias
    (recInfos.flatMap (·.minors)).size
    (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList k
    (c.safety != .safe) c.allowPrimitive 0 (by omega) c.env
    Hvalid VEnv.LE.rfl
    (Htypes.recursorInfoTranslation k) hnprim
  change ((Prod.fst <$> AddInductive.declareRecursors.loop stats indTypes
    elimLevel recInfos (recInfos.map (·.motive))
    (recInfos.flatMap (·.minors)) (recInfos.flatMap (·.minors)).size
    (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList c.lctx
    k (c.safety != .safe) c.lparams c.allowPrimitive 0 c.env 0 c).WF _)
  exact Hloop.map fun out Hout => by
    rcases Hout with
      ⟨outVEnv, entries, _hstate, ⟨Hrange⟩, Hinstalled⟩
    have hsize : entries.length = recInfos.size := by
      simpa using Hrange.covered
    exact ⟨outVEnv, entries, ⟨Hrange.atZero hsize⟩, Hinstalled⟩

/-- Public semantic recursor-declaration boundary.  This is the same
executable declaration pass as `bindingWF`, with the constructor-rule
semantics retained alongside the ordinary generated-recursors certificate. -/
theorem AddInductive.declareRecursors.bindingSemanticWF
    {envTypes envCtors : VEnv} {decl : VInductDecl}
    {currentVEnv : VEnv} {recLparams : List Name} {depth : Nat}
    (k : Bool)
    (Hvalid : CheckingEnv.Valid c.safety c.env currentVEnv)
    (Hcontext : BindingContextWF c)
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv c.lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ owner (howner : owner < indTypes.size),
      ∀ ctor, ctor ∈ indTypes[owner]!.ctors →
        ∃ tail tailTarget introTarget,
          RecursorParamPrefix stats 0 ctor.type tail ∧
          Nonempty
            (CheckedConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS R.venv recLparams R.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
            tailTarget)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety currentVEnv c.lparams
            elimLevel c stats indTypes recInfos entries) ∧
          Nonempty (GeneratedRecursorRuleSemanticsRange R decl stats
            indTypes recInfos elimLevel 0 entries) ∧
          AddConstants c.safety c.env currentVEnv entries outEnv
            outVEnv := by
  unfold AddInductive.declareRecursors
  simp only [getLCtx, readThe, read, ReaderT.read]
  simp only [readThe, read, ReaderT.read, bind, ReaderT.bind]
  have Hcheck :
        (AddInductive.declareRecursors.checkRecursorTypes stats indTypes
          elimLevel recInfos (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
          c.lctx k (c.safety != .safe) c.lparams 0 c).WF fun _ =>
            RecursorTypeTranslations currentVEnv c.lparams elimLevel c
              stats indTypes recInfos := by
      simpa using
        (AddInductive.declareRecursors.checkRecursorTypes.recursorTypeTranslationsWF
          Hvalid hnotPartial stats indTypes elimLevel recInfos
          (recInfos.flatMap (·.minors)).size
          (recInfos.map (·.motive)).size
          (indTypes.map (·.name)).toList c.lctx k (c.safety != .safe)
          c.lparams)
  refine Hcheck.bind fun _ Htypes => ?_
  have Hloop := AddInductive.declareRecursors.loop.semanticWF
      (elimLevel := elimLevel) Hcard Hdecl c R Hstats hwhnf hconsume hlit
      hctx hproj Hbindings Hparams hnoalias hparameterUp Hseed
      (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList k
      (c.safety != .safe) c.allowPrimitive 0 (by omega) c.env
      Hvalid VEnv.LE.rfl
      (Htypes.recursorInfoTranslation k) hnprim
  change ((Prod.fst <$> AddInductive.declareRecursors.loop stats indTypes
      elimLevel recInfos (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) (recInfos.flatMap (·.minors)).size
      (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList c.lctx
      k (c.safety != .safe) c.lparams c.allowPrimitive 0 c.env 0 c).WF _)
  exact Hloop.map fun out Hout => by
    rcases Hout with
      ⟨outVEnv, entries, _hstate, ⟨Hrange⟩, ⟨HsemRange⟩,
        Hinstalled⟩
    have hsize : entries.length = recInfos.size := by
      simpa using Hrange.covered
    exact ⟨outVEnv, entries, ⟨Hrange.atZero hsize⟩, ⟨HsemRange⟩,
      Hinstalled⟩

/-- Full-context wrapper for callers that have semantic local-context typing,
retaining the original public interface. -/
theorem AddInductive.declareRecursors.WF
    {envTypes envCtors : VEnv} {decl : VInductDecl}
    (k : Bool)
    (Hcontext : ContextWF c)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv c.lparams nparams
      indTypes.toList sourceIsUnsafe decl envTypes envCtors)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.declareRecursors stats indTypes elimLevel recInfos k c).WF
      fun outEnv =>
        ∃ outVEnv : VEnv,
        ∃ entries : List (ConstantInfo × VConstVal),
          Nonempty (GeneratedRecursors c.safety Hcontext.venv c.lparams
            elimLevel c stats indTypes recInfos entries) ∧
          AddConstants c.safety c.env Hcontext.venv entries outEnv
            outVEnv :=
  AddInductive.declareRecursors.bindingWF k Hcontext.checking
    Hcontext.toBindingContextWF Hcard Hdecl Hbindings Hparams hnoalias
    hnotPartial
    hnprim


end VerifyInductive
end Lean4Lean
