import Lean4Lean.Verify.Inductive.Recursor.Rules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace mkRecRules.loopU

/-- Binder-aware refinement of the production recursive-result loop. -/
theorem boundGeneratedCalls
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hprefix : BoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls c u v i)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
        let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
          motives) minors) itIndices
        return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => Nonempty (BoundGeneratedRecursiveCall indTypes stats
            motives minors lvls c u[i] value)) := by
      refine mkRecInfos.loopUArgs.resultBindings
        (Q := fun value => Nonempty (BoundGeneratedRecursiveCall indTypes
          stats motives minors lvls c u[i] value)) u[i] buildCall c Hc ?_
      intro uiTy xs c' Hc' Hxs Hle
      unfold buildCall
      cases hvalid : AddInductive.isValidIndApp? stats uiTy with
      | none =>
        simp only [hvalid, bind, Except.bind]
        exact Except.WF.throw
      | some target =>
        simp only [hvalid, bind, Except.bind]
        refine Except.WF.pure ⟨{
          exposedType := uiTy
          ownerIdx := target
          owner_valid := hvalid
          localArgs := xs
          current := c'
          current_wf := Hc'
          current_extends := Hle
          arguments_bound := Hxs
          value_eq := ?_ }⟩
        simp [AddInductive.getIIndices, hvalid]
    exact hval.bind fun value Hvalue => by
      rcases Hvalue with ⟨Hvalue⟩
      exact boundGeneratedCalls Hc
        (Hprefix.push hnext Hvalue) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

/-- Semantic binder-aware refinement of the production recursive-result
loop.  Every selected source field is supplied with its translation in the
root recursor context; `loopUArgs` then reconstructs and couples the complete
recursive domain to the exact generated call at the same array position. -/
theorem semanticBoundGeneratedCalls
    {alpha : Type} {Q : alpha → Prop}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ i (hi : i < u.size),
      ∃ fv fieldTarget,
        u[i] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (HfieldScope : ∀ i (hi : i < u.size) {fv},
      u[i] = .fvar fv → P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {k : Array Expr → AddInductive.M alpha}
    (Hprefix : SemanticBoundGeneratedRecursiveCalls indTypes stats motives
      minors lvls R decl depth P u v i)
    (Hk : ∀ v,
      SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
        lvls R decl depth P u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    rcases Hfields i hnext with ⟨fv, fieldTarget, hfield, Hfield⟩
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      mkRecRules.buildRecursiveCall indTypes stats motives minors lvls u[i]
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => ∃ S :
            SemanticBoundGeneratedRecursiveCall indTypes stats motives
              minors lvls R decl depth u[i] value,
            S.rootScope = P) := by
      rw [hfield]
      simpa only [buildCall, hfield] using
        mkRecRules.boundGeneratedCallSemantic indTypes stats motives minors
        lvls R Hstats hwhnf hconsume hlit hctx hproj fv Hfield
        (HfieldScope i hnext hfield) hrootUp
    exact hval.bind fun value Hvalue => by
      rcases Hvalue with ⟨Hvalue, hscope⟩
      exact semanticBoundGeneratedCalls R Hstats hwhnf hconsume hlit hctx
        hproj Hfields HfieldScope hrootUp
          (Hprefix.push hnext Hvalue hscope) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.boundGeneratedCallsFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.boundGeneratedCalls Hc
    (BoundGeneratedRecursiveCalls.empty
      indTypes stats motives minors lvls c u) Hk

theorem mkRecRules.loopU.semanticBoundGeneratedCallsFromEmpty
    {alpha : Type} {Q : alpha → Prop}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ i (hi : i < u.size),
      ∃ fv fieldTarget,
        u[i] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (HfieldScope : ∀ i (hi : i < u.size) {fv},
      u[i] = .fvar fv → P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {k : Array Expr → AddInductive.M alpha}
    (Hk : ∀ v,
      SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
        lvls R decl depth P u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.semanticBoundGeneratedCalls R Hstats hwhnf hconsume hlit
    hctx hproj Hfields HfieldScope hrootUp
    (SemanticBoundGeneratedRecursiveCalls.empty indTypes stats motives minors
      lvls R decl depth P u) Hk

namespace mkRecInfos.loopCtorArgs.loop

/-- Operational binder refinement for constructor-field classification. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hbu : FreshBoundFVarArray root c bu)
    (Hu : FreshBoundFVarArray root c u)
    (Hselected : u.toList.Sublist bu.toList)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ t bu u c, BindingContextWF c →
      FreshBoundFVarArray root c bu → FreshBoundFVarArray root c u →
      u.toList.Sublist bu.toList → BindingContextLE root c →
      (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih Hc Hbu Hu Hselected Hroot
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotations
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF
            (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        let Hc' := Hc.withLocalDecl name dom.consumeTypeAnnotations bi
        let hstep := BindingContextLE.withLocalDecl c Hc name
          dom.consumeTypeAnnotations bi
        cases selected with
        | none =>
          have hselected' : u.toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using Hselected.trans
              (List.sublist_append_left bu.toList
                [.fvar ⟨c.ngen.curr⟩])
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            (Hu.weaken name dom.consumeTypeAnnotations bi)
            hselected'
            (Hroot.trans hstep)
        | some target =>
          have hselected' : (u.push (.fvar ⟨c.ngen.curr⟩)).toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using
              Hselected.append_right [.fvar ⟨c.ngen.curr⟩]
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            (Hu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            hselected'
            (Hroot.trans hstep)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ Hc Hbu Hu Hselected Hroot

end mkRecInfos.loopCtorArgs.loop

theorem mkRecInfos.loopCtorArgs.resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hk : ∀ t bu u c', BindingContextWF c' →
      FreshBoundFVarArray c c' bu → FreshBoundFVarArray c c' u →
      u.toList.Sublist bu.toList → BindingContextLE c c' →
      (k t bu u c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.resultBindings stats k Hc
    (FreshBoundFVarArray.empty c) (FreshBoundFVarArray.empty c)
    .slnil (BindingContextLE.refl c) Hk

namespace mkRecRules.loopCtors

/-- Semantic refinement of one exact production rule-generation iteration.
The constructor-field traversal supplies the ordered recursive-domain trace;
the recursive-call traversal then couples every generated IH application to
that trace.  The result retains both the existing binder-aware operational
certificate and the new pointwise semantic payload. -/
theorem oneRuleSemantics
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx ownerIdx : Nat)
    {recLparams : List Name} {depth : Nat}
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tail : Expr} {tailTarget introTarget : VExpr}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : RecursorParamPrefix stats 0 ctor.type tail)
    (htailFVars : tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params))
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (howner : ownerIdx < decl.types.length)
    (Hnormal : CheckedConstructorOwnerNormalForm stats ownerIdx tail)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (HtailType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
      tailTarget)
    (Hintro : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN (.const ctor.name stats.levels) stats.params) introTarget)
    (HintroType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      introTarget tailTarget)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminor : minorIdx < minors.size) :
    (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type
      (fun _ allArgs recursiveArgs =>
        AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
          recursiveArgs 0 #[] fun recursiveResults => do
            let lctx ← getLCtx
            let rule : RecursorRule := {
              ctor := ctor.name
              nfields := allArgs.size
              rhs := lctx.mkLambda stats.params <|
                lctx.mkLambda motives <| lctx.mkLambda minors <|
                lctx.mkLambda allArgs <|
                mkAppN (mkAppN minors[minorIdx]! allArgs)
                  recursiveResults }
            return (rule, minorIdx + 1)) c).WF fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1 := by
  let process : Expr → Array Expr → Array Expr →
      AddInductive.M (RecursorRule × Nat) := fun _ allArgs recursiveArgs =>
    AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      recursiveArgs 0 #[] fun recursiveResults => do
        let lctx ← getLCtx
        let rule : RecursorRule := {
          ctor := ctor.name
          nfields := allArgs.size
          rhs := lctx.mkLambda stats.params <|
            lctx.mkLambda motives <| lctx.mkLambda minors <|
            lctx.mkLambda allArgs <|
            mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults }
        return (rule, minorIdx + 1)
  change (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type process c).WF _
  apply mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent
    (Q := fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1)
    stats ctor.type tail
      (mkAppN (.const ctor.name stats.levels) stats.params)
      process c R Hstats hprefix hwhnf hconsume hlit hctx hproj Htail
      HtailType htailFVars hparameterUp Hintro HintroType
  intro current Rargs terminal terminalTarget appliedTarget allArgs
    recursiveArgs fields positions args hterminalNonforall Hterminal HterminalType
    Hselection Hdecisions Hrecursive HfieldsRecent _Hopening HfieldTargetDefEq
    _HterminalScope
    _HfieldParameterUp _HintroApplied _HintroAppliedType
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  have hvalidIdx : AddInductive.isValidIndAppIdx stats terminal ownerIdx =
      true :=
    Hnormal.validOfOpening _Hopening Hparams
      HfieldsRecent.toFreshBoundFVarArray
      (Hstats.indConstAt howner) hterminalNonforall
  rcases checkPositivityStep.isValidIndApp?_exists_of_valid hvalidIdx
      (Hstats.indConstAt howner) with ⟨selectedOwner, hselectedOwner⟩
  have hselectedStats :=
    checkPositivityStep.isValidIndApp?_some hselectedOwner
  have hselectedOwnerLt : selectedOwner < decl.types.length := by
    rw [← Hstats.types_size]
    exact hselectedStats.1
  let buildRule : Array Expr →
      AddInductive.M (RecursorRule × Nat) := fun recursiveResults => do
    let lctx ← getLCtx
    let rule : RecursorRule := {
      ctor := ctor.name
      nfields := allArgs.size
      rhs := lctx.mkLambda stats.params <|
        lctx.mkLambda motives <| lctx.mkLambda minors <|
        lctx.mkLambda allArgs <|
        mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults }
    return (rule, minorIdx + 1)
  change (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
    recursiveArgs 0 #[] buildRule current).WF _
  apply mkRecRules.loopU.semanticBoundGeneratedCallsFromEmpty
    (Q := fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1)
    (indTypes := indTypes) (stats := stats) (motives := motives)
    (minors := minors) (lvls := lvls) (u := recursiveArgs)
    (k := buildRule) (c := current) (decl := decl) Rargs
    HstatsArgs hwhnf hconsume hlit hctxArgs hproj
    (Hselection.selectedFVars
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray Hrecursive)
    (P := fun fv => fv ∈ _Hopening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params)
    (by
      intro i hi fv hfv
      have hselectedExpr : Expr.fvar fv ∈ recursiveArgs.toList := by
        rw [← hfv]
        exact Array.getElem_mem_toList hi
      have hallExpr : Expr.fvar fv ∈ allArgs.toList :=
        Hselection.toSource.selectedSublist.subset hselectedExpr
      have hallFv : fv ∈
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars := by
        rw [HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.expressions]
          at hallExpr
        simpa using hallExpr
      exact Or.inl (by
        rw [_Hopening.fvars_eq_bound
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
        exact hallFv))
    _HfieldParameterUp
  intro recursiveResults Hcalls
  simp only [buildRule, getLCtx, readThe, read, ReaderT.read]
  let Hparams' := Hparams.mono HfieldsRecent.contextLE
  let Hmotives' := Hmotives.mono HfieldsRecent.contextLE
  let Hminors' := Hminors.mono HfieldsRecent.contextLE
  have HouterNodup' :
      ((Hparams'.fvars ++ Hmotives'.fvars) ++ Hminors'.fvars).Nodup := by
    change ((Hparams.fvars ++ Hmotives.fvars) ++ Hminors.fvars).Nodup
    exact HouterNodup
  have hselected : recursiveArgs.toList.Sublist allArgs.toList :=
    Hselection.toSource.selectedSublist
  rcases BoundFVarArray.ofSublist
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray hselected with
    ⟨HrecursiveBound⟩
  have hrecursiveNodup : HrecursiveBound.fvars.Nodup := by
    have hallExpr : allArgs.toList.Nodup := by
      rw [HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.expressions]
      exact List.Pairwise.map Expr.fvar
        (fun _ _ hne heq => hne (Expr.fvar.inj heq))
        HfieldsRecent.toFreshBoundFVarArray.nodup
    have hrecursiveExpr := hallExpr.sublist hselected
    rw [HrecursiveBound.expressions] at hrecursiveExpr
    change List.Pairwise (fun a b : Expr => a ≠ b)
      (HrecursiveBound.fvars.map Expr.fvar) at hrecursiveExpr
    rw [List.pairwise_map] at hrecursiveExpr
    change List.Pairwise (fun a b : FVarId => a ≠ b)
      HrecursiveBound.fvars
    exact hrecursiveExpr.imp fun hneq heq =>
      hneq (congrArg Expr.fvar heq)
  let Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx {
        ctor := ctor.name
        nfields := allArgs.size
        rhs := current.lctx.mkLambda stats.params <|
          current.lctx.mkLambda motives <| current.lctx.mkLambda minors <|
          current.lctx.mkLambda allArgs <|
          mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults } := {
    root := current
    root_wf := Rargs.toBindingContextWF
    target := terminal
    allArgs := allArgs
    recursiveArgs := recursiveArgs
    recursiveResults := recursiveResults
    minor_valid := hminor
    params_bound := Hparams'
    motives_bound := Hmotives'
    minors_bound := Hminors'
    outer_binders_nodup := HouterNodup'
    all_args_bound :=
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    recursive_args_bound := HrecursiveBound
    recursive_args_sublist := hselected
    all_args_nodup := HfieldsRecent.toFreshBoundFVarArray.nodup
    recursive_args_nodup := hrecursiveNodup
    all_args_outer_fresh := by
      intro fv hfv houter
      apply HfieldsRecent.toFreshBoundFVarArray.fresh fv hfv
      rcases List.mem_append.mp houter with hpm | hminor
      · rcases List.mem_append.mp hpm with hparam | hmotive
        · exact Hparams.members fv hparam
        · exact Hmotives.members fv hmotive
      · exact Hminors.members fv hminor
    recursive_calls := Hcalls.bound
    ctor_eq := rfl
    fields_eq := rfl
    rhs_eq := rfl }
  let Hsemantic : Hrule.Semantics R decl ownerIdx := {
    depth := depth + allArgs.size
    context := Rargs
    fieldRoot := c
    fieldRootContext := R
    fieldRootExtension := .refl R
    fieldRoot_vlctx := rfl
    fieldsRecent := HfieldsRecent
    parameterTail := tail
    parameterPrefix := hprefix
    parameterTail_fvars := htailFVars
    parameterTarget := tailTarget
    parameterTranslation := Htail
    parameterType := HtailType
    fieldOpening := _Hopening
    fieldParameterUp := by
      rw [_Hopening.fvars_eq_bound
        HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at _HfieldParameterUp
      exact _HfieldParameterUp
    context_venv := HfieldsRecent.venv_eq
    validStats := HstatsArgs
    ownerIdx := selectedOwner
    owner_lt := hselectedOwnerLt
    expected_owner_lt := howner
    expected_target_valid := hvalidIdx
    targetTarget := terminalTarget
    target_not_forall := hterminalNonforall
    target_translation := Hterminal
    target_type := HterminalType
    fieldTargetDefEq := HfieldTargetDefEq
    constructorTarget := appliedTarget
    constructor_translation := by
      simpa [BoundGeneratedRecursorRule.sourceConstructorMajor, mkAppN] using
        _HintroApplied
    constructor_typing := _HintroAppliedType
    target_valid := hselectedOwner
    validated := HstatsArgs.validatedIndAppAt Hterminal hselectedOwner
      hselectedOwnerLt hlit hctxArgs hproj
    fields := fields
    selection := Hselection
    decisionPositions := positions
    decisions := Hdecisions
    calls := Hcalls }
  apply Except.WF.pure
  refine Exists.intro Hrule ?_
  exact And.intro (Nonempty.intro Hsemantic) rfl

/-- Semantic traversal of a complete constructor batch.  It follows the
production accumulator and minor-state equations exactly, while obtaining
each constructor seed from the earlier checker certificate. -/
theorem semanticGeneratedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule) (start ownerIdx : Nat)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (howner : ownerIdx < decl.types.length)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (hminorsRoom : start + ctors.length ≤ minors.size)
    (Hseed : ∀ ctor, ctor ∈ ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats ownerIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          SemanticBoundGeneratedRecursorRules indTypes stats motives minors
            lvls R decl ownerIdx ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      exact ⟨[], by simp, .nil, by simp⟩
  | cons ctor ctors ih =>
      rcases Hseed ctor (by simp) with
        ⟨tail, tailTarget, introTarget, Hprefix, ⟨Hnormal⟩, HtailFVars,
          Htail, HtailType, Hintro, HintroType⟩
      rw [AddInductive.mkRecRules.loopCtors]
      have Hone := oneRuleSemantics indTypes stats motives minors lvls ctor
        start ownerIdx R Hstats Hprefix HtailFVars hparameterUp howner Hnormal hwhnf
        hconsume hlit hctx hproj Htail
        HtailType Hintro HintroType Hparams Hmotives Hminors HouterNodup
        (by simp at hminorsRoom; omega)
      exact Hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, Hsemantic, hnext⟩
        have HtailSeed : ∀ nextCtor, nextCtor ∈ ctors →
            ∃ tail tailTarget introTarget,
              RecursorParamPrefix stats 0 nextCtor.type tail ∧
              Nonempty
                (CheckedConstructorOwnerNormalForm stats ownerIdx tail) ∧
              tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
              TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
              R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
                tailTarget ∧
              TrExprS R.venv recLparams R.mlctx.vlctx
                (mkAppN (.const nextCtor.name stats.levels) stats.params)
                introTarget ∧
              R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
                introTarget tailTarget := by
          intro nextCtor hmem
          exact Hseed nextCtor (by simp [hmem])
        have hminorsRoom' : out.2 + ctors.length ≤ minors.size := by
          rw [hnext]
          simp at hminorsRoom ⊢
          omega
        have Htail := ih (acc := acc.push out.1) (start := out.2)
          hminorsRoom' HtailSeed
        exact Htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, ?_, ?_⟩
          · simpa [hout]
          · exact SemanticBoundGeneratedRecursorRules.cons Hrule Hsemantic
              (by simpa [hnext] using Hgenerated)
          · simp at hend ⊢
            omega

/-- The complete rule traversal retains the constructor-field binding context
and the bound recursive-call evidence for every emitted rule. -/
theorem boundGeneratedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule)
    (start : Nat) (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          BoundGeneratedRecursorRules indTypes stats motives minors lvls
            ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start c with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      refine ⟨[], ?_, .nil, by simp⟩
      simp
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecRules.loopCtors]
      have hone :
          ((fun minorIdx => AddInductive.mkRecInfos.loopCtorArgs stats
            ctor.type fun _ bu u =>
              AddInductive.mkRecRules.loopU indTypes stats motives minors
                lvls u 0 #[] fun v => do
                  let lctx ← getLCtx
                  let rule := {
                    ctor := ctor.name
                    nfields := bu.size
                    rhs := lctx.mkLambda stats.params <|
                      lctx.mkLambda motives <| lctx.mkLambda minors <|
                      lctx.mkLambda bu <|
                      mkAppN (mkAppN minors[minorIdx]! bu) v }
                  return (rule, minorIdx + 1)) start c).WF fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1 := by
        dsimp only
        apply mkRecInfos.loopCtorArgs.resultBindings stats ctor.type
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (k := fun _ bu u =>
            AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
              u 0 #[] fun v => do
                let lctx ← getLCtx
                let rule : RecursorRule := {
                  ctor := ctor.name
                  nfields := bu.size
                  rhs := lctx.mkLambda stats.params <|
                    lctx.mkLambda motives <| lctx.mkLambda minors <|
                    lctx.mkLambda bu <|
                    mkAppN (mkAppN minors[start]! bu) v }
                return (rule, start + 1))
          (c := c) (Hc := Hc)
        intro target bu u c' Hc' Hbu Hu hselected hroot
        let buildRule : Array Expr →
            AddInductive.M (RecursorRule × Nat) := fun v => do
          let lctx ← getLCtx
          let rule := {
            ctor := ctor.name
            nfields := bu.size
            rhs := lctx.mkLambda stats.params <|
              lctx.mkLambda motives <| lctx.mkLambda minors <|
              lctx.mkLambda bu <|
              mkAppN (mkAppN minors[start]! bu) v }
          return (rule, start + 1)
        change (AddInductive.mkRecRules.loopU indTypes stats motives minors
          lvls u 0 #[] buildRule c').WF _
        apply mkRecRules.loopU.boundGeneratedCallsFromEmpty
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (indTypes := indTypes) (stats := stats) (motives := motives)
          (minors := minors) (lvls := lvls) (u := u) (k := buildRule)
          (c := c') Hc'
        intro v Hcalls
        simp only [buildRule, getLCtx, readThe, read, ReaderT.read]
        refine Except.WF.pure ⟨?_, rfl⟩
        let Hparams' := Hparams.mono hroot
        let Hmotives' := Hmotives.mono hroot
        let Hminors' := Hminors.mono hroot
        have HouterNodup' :
            ((Hparams'.fvars ++ Hmotives'.fvars) ++
              Hminors'.fvars).Nodup := by
          change ((Hparams.fvars ++ Hmotives.fvars) ++
            Hminors.fvars).Nodup
          exact HouterNodup
        exact ⟨{
          root := c'
          root_wf := Hc'
          target := target
          allArgs := bu
          recursiveArgs := u
          recursiveResults := v
          minor_valid := by simp at hminorsRoom; omega
          params_bound := Hparams'
          motives_bound := Hmotives'
          minors_bound := Hminors'
          outer_binders_nodup := HouterNodup'
          all_args_bound := Hbu.toBoundFVarArray
          recursive_args_bound := Hu.toBoundFVarArray
          recursive_args_sublist := hselected
          all_args_nodup := Hbu.nodup
          recursive_args_nodup := Hu.nodup
          all_args_outer_fresh := by
            intro fv hfv houter
            apply Hbu.fresh fv hfv
            rcases List.mem_append.mp houter with hpm | hminor
            · rcases List.mem_append.mp hpm with hparam | hmotive
              · exact Hparams.members fv hparam
              · exact Hmotives.members fv hmotive
            · exact Hminors.members fv hminor
          recursive_calls := Hcalls
          ctor_eq := rfl
          fields_eq := rfl
          rhs_eq := rfl }⟩
      exact hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, hnext⟩
        have htail := ih (acc := acc.push out.1)
          (start := out.2) (c := c) Hc Hparams Hmotives Hminors
            HouterNodup (by simp at hminorsRoom; omega)
        exact htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, .cons Hrule ?_, ?_⟩
          · simpa [hout]
          · simpa [hnext] using Hgenerated
          · simp at hend ⊢
            omega

end mkRecRules.loopCtors

/-- Public binder-aware rule-generator boundary. -/
theorem mkRecRules.boundGeneratedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + indTypes[dIdx]!.ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        BoundGeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.boundGeneratedRules indTypes stats
    motives minors (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start c Hc Hparams Hmotives Hminors
      HouterNodup hminorsRoom
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- Public semantic rule-generator boundary for one mutual-family owner. -/
theorem mkRecRules.semanticGeneratedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (howner : dIdx < decl.types.length)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (hminorsRoom : start + indTypes[dIdx]!.ctors.length ≤ minors.size)
    (Hseed : ∀ ctor, ctor ∈ indTypes[dIdx]!.ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        SemanticBoundGeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels) R decl dIdx
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.semanticGeneratedRules indTypes stats
    motives minors (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start dIdx R Hstats howner hwhnf hconsume hlit hctx
    hproj Hparams Hmotives Hminors HouterNodup hparameterUp hminorsRoom Hseed
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- One iteration of the production recursor loop consumes exactly the
constructor-sized slice assigned to its mutual-family owner. The starting
state and available room are consequences of source translation and the
`mkRecInfos` cardinality certificate, not extra executable assumptions. -/
theorem RecursorCardinalityCertificate.mkRecRulesAtOffsetWF
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (elimLevel : Level) (dIdx : Nat) (hidx : dIdx < indTypes.size)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        BoundGeneratedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors (recursorMinorOffset indTypes dIdx) out.1 ∧
        out.2 = recursorMinorOffset indTypes (dIdx + 1) := by
  have htotal :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        (recInfos.flatMap (·.minors)).size := by
    have howners :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl
    have howners' :
        (indTypes.toList.flatMap (fun type => type.ctors)).length =
          decl.ownedConstructors.length := by
      simpa [ownedConstructors, List.length_flatMap] using howners
    exact howners'.trans Hcard.minors.symm
  have hroom := recursorMinorOffset_room indTypes dIdx hidx
  rw [htotal] at hroom
  have H := mkRecRules.boundGeneratedRules indTypes elimLevel stats dIdx
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (recursorMinorOffset indTypes dIdx) c Hc Hparams Hbindings.motives
    Hbindings.flatMinors (Hbindings.outerNodup Hparams hnoalias) hroom
  exact H.mono fun out Hout => by
    refine ⟨Hout.1, ?_⟩
    rw [Hout.2, recursorMinorOffset_step indTypes dIdx hidx]

/-- Semantic strengthening of `mkRecRulesAtOffsetWF`.  Cardinality supplies
the flattened minor slice while the retained recursor context and checker
seed supply the pointwise field/call semantics. -/
theorem RecursorCardinalityCertificate.mkRecRulesAtOffsetSemanticWF
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (elimLevel : Level) (dIdx : Nat) (hidx : dIdx < indTypes.size)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
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
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ ctor, ctor ∈ indTypes[dIdx]!.ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        SemanticBoundGeneratedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) R decl dIdx
          indTypes[dIdx]!.ctors
          (recursorMinorOffset indTypes dIdx) out.1 ∧
        out.2 = recursorMinorOffset indTypes (dIdx + 1) := by
  have htotal :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        (recInfos.flatMap (·.minors)).size := by
    have howners :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl
    have howners' :
        (indTypes.toList.flatMap (fun type => type.ctors)).length =
          decl.ownedConstructors.length := by
      simpa [ownedConstructors, List.length_flatMap] using howners
    exact howners'.trans Hcard.minors.symm
  have hroom := recursorMinorOffset_room indTypes dIdx hidx
  rw [htotal] at hroom
  have howner : dIdx < decl.types.length := by
    have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
    have hsize : indTypes.size = decl.types.length := by simpa using htypes
    rwa [← hsize]
  have H := mkRecRules.semanticGeneratedRules indTypes elimLevel stats dIdx
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (recursorMinorOffset indTypes dIdx) R Hstats howner hwhnf hconsume hlit hctx
    hproj Hparams Hbindings.motives Hbindings.flatMinors
    (Hbindings.outerNodup Hparams hnoalias) hparameterUp hroom Hseed
  exact H.mono fun out Hout => by
    refine ⟨Hout.1, ?_⟩
    rw [Hout.2, recursorMinorOffset_step indTypes dIdx hidx]

/-- Binder-aware analogue of `appendGeneratedRules`. Traversal, ordering, and
flattened constructor indexing are discharged here; the remaining pointwise
premise receives all local-binding evidence needed to construct `IotaRule`. -/
theorem IotaBuildCertificate.appendBoundGeneratedRules
    (Hbuild : IotaBuildCertificate env decl block prior)
    (Hgenerated : BoundGeneratedRecursorRules
      indTypes stats motives minors lvls ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (hsemantic : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length),
      BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) sourceRules[i] →
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate env decl block (prior ++ abstractRules) := by
  apply Hbuild.append hroom
  intro i habstract
  have hsource : i < sourceRules.length := by omega
  have hctor : i < ctors.length := by
    rw [← Hgenerated.length]
    exact hsource
  rcases Hgenerated.entry i hctor hsource with ⟨Hrule⟩
  exact hsemantic i hctor hsource habstract Hrule

namespace mkRecInfos.loopU

/-- Every induction-hypothesis declaration introduced by `loopU` is retained
and appended to the certified hypothesis array. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha) {Q : alpha → Prop}
    (i : Nat) (v : Array Expr) (c : AddInductive.Context)
    (Hc : BindingContextWF c) (Hv : FreshBoundFVarArray root c v)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ outValues c, BindingContextWF c →
      FreshBoundFVarArray root c outValues →
      BindingContextLE root c →
      outValues.size = v.size + (u.size - i) →
      (k outValues c).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopU]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hviTy :
        ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
          let some itIdx := AddInductive.isValidIndApp? stats uiTy
            | throw (.other
              "recursive constructor field lost its inductive result type")
          let itIndices := uiTy.getAppArgs[stats.params.size:]
          let motiveApp := .app
            (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
          return (← getLCtx).mkForall xs motiveApp) c).WF
          (fun _ => True) := by
      intro _ _
      trivial
    refine hviTy.bind fun viTy _ => ?_
    have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
        (fun lctx => lctx = c.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName := (c.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    apply withLocalDecl.continueRaw
    refine resultBindings stats u recInfos k (i + 1)
      (v.push (.fvar ⟨c.ngen.curr⟩)) _
      (Hc.withLocalDecl vName viTy.consumeTypeAnnotations .default)
      (Hv.pushCurrent Hc Hroot vName viTy.consumeTypeAnnotations .default)
      (Hroot.trans <| BindingContextLE.withLocalDecl c Hc vName
        viTy.consumeTypeAnnotations .default) ?_
    intro outValues out Hout Hvalues HrootOut hsize
    apply Hk outValues out Hout Hvalues HrootOut
    simp only [Array.size_push] at hsize
    omega
  · rw [dif_neg hnext]
    exact Hk v c Hc Hv Hroot (by omega)
termination_by u.size - i

/-- Semantic orchestration for the induction-hypothesis loop.  The only
operation-specific premise is the pointwise typing of the exact `viTy`
computed by `loopUArgs`; once supplied, every production `withLocalDecl` is
mirrored in `RecursorContextWF`, and the continuation receives the complete
recent-binder trace.  Keeping this separate makes the dependent motive
application used for `viTy` the sole remaining local semantic obligation. -/
theorem resultSemanticBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name}
    {root current : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF current recLparams)
    (i : Nat) (v : Array Expr)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R v)
    (Horigins : RecInfoHypothesisTypeOrigins stats recInfos current u v)
    (hprocessed : v.size = i)
    (Hvi : ∀ {next : AddInductive.Context}
      (Rnext : RecursorContextWF next recLparams)
      {prior : Array Expr}
      (Hprior : RecursorRecentBoundFVarArray Rroot Rnext prior)
      (j : Nat) (hj : j < u.size),
      ((AddInductive.mkRecInfos.loopUArgs u[j] fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let motiveApp := .app
          (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[j] xs)
        return (← getLCtx).mkForall xs motiveApp) next).WF fun viTy =>
          ∃ viTarget,
            TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
              viTy.consumeTypeAnnotations viTarget ∧
            Rnext.venv.IsType recLparams.length
              Rnext.mlctx.vlctx.toCtx viTarget ∧
            Nonempty (RecInfoHypothesisTypeOrigin
              stats recInfos next u[j]! viTy))
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray Rroot Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos out u values →
      values.size = v.size + (u.size - i) →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopU]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    refine (Hvi R Hrecent i hnext).bind fun viTy HviTy => ?_
    rcases HviTy with ⟨viTarget, HviTr, HviType, HviOrigin⟩
    have hget : ((getLCtx : AddInductive.M LocalContext) current).WF
        (fun lctx => lctx = current.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName :=
      (current.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    refine withLocalDecl.recursorWF (name := vName) (bi := .default)
      R HviTr HviType ?_
    let R' := R.withLocalDecl (name := vName) (bi := .default)
      HviTr HviType
    have HviOrigin' := HviOrigin
    rw [← hprocessed] at HviOrigin'
    refine resultSemanticBindings stats u recInfos k Rroot R' (i + 1)
      (v.push (.fvar ⟨current.ngen.curr⟩))
      (Hrecent.pushCurrent vName viTy.consumeTypeAnnotations viTarget
        .default HviTr HviType)
      (Horigins.pushCurrent R.toBindingContextWF vName viTy .default
        (by rw [hprocessed]; exact hnext) HviOrigin')
      (by simp [hprocessed])
      Hvi ?_
    intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simp only [Array.size_push] at hsize
    omega
  · rw [dif_neg hnext]
    exact Hk R v Hrecent Horigins (by omega)
termination_by u.size - i

/-- Semantic refinement of the actual induction-hypothesis loop, factored
through one explicit motive-application compatibility premise.  Recursive
field translations and positivity statistics are weakened automatically
across all previously generated hypotheses; the continuation therefore sees
the exact final production context as a `RecursorContextWF`. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name}
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Hmotives : BoundFVarArray c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {base current : AddInductive.Context}
      (Rbase : RecursorContextWF base recLparams)
      (Rcurrent : RecursorContextWF current recLparams)
      {fv : FVarId} {exposedType : Expr}
      {syntaxTarget terminalTarget fieldTarget appliedTarget : VExpr}
      {args : Array Expr} {target : Nat},
      TrExprS Rbase.venv recLparams Rbase.mlctx.vlctx
        (.fvar fv) fieldTarget →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorRecentBoundFVarArray Rbase Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q := by
  refine resultSemanticBindings stats u recInfos k R R 0 #[]
    (RecursorRecentBoundFVarArray.empty R)
    (RecInfoHypothesisTypeOrigins.empty stats recInfos c u) rfl ?_ ?_
  intro next Rnext prior Hprior j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsAt := Hstats.weakenRecent Hprior
  have hctxAt : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  apply mkRecInfos.loopUArgs.inductionHypothesisTypeOrigin fv stats recInfos next
    Rnext HstatsAt hwhnf hconsume hlit hctxAt hproj HfieldAt
      (Hmotives.mono Hprior.contextExtension.contextLE) hrecords
  intro current Rcurrent exposedType syntaxTarget terminalTarget
    appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
    HappliedType hvalid
  exact Happ Rnext Rcurrent HfieldAt Hexposed Hdefeq Hterminal Hargs
    Happlied HappliedType hvalid
  · intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simpa using hsize

/-- Close the semantic induction-hypothesis loop from the retained
target-indexed motive contracts.  Unlike `resultSemantics`, this public
strengthening has no ad hoc motive-application premise: the terminal
classifier result is upgraded to `RecursorValidatedIndAppAt`, its target is
bounded by the completed mutual record cardinality, and the corresponding
independent motive contract is selected directly. -/
theorem resultSemanticsOfMotiveApplications
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Happlications : RecInfoMotiveApplications R stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q := by
  refine resultSemanticBindings stats u recInfos k R R 0 #[]
    (RecursorRecentBoundFVarArray.empty R)
    (RecInfoHypothesisTypeOrigins.empty stats recInfos c u) rfl ?_ ?_
  intro next Rnext prior Hprior j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsNext := Hstats.weakenRecent Hprior
  have hctxNext : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  apply mkRecInfos.loopUArgs.inductionHypothesisTypeOrigin fv stats recInfos next
    Rnext HstatsNext hwhnf hconsume hlit hctxNext hproj HfieldAt
      (Hbindings.motives.mono Hprior.contextExtension.contextLE) hrecords
  intro current Rcurrent exposedType syntaxTarget terminalTarget
    appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
    HappliedType hvalid
  let HstatsCurrent := HstatsNext.weakenRecent Hargs
  have htargetStats : target < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some hvalid).1
  have htarget : target < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : target < decl.types.length := by
    rw [← HstatsCurrent.types_size]
    exact htargetStats
  have hctxCurrent : VLCtx.NoIndConsts
      (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
    Hargs.noIndConsts (names := decl.types.map (·.name)) hctxNext
  let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
    htargetDecl hlit hctxCurrent hproj
  exact Happlications.applyAtMono Hbindings Horigins Hshape
    (Hprior.contextExtension.trans Hargs.contextExtension)
    target htarget Hexposed Hdefeq
    Hterminal Happlied HappliedType Hvalidated
  · intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simpa using hsize

/-- Shared-telescope form used by the strengthened first pass. -/
theorem resultSemanticsOfMotiveTelescopes
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q :=
  resultSemanticsOfMotiveApplications stats u recInfos k R Hstats hwhnf
    hconsume hlit hctx hproj Hfields Htelescopes.applications Hbindings
    Horigins Hshape hrecords Hk

end mkRecInfos.loopU

namespace mkRecInfos.loopCtors

/-- Semantic boundary for the final action of one constructor iteration.
Once the complete minor domain has been independently translated and typed,
this mirrors production's `withLocalDecl`, updates the owning minor row, and
transports every first-pass semantic invariant into the new context. -/
theorem continueMinorSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {minorTarget : VExpr}
    (Hminor : TrExprS R.venv recLparams R.mlctx.vlctx
      minorTy.consumeTypeAnnotations minorTarget)
    (HminorType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx minorTarget)
    (HminorShape : RecInfoMinorTypeShape)
    (HminorShapePosition :
      HminorShape.localIndex = Horigins.minorTypes[dIdx]!.size ∧
      HminorShape.origin = minorTy.consumeTypeAnnotations)
    (HminorSource : HminorShape.sourceConstructors =
      indTypes[dIdx]!.ctors)
    (HminorHypothesisOrigins :
      HminorShape.HasHypothesisTypeOrigins stats recInfos)
    (HminorSemantic :
      Nonempty (RecInfoMinorSemanticSourceAt R HminorShape
        Hsuffix.parameterDecls))
    (HminorTraversal : ∃ traversal,
      HminorShape.traversal = some traversal ∧
      traversal.constructor = HminorShape.constructor ∧
      traversal.fields = HminorShape.fields ∧
      traversal.recursiveFields = HminorShape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      HminorShape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const HminorShape.constructor.name stats.levels)
              stats.params)
            HminorShape.fields)) ∧
      BindingContextLE traversal.rootContext c ∧
      BindingContextLE traversal.terminalContext c ∧
      BindingContextLE HminorShape.sourceFullContext c)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoTypeOrigins outCtx out),
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (withLocalDecl minorName .default minorTy.consumeTypeAnnotations
      (fun minor =>
        let next := recInfos.modify dIdx fun info =>
          { info with minors := info.minors.push minor }
        k next) c).WF Q := by
  refine withLocalDecl.recursorWF (name := minorName) (bi := .default)
    R Hminor HminorType ?_
  let Rminor := R.withLocalDecl (name := minorName) (bi := .default)
    Hminor HminorType
  let cMinor : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName
      minorTy.consumeTypeAnnotations .default }
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push (.fvar ⟨c.ngen.curr⟩) }
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := .default) R Hminor HminorType
  let HbindingsMinor := Hbindings.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotations .default
  let HoriginsMinor := Horigins.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotations .default HminorShape
      HminorShapePosition
  let HminorSourcesMinor := HminorSources.addMinor dIdx hidx hsourceIdx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
    minorTy.consumeTypeAnnotations .default HminorShape
    HminorShapePosition HminorSource HminorHypothesisOrigins HminorTraversal
  let HminorSemanticsMinor := HminorSemantics.addMinor
    (RecursorContextExtension.refl R) dIdx hidx minorName
    minorTy.consumeTypeAnnotations .default Hminor HminorType HminorShape
    HminorShapePosition HminorSemantic
  let HparamsMinor := Hparams.mono Hstep.contextLE
  have HorderMinor : RecInfoOuterOrder Rminor HparamsMinor
      HbindingsMinor := by
    refine RecInfoOuterOrder.addMinor
      (minor := (⟨c.ngen.curr⟩ : FVarId)) Horder ?_ ?_ ?_ ?_
    · rfl
    · exact Hbindings.addMinor_motives_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          minorTy.consumeTypeAnnotations .default
    · exact Hbindings.addMinor_flatMinors_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          minorTy.consumeTypeAnnotations .default Hlater
    · rfl
  refine Hk next Rminor rfl (Hsuffix.withAmbient Hminor HminorType) rfl
    (Hstats.withFVar Rminor.checking.tr.wf Rminor.mlctx_wf.tr.wf)
    (VLCtx.NoIndConsts.cons hctx rfl)
    HbindingsMinor HoriginsMinor HminorSourcesMinor HminorSemanticsMinor
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      HparamsMinor ?_ ?_ ?_ ?_
  · simp [next]
  · dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    simp
  · intro i hi hine
    dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hine]
  · exact HmajorTypes.mono Hstep
  · exact HmajorShapes.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))
  · exact HmotiveTypes.mono Hstep
  · exact (HmotiveShapes.mono Hbindings Hstep.contextLE).modifyMinors
      dIdx (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))
  · exact (Htelescopes.mono Hstep).modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))
  · exact HindexRows.mono Hstep
  · exact Hbindings.addMinor_noAlias Hparams HnoAlias dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName
        minorTy.consumeTypeAnnotations .default
  · exact HorderMinor
  · exact Harities.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))
  · exact Hroot.trans Hstep.contextLE

/-- Complete semantic refinement of one constructor iteration in the second
`mkRecInfos` pass.  The only constructor-specific premise is the independent
introduction certificate for the exact terminal application exposed by the
field traversal; all recursive-field motives, generated IH binders, telescope
closure, and minor insertion are derived here. -/
theorem oneConstructorSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctor : Constructor) (tail : Expr)
    (sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hsourceConstructor : sourceConstructors[sourceIndex]? = some ctor)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tailTarget : VExpr}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : RecursorParamPrefix stats 0 ctor.type tail)
    (htailScope : tail.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params))
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (htailType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx tailTarget)
    {introTarget : VExpr}
    (Hintro : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN (.const ctor.name stats.levels) stats.params) introTarget)
    (HintroType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hnormal : Nonempty
      (CheckedConstructorOwnerNormalForm stats dIdx tail))
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoTypeOrigins outCtx out),
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type
      (fun terminal allFields recursiveFields =>
        let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
        let introApp := mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields
        let motiveApp := Expr.app
          (mkAppN recInfos[ownerIdx]!.motive indices) introApp
        AddInductive.mkRecInfos.loopU stats recursiveFields recInfos 0 #[]
          fun hypotheses => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall allFields <|
              lctx.mkForall hypotheses motiveApp
            let minorName :=
              ctor.name.replacePrefix indTypeName .anonymous
            withLocalDecl minorName .default
                minorTy.consumeTypeAnnotations fun minor =>
              let next := recInfos.modify dIdx fun info =>
                { info with minors := info.minors.push minor }
              k next) c).WF Q := by
  let process := fun terminal allFields recursiveFields =>
    let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
    let introApp := mkAppN
      (mkAppN (.const ctor.name stats.levels) stats.params) allFields
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive indices) introApp
    AddInductive.mkRecInfos.loopU stats recursiveFields recInfos 0 #[]
      fun hypotheses => do
        let lctx ← getLCtx
        let minorTy := lctx.mkForall allFields <|
          lctx.mkForall hypotheses motiveApp
        let minorName := ctor.name.replacePrefix indTypeName .anonymous
        withLocalDecl minorName .default minorTy.consumeTypeAnnotations
            fun minor =>
          let next := recInfos.modify dIdx fun info =>
            { info with minors := info.minors.push minor }
          k next
  change (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type process c).WF Q
  apply mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent (Q := Q)
    stats ctor.type tail
      (mkAppN (.const ctor.name stats.levels) stats.params)
      process c R Hstats hprefix hwhnf hconsume hlit hctx hproj htail
      htailType htailScope Hsuffix.parameterFVarsUp Hintro HintroType
  intro current Rargs terminal terminalTarget appliedTarget allFields
    recursiveFields fields positions args HterminalNonforall Hterminal
    HterminalType Hselections Hdecisions Hrecursive HfieldsRecent Hopening
    HfieldTargetDefEq _HterminalScope _HfieldParameterUp
    HintroApplied HintroAppliedType
  let HextArgs := HfieldsRecent.contextExtension
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  have hdidxDecl : dIdx < decl.types.length := by
    rw [← Hstats.types_size, ← hrecords]
    exact hidx
  have hdidxConst := Hstats.indConstAt hdidxDecl
  rcases Hnormal with ⟨Hnormal⟩
  have hdidxValid := Hnormal.validOfOpening Hopening Hparams
    HfieldsRecent.toFreshBoundFVarArray hdidxConst HterminalNonforall
  rcases checkPositivityStep.isValidIndApp?_exists_of_valid
      hdidxValid hdidxConst with
    ⟨ownerIdx, hownerValid⟩
  let Happlication : RecursorConstructorApplicationAt Rargs stats ctor
      terminal allFields terminalTarget := {
    ownerIdx := ownerIdx
    owner_valid := hownerValid
    terminal_type := HterminalType
    introTarget := appliedTarget
    intro := by simpa [mkAppN] using HintroApplied
    typing := HintroAppliedType }
  have htargetStats : Happlication.ownerIdx < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some Happlication.owner_valid).1
  have htarget : Happlication.ownerIdx < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : Happlication.ownerIdx < decl.types.length := by
    rw [← HstatsArgs.types_size]
    exact htargetStats
  let Hvalidated := HstatsArgs.validatedIndAppAt Hterminal
    Happlication.owner_valid htargetDecl hlit hctxArgs hproj
  have HterminalWF : VExpr.WF Rargs.venv recLparams.length
      Rargs.mlctx.vlctx.toCtx terminalTarget := by
    rcases Happlication.terminal_type with ⟨u, Htyped⟩
    exact ⟨.sort u, Htyped⟩
  rcases Htelescopes.applications.applyAtMono Hbindings Horigins
      HmotiveShapes HextArgs Happlication.ownerIdx htarget Hterminal
      (.refl HterminalWF) Happlication.terminal_type
      Happlication.intro Happlication.typing Hvalidated with
    ⟨motiveTarget, Hmotive, HmotiveType⟩
  let indices : Array Expr := terminal.getAppArgs[stats.params.size:]
  have howner : AddInductive.getIIndices stats terminal =
      (Happlication.ownerIdx, indices) := by
    simp only [AddInductive.getIIndices, indices]
    rw [Happlication.owner_valid]
    rfl
  dsimp only [process]
  rw [howner]
  let finish := fun hypotheses => do
    let lctx ← getLCtx
    let motiveApp := Expr.app
      (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
      (mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
    let minorTy := lctx.mkForall allFields <|
      lctx.mkForall hypotheses motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default minorTy.consumeTypeAnnotations
        fun minor =>
      let next := recInfos.modify dIdx fun info =>
        { info with minors := info.minors.push minor }
      k next
  change (AddInductive.mkRecInfos.loopU stats recursiveFields recInfos 0 #[]
    finish current).WF Q
  let HbindingsArgs := Hbindings.mono HextArgs.contextLE
  let HoriginsArgs := Horigins.mono HextArgs.contextLE
  let HmotiveShapesArgs := HmotiveShapes.mono Hbindings HextArgs.contextLE
  let HtelescopesArgs := Htelescopes.mono HextArgs
  apply mkRecInfos.loopU.resultSemanticsOfMotiveTelescopes (Q := Q)
    stats recursiveFields recInfos finish Rargs HstatsArgs hwhnf hconsume hlit
      hctxArgs hproj
      (Hselections.selectedFVars
        HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray Hrecursive)
      HtelescopesArgs HbindingsArgs HoriginsArgs HmotiveShapesArgs hrecords
  intro outCtx Rout hypotheses HhypothesesRecent HhypothesisOrigins
    hhypothesesSize
  let HextAll := HextArgs.trans HhypothesesRecent.contextExtension
  have HmotiveAt : TrExprS Rout.venv recLparams Rout.mlctx.vlctx
      (Expr.app
        (mkAppN recInfos[Happlication.ownerIdx]!.motive
          terminal.getAppArgs[stats.params.size:])
        (mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields))
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakTrExprS Hmotive
  have HmotiveTypeAt : Rout.venv.IsType recLparams.length
      Rout.mlctx.vlctx.toCtx
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakIsType HmotiveType
  rcases HhypothesesRecent.mkForall HmotiveAt HmotiveTypeAt with
    ⟨hypothesesTarget, Hhypotheses, HhypothesesType⟩
  have houter : outCtx.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields))) =
      current.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields))) :=
    HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
      HhypothesesRecent.contextLE _
  rcases HfieldsRecent.mkForall Hhypotheses HhypothesesType with
    ⟨minorTarget, HminorRaw, HminorRawType⟩
  have HminorRaw' : TrExprS R.venv recLparams R.mlctx.vlctx
      (outCtx.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields)))) minorTarget := by
    rw [houter]
    exact HminorRaw
  have hget : ((getLCtx : AddInductive.M LocalContext) outCtx).WF
      (fun lctx => lctx = outCtx.lctx) := by
    intro lctx h
    cases h
    rfl
  dsimp only [finish]
  refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
    hget fun lctx hlctx => ?_
  subst lctx
  have HminorRawAt := HextAll.weakTrExprS HminorRaw'
  have HminorRawTypeAt := HextAll.weakIsType HminorRawType
  rcases hconsume outCtx recLparams Rout HminorRawAt HminorRawTypeAt with
    ⟨consumedTarget, Hconsumed⟩
  let HsuffixOut :=
    (Hsuffix.weakenRecent HfieldsRecent).weakenRecent HhypothesesRecent
  let HstatsOut := HstatsArgs.weakenRecent HhypothesesRecent
  have hctxOut : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rout.mlctx.vlctx :=
    HhypothesesRecent.noIndConsts
      (names := decl.types.map (·.name)) hctxArgs
  let traversal : RecInfoMinorTraversalShape := {
    constructor := ctor
    rootContext := c
    terminalContext := current
    terminal := terminal
    fields := allFields
    recursiveFields := recursiveFields
    stats := stats
    recursivePositions := positions
    decisions := Hdecisions
    recursivePositions_ordered := Hdecisions.positions_ordered
    recursivePositions_lt := Hdecisions.positions_lt
    recursivePositions_length := Hdecisions.positions_length
    parameterTail := tail
    parameterTail_fvars := by
      apply htailScope.mono
      intro fv hfv
      rw [Hparams.exprArrayFVarIds] at hfv
      exact Hparams.members fv hfv
    parameterPrefix := hprefix
    fieldFVars := Hopening.fvars
    fields_eq := Hopening.expressions
    fieldFVars_nodup := Hopening.nodup
    fieldResidual := Hopening.residual
    fieldTelescope := Hopening.telescope
    fieldClosed := Hopening.closed
    fieldResidual_not_forall := by
      rw [← Hopening.closed, Expr.abstractList_isForall]
      exact HterminalNonforall }
  let HbindingsOut := Hbindings.mono HextAll.contextLE
  let HoriginsOut := Horigins.mono HextAll.contextLE
  let HparamsOut := Hparams.mono HextAll.contextLE
  have HorderArgs := Horder.monoRecent HfieldsRecent
  have HorderOut0 := HorderArgs.monoRecent HhypothesesRecent
  have HorderOut : RecInfoOuterOrder Rout HparamsOut HbindingsOut := by
    unfold RecInfoOuterOrder at HorderOut0 ⊢
    change (Hparams.fvars ++ Hbindings.motives.fvars ++
      Hbindings.flatMinors.fvars).reverse <+ Rout.mlctx.vlctx.fvars
    exact HorderOut0
  let HminorSemanticsOut := HminorSemantics.mono HextAll
  refine continueMinorSemantics (Q := Q) stats indTypes dIdx recInfos
    (ctor.name.replacePrefix indTypeName .anonymous)
    (outCtx.lctx.mkForall allFields
      (outCtx.lctx.mkForall hypotheses
        (Expr.app
          (mkAppN recInfos[Happlication.ownerIdx]!.motive
            indices)
          (mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params)
            allFields))))
    k Rout HsuffixOut HstatsOut hctxOut HbindingsOut HoriginsOut
      (HminorSources.mono HextAll.contextLE)
      HminorSemanticsOut
      (HmajorTypes.mono HextAll) HmajorShapes
      (HmotiveTypes.mono HextAll)
      (HmotiveShapes.mono Hbindings HextAll.contextLE)
      (Htelescopes.mono HextAll) (HindexRows.mono HextAll)
      HparamsOut
      (Hbindings.mono_noAlias Hparams HextAll.contextLE HnoAlias)
      HorderOut (Hroot.trans HextAll.contextLE) hidx hsourceIdx Harities
      Hlater Hconsumed.consumed
      Hconsumed.isType {
        localIndex := HoriginsOut.minorTypes[dIdx]!.size
        origin := (outCtx.lctx.mkForall allFields
          (outCtx.lctx.mkForall hypotheses
            (Expr.app
              (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
              (mkAppN
                (mkAppN (.const ctor.name stats.levels) stats.params)
                allFields)))).consumeTypeAnnotations
        constructor := ctor
        sourceConstructors := sourceConstructors
        sourceConstructor := by
          simpa [HoriginsOut, RecInfoTypeOrigins.mono, horiginIndex] using
            hsourceConstructor
        sourceFullContext := outCtx
        sourceFullWF := Rout.toBindingContextWF
        sourceContext := outCtx.lctx
        sourceContext_eq := rfl
        fields := allFields
        fields_bound :=
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.mono
            HhypothesesRecent.contextExtension.contextLE
        fields_nodup := HfieldsRecent.toFreshBoundFVarArray.nodup
        recursiveFields := recursiveFields
        hypotheses := hypotheses
        hypotheses_bound :=
          HhypothesesRecent.toFreshBoundFVarArray.toBoundFVarArray
        hypotheses_nodup :=
          HhypothesesRecent.toFreshBoundFVarArray.nodup
        hypotheses_fields_fresh := by
          intro fv hhypothesis hfield
          apply HhypothesesRecent.toFreshBoundFVarArray.fresh fv
            hhypothesis
          exact HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.members
            fv hfield
        hypothesis_type_origins := some {
          stats := stats
          recInfos := recInfos
          hypotheses_outer_fresh := by
            intro fv houter hhypothesis
            rw [Hparams.exprArrayFVarIds,
              Hbindings.motives.exprArrayFVarIds] at houter
            rw [(HhypothesesRecent.toFreshBoundFVarArray.toBoundFVarArray
              ).exprArrayFVarIds] at hhypothesis
            apply HhypothesesRecent.toFreshBoundFVarArray.fresh fv
              hhypothesis
            apply HextArgs.contextLE.fvars
            rcases List.mem_append.mp houter with hparam | hmotive
            · exact Hparams.members fv hparam
            · exact Hbindings.motives.members fv hmotive
          entry := by
            intro j hj
            rcases HhypothesisOrigins.entry j hj with
              ⟨originRoot, sourceType, ⟨O⟩, D, htype⟩
            exact ⟨originRoot, sourceType, ⟨{
              current := O.current
              current_wf := O.current_wf
              current_extends := O.current_extends
              exposedType := O.exposedType
              args := O.args
              arguments_bound := O.arguments_bound
              field_fvar := O.field_fvar
              ownerIdx := O.ownerIdx
              owner_valid := O.owner_valid
              motive_is_fvar := O.motive_is_fvar
              type_eq := O.type_eq }⟩, D, htype⟩ }
        hypotheses_size := hhypothesesSize
        traversal := some traversal
        motiveApp := Expr.app
          (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
          (mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params)
            allFields)
        sourceType := outCtx.lctx.mkForall allFields
          (outCtx.lctx.mkForall hypotheses
            (Expr.app
              (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
              (mkAppN
                (mkAppN (.const ctor.name stats.levels) stats.params)
                allFields)))
        sourceType_eq := rfl
        consumed_eq := rfl } ⟨rfl, rfl⟩ (by
          simpa [HoriginsOut, RecInfoTypeOrigins.mono, horiginIndex] using
            hsourceFamily)
      (by simp [RecInfoMinorTypeShape.HasHypothesisTypeOrigins])
      ⟨{
        semantic := {
          sourceWF := Rout
          extension := RecursorContextExtension.refl Rout
          traversal := traversal
          traversal_eq := rfl
          traversal_fields := rfl
          rootWF := R
          terminalWF := Rargs
          parameterDepth := depth
          parameterSuffix := Hsuffix
          parameterScope := by
            apply htailScope.mono
            intro fv hfv
            rw [Hsuffix.parameterDecls_fvars]
            simpa using hfv
          parameterTarget := tailTarget
          parameterTranslation := htail
          parameterType := htailType
          fieldsRecent := HfieldsRecent
          hypothesesRecent := HhypothesesRecent
          terminalTarget := terminalTarget
          terminalTranslation := Hterminal
          terminalType := HterminalType
          fieldTargetDefEq := HfieldTargetDefEq
          motivePreTarget := motiveTarget
          motivePreTranslation := Hmotive
          motivePreType := HmotiveType
          motiveTarget := motiveTarget.lift'
            (HhypothesesRecent.contextExtension.shift.consN 0)
          motiveTranslation := HmotiveAt
          motiveType := HmotiveTypeAt
          sourceTarget := minorTarget.lift' (HextAll.shift.consN 0)
          consumedTarget := consumedTarget
          consumption := Hconsumed }
        parameterDecls_eq := rfl }⟩
      ⟨traversal, rfl, rfl, rfl, rfl, rfl, by
        rw [howner]
        exact Happlication.owner_valid, by rw [howner],
        HextAll.contextLE,
        HhypothesesRecent.contextExtension.contextLE,
        BindingContextLE.refl outCtx⟩ ?_
  intro nextCtx nextDepth next Rnext henvNext HsuffixNext
    hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
    HminorSourcesNext HminorSemanticsNext hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext
    HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
    HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
  exact Hk next Rnext (henvNext.trans HextAll.venv_eq) HsuffixNext
    (hparameterDeclsNext.trans (by rfl)) HstatsNext hctxNext
    HbindingsNext HoriginsNext HminorSourcesNext HminorSemanticsNext
    hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext HmotiveTypesNext HmotiveShapesNext
    HtelescopesNext HindexRowsNext HparamsNext HnoAliasNext HorderNext
    HaritiesNext HrootNext

/-- Semantic refinement of the complete constructor list for one mutual
family.  Each iteration consumes the checker-produced runtime seed for its
constructor and adds exactly one verified minor to the owning recursor row. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hconstructors : ctors = sourceConstructors.drop sourceIndex)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hminorIndex : recInfos[dIdx]!.minors.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = Hsuffix.parameterDecls →
      ∀ ctor, ctor ∈ ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = Hsuffix.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoTypeOrigins outCtx out) →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c depth sourceIndex with
  | nil =>
      exact Hk recInfos R rfl Hsuffix rfl Hstats hctx Hbindings Horigins
        HminorSources HminorSemantics rfl (by simp) (by intros; rfl)
        HmajorTypes HmajorShapes
        HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams HnoAlias
        Horder Harities Hroot
  | cons ctor ctors ih =>
      have hsourceConstructor :
          sourceConstructors[sourceIndex]? = some ctor := by
        have hhead := congrArg (fun xs => xs[0]?) hconstructors
        simpa using hhead.symm
      have htailConstructors :
          ctors = sourceConstructors.drop (sourceIndex + 1) := by
        have htail := congrArg List.tail hconstructors
        simpa [List.tail_drop] using htail
      have horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex := by
        rw [(Horigins.minors dIdx hidx).size_eq]
        exact hminorIndex
      rcases Hseed R rfl Hsuffix rfl ctor (by simp) with
        ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailScope, Htail,
          HtailType, Hintro, HintroType⟩
      rw [AddInductive.mkRecInfos.loopCtors]
      refine oneConstructorSemantics (Q := Q) stats indTypes indTypeName dIdx recInfos
        ctor tail sourceConstructors sourceIndex hsourceConstructor hsourceFamily
        (fun next => AddInductive.mkRecInfos.loopCtors stats indTypeName
          dIdx next ctors k)
        R Hsuffix Hstats Hprefix HtailScope hwhnf hconsume hlit hctx hproj Htail
        HtailType Hintro HintroType Hbindings Horigins HminorSources
        HminorSemantics HmajorTypes
        HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows
        Hparams HnoAlias Horder Hroot hidx hsourceIdx horiginIndex Harities
        Hlater hrecords Hnormal ?_
      intro nextCtx nextDepth next Rnext henvNext HsuffixNext
        hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
        HminorSourcesNext HminorSemanticsNext hsizeNext hcountNext hotherNext
        HmajorTypesNext HmajorShapesNext
        HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
        HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
      refine ih next (sourceIndex + 1) htailConstructors Rnext HsuffixNext
        HstatsNext hctxNext HbindingsNext
        HoriginsNext HminorSourcesNext HminorSemanticsNext HmajorTypesNext
        HmajorShapesNext HmotiveTypesNext
        HmotiveShapesNext HtelescopesNext HindexRowsNext HparamsNext
        HnoAliasNext HorderNext HrootNext ?_ ?_ HaritiesNext ?_ ?_ ?_ ?_
      · simpa [hsizeNext] using hidx
      · rw [hcountNext, hminorIndex]
      · intro i hdi hiNext
        rw [hotherNext i (by simpa [hsizeNext] using hiNext)
          (Nat.ne_of_lt hdi)]
        exact Hlater i hdi (by simpa [hsizeNext] using hiNext)
      · exact hsizeNext.trans hrecords
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent nextCtor hnextCtor
        apply Hseed Rcurrent (henvCurrent.trans henvNext) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsNext) nextCtor
        simp [hnextCtor]
      · intro outCtx outDepth out Rout henvOut HsuffixOut
          hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
          HminorSourcesOut HminorSemanticsOut houtSize houtCount houtOther
          HmajorTypesOut HmajorShapesOut
          HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
          HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size :=
          houtSize.trans hsizeNext
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount, hcountNext]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [hsizeNext] using hi) hine]
          exact hotherNext i hi hine
        exact Hk out Rout (henvOut.trans henvNext) HsuffixOut
          (hparameterDeclsOut.trans hparameterDeclsNext) HstatsOut hctxOut
          HbindingsOut HoriginsOut HminorSourcesOut HminorSemanticsOut
          houtSize' houtCount' houtOther'
          HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
          HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
          HaritiesOut HrootOut

/-- Processing constructors retains every field and induction-hypothesis
binder and appends the resulting minor binder to the certificate of its
owning inductive. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (Harities : RecInfoArities stats recInfos)
    (Hk : ∀ out c, out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Horigins : RecInfoTypeOrigins c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simpa [AddInductive.mkRecInfos.loopCtors] using
        Hk recInfos c rfl (by simp) (by intros; rfl)
          Hc Hbindings Horigins Hparams HnoAlias Harities Hroot
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      refine mkRecInfos.loopCtorArgs.resultBindings (Q := Q) stats ctor.type
        (fun t bu u =>
          let (itIdx, itIndices) := AddInductive.getIIndices stats t
          let introApp := mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params) bu
          let motiveApp := Expr.app
            (mkAppN recInfos[itIdx]!.motive itIndices) introApp
          AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] fun v => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
            let minorName := ctor.name.replacePrefix indTypeName .anonymous
            withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor =>
              let recInfos := recInfos.modify dIdx fun s =>
                { s with minors := s.minors.push minor }
              AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
                ctors k)
        c Hc ?_
      intro t bu u cArgs HcArgs Hbu Hu _hselected hArgs
      rcases hindices : AddInductive.getIIndices stats t with
        ⟨itIdx, itIndices⟩
      simp only
      let introApp := mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) bu
      let motiveApp := Expr.app
        (mkAppN recInfos[itIdx]!.motive itIndices) introApp
      apply mkRecInfos.loopU.resultBindings (root := cArgs) (Q := Q)
        stats u recInfos
        (fun v => do
          let lctx ← getLCtx
          let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
          let minorName := ctor.name.replacePrefix indTypeName .anonymous
          withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor =>
            let recInfos := recInfos.modify dIdx fun s =>
              { s with minors := s.minors.push minor }
            AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
              ctors k)
        0 #[] cArgs HcArgs (FreshBoundFVarArray.empty cArgs)
          (BindingContextLE.refl cArgs)
      intro v cIH HcIH Hv hIH hvSize
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      let minorTy := cIH.lctx.mkForall bu <| cIH.lctx.mkForall v motiveApp
      let minorName := ctor.name.replacePrefix indTypeName .anonymous
      apply withLocalDecl.continueRaw
      let next := recInfos.modify dIdx fun s =>
        { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }
      let cMinor : AddInductive.Context := { cIH with
        ngen := cIH.ngen.next
        lctx := cIH.lctx.mkLocalDecl ⟨cIH.ngen.curr⟩ minorName
          minorTy.consumeTypeAnnotations .default }
      let HcMinor := HcIH.withLocalDecl minorName
        minorTy.consumeTypeAnnotations .default
      let HbindingsMinor := Hbindings.addMinor dIdx hidx (hArgs.trans hIH)
        HcIH minorName minorTy.consumeTypeAnnotations .default
      let HoriginsMinor := Horigins.addMinor dIdx hidx (hArgs.trans hIH)
        HcIH minorName minorTy.consumeTypeAnnotations .default {
          localIndex := Horigins.minorTypes[dIdx]!.size
          origin := minorTy.consumeTypeAnnotations
          constructor := ctor
          sourceConstructors :=
            List.replicate Horigins.minorTypes[dIdx]!.size ctor ++ [ctor]
          sourceConstructor := by simp
          sourceFullContext := cIH
          sourceFullWF := HcIH
          sourceContext := cIH.lctx
          sourceContext_eq := rfl
          fields := bu
          fields_bound := Hbu.mono hIH
          fields_nodup := Hbu.nodup
          recursiveFields := u
          hypotheses := v
          hypotheses_bound := Hv.toBoundFVarArray
          hypotheses_nodup := Hv.nodup
          hypotheses_fields_fresh := by
            intro fv hhypothesis hfield
            exact Hv.fresh fv hhypothesis
              (Hbu.toBoundFVarArray.members fv hfield)
          hypothesis_type_origins := none
          hypotheses_size := by simpa using hvSize
          traversal := none
          motiveApp := motiveApp
          sourceType := minorTy
          sourceType_eq := rfl
          consumed_eq := rfl } ⟨rfl, rfl⟩
      let HparamsMinor := Hparams.mono <| (hArgs.trans hIH).trans <|
          BindingContextLE.withLocalDecl cIH HcIH minorName
            minorTy.consumeTypeAnnotations .default
      let HnoAliasMinor := Hbindings.addMinor_noAlias Hparams HnoAlias
        dIdx hidx (hArgs.trans hIH) HcIH minorName
          minorTy.consumeTypeAnnotations .default
      let HrootMinor := (Hroot.trans hArgs).trans <| hIH.trans <|
          BindingContextLE.withLocalDecl cIH HcIH minorName
            minorTy.consumeTypeAnnotations .default
      refine ih next cMinor HcMinor HbindingsMinor HoriginsMinor
        HparamsMinor HnoAliasMinor
        HrootMinor ?_ ?_ ?_
      · simpa [next] using hidx
      · exact Harities.modifyMinors dIdx (fun minors =>
          minors.push (.fvar ⟨cIH.ngen.curr⟩))
      · intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
          HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size := by
          simpa [next] using houtSize
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount]
          dsimp [next]
          rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _
            hidx]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
            hi hine]
        exact Hk out cOut houtSize' houtCount' houtOther' HcOut HbindingsOut
          HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

/-- The second mutual pass preserves all retained recursor binders while it
visits each owner and inserts that owner's constructor minors. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hsize : recInfos.size = indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (Hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Horigins : RecInfoTypeOrigins c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultBindings (Q := Q) stats
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      c Hc Hbindings Horigins Hparams HnoAlias Hroot
      (by simpa [hsize] using hidx)
      Harities
    intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
      HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut
    apply resultBindings (root := root) (Q := Q) stats indTypes (dIdx + 1)
      out k cOut HcOut HbindingsOut HoriginsOut HparamsOut HnoAliasOut HrootOut
    · exact houtSize.trans hsize
    · exact HaritiesOut
    · intro i hiDone hiOut
      by_cases hieq : i = dIdx
      · subst i
        rw [houtCount, Hsuffix dIdx (Nat.le_refl _) (by
          simpa [houtSize] using hiOut)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [houtSize] using hiOut) (Ne.symm hieq)]
        exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
    · intro i hiNext hiOut
      have hine : dIdx ≠ i := by omega
      rw [houtOther i (by simpa [houtSize] using hiOut) hine]
      exact Hsuffix i (by omega) (by simpa [houtSize] using hiOut)
    · exact Hk
  · rw [dif_neg hidx]
    exact Hk recInfos c hsize (fun i hi => Hprefix i (by omega) hi)
      Hc Hbindings Horigins Hparams HnoAlias Harities Hroot
termination_by indTypes.size - dIdx

/-- Semantic refinement of the complete second mutual pass.  The processed
prefix has its exact constructor/minor cardinalities, the unprocessed suffix
is empty, and every checker-produced constructor seed is consumed at its
original mutual-family owner. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (HsuffixCtx : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      HsuffixCtx.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hsize : recInfos.size = indTypes.size)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (HemptySuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = HsuffixCtx.parameterDecls →
      ∀ familyIdx, (hfamily : familyIdx < indTypes.size) →
      ∀ ctor, ctor ∈ indTypes[familyIdx].ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty
          (CheckedConstructorOwnerNormalForm stats familyIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = HsuffixCtx.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoTypeOrigins outCtx out) →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hfamily : dIdx < indTypes.size
  · rw [dif_pos hfamily]
    refine mkRecInfos.loopCtors.resultSemantics (Q := Q) stats indTypes
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      indTypes[dIdx].ctors 0 rfl
      (by simp [getElem!_pos indTypes dIdx hfamily])
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      R HsuffixCtx Hstats hwhnf hconsume hlit hctx hproj Hbindings
      Horigins HminorSources HminorSemantics HmajorTypes HmajorShapes
      HmotiveTypes HmotiveShapes
      Htelescopes HindexRows Hparams HnoAlias Horder Hroot
      (by simpa [hsize] using hfamily)
      hfamily
      (by
        exact HemptySuffix dIdx (Nat.le_refl _) (by
          simpa [hsize] using hfamily))
      Harities (fun i hdi hi => HemptySuffix i (by omega) hi) hrecords ?_ ?_
    · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent ctor hctor
      exact Hseed Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent dIdx hfamily ctor hctor
    · intro outCtx outDepth out Rout henvOut HsuffixOut
        hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
        HminorSourcesOut HminorSemanticsOut houtSize houtCount houtOther
        HmajorTypesOut HmajorShapesOut
        HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
        HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
      refine resultSemantics (root := root) (Q := Q) stats indTypes
        (dIdx + 1) out k Rout HsuffixOut HstatsOut hwhnf hconsume hlit
        hctxOut hproj HbindingsOut HoriginsOut HminorSourcesOut
        HminorSemanticsOut HmajorTypesOut
        HmajorShapesOut HmotiveTypesOut HmotiveShapesOut HtelescopesOut
        HindexRowsOut HparamsOut HnoAliasOut HorderOut HrootOut ?_ ?_
        HaritiesOut
        ?_ ?_ ?_ ?_
      · exact houtSize.trans hsize
      · exact houtSize.trans hrecords
      · intro i hiDone hiOut
        by_cases hieq : i = dIdx
        · subst i
          rw [houtCount, HemptySuffix dIdx (Nat.le_refl _) (by
            simpa [houtSize] using hiOut)]
          simp [Array.getElem!_eq_getD, Array.getD, hfamily]
        · rw [houtOther i (by simpa [houtSize] using hiOut)
            (Ne.symm hieq)]
          exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
      · intro i hiNext hiOut
        have hine : dIdx ≠ i := by omega
        rw [houtOther i (by simpa [houtSize] using hiOut) hine]
        exact HemptySuffix i (by omega) (by simpa [houtSize] using hiOut)
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent familyIdx hfamilyIdx ctor hctor
        exact Hseed Rcurrent (henvCurrent.trans henvOut) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsOut) familyIdx
          hfamilyIdx ctor hctor
      · intro finalCtx finalDepth final Rfinal henvFinal HsuffixFinal
          hparameterDeclsFinal HstatsFinal hctxFinal HbindingsFinal
          HoriginsFinal HminorSourcesFinal HminorSemanticsFinal
          hfinalSize hfinalCounts HmajorTypesFinal
          HmajorShapesFinal HmotiveTypesFinal HmotiveShapesFinal
          HtelescopesFinal HindexRowsFinal HparamsFinal HnoAliasFinal
          HorderFinal HaritiesFinal HrootFinal
        exact Hk final Rfinal (henvFinal.trans henvOut) HsuffixFinal
          (hparameterDeclsFinal.trans hparameterDeclsOut) HstatsFinal
          hctxFinal HbindingsFinal HoriginsFinal HminorSourcesFinal
          HminorSemanticsFinal hfinalSize hfinalCounts
          HmajorTypesFinal HmajorShapesFinal HmotiveTypesFinal
          HmotiveShapesFinal HtelescopesFinal HindexRowsFinal HparamsFinal
          HnoAliasFinal HorderFinal HaritiesFinal HrootFinal
  · rw [dif_neg hfamily]
    exact Hk recInfos R rfl HsuffixCtx rfl Hstats hctx Hbindings Horigins
      HminorSources HminorSemantics hsize
      (fun i hi => Hprefix i (by omega) hi) HmajorTypes
      HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams
      HnoAlias Horder Harities Hroot
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end operational certificate for `mkRecInfos`: every successful
result has one retained frame per mutual inductive, and all binders created by
both passes remain selectable in the final local context. -/
theorem mkRecInfos.resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF cOut → (Hbindings : RecInfoBindings cOut out) →
      (Horigins : RecInfoTypeOrigins cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoArities stats out →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultBindings (root := c) (Q := Q)
    stats indTypes elimLevel 0 #[]
    (fun recInfos => AddInductive.mkRecInfos.loopInd2 stats indTypes 0
      recInfos k)
    c Hc (RecInfoBindings.empty c) (RecInfoTypeOrigins.empty c) Hparams
      (RecInfoBindings.empty_noAlias c Hparams hparamsNodup)
      (BindingContextLE.refl c) rfl
      (RecInfoArities.empty stats) RecInfoMinorsEmpty.empty
  intro recInfos cFrames hsize HcFrames HbindingsFrames HoriginsFrames HparamsFrames
    HnoAliasFrames HaritiesFrames HemptyFrames HrootFrames
  apply mkRecInfos.loopInd2.resultBindings (root := c) (Q := Q)
    stats indTypes 0 recInfos k cFrames HcFrames HbindingsFrames HoriginsFrames
      HparamsFrames HnoAliasFrames HrootFrames
  · simpa using hsize
  · exact HaritiesFrames
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro out cOut houtSize houtCounts HcOut HbindingsOut HoriginsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut
    exact Hk out cOut houtSize houtCounts HcOut HbindingsOut HoriginsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut

/-- Unified projection used by recursor generation: a single successful run
supplies both the retained executable binders and the independent cardinality
certificate derived from the translated source declaration. -/
theorem mkRecInfos.resultCertificate {alpha : Type} {Q : alpha → Prop}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, BindingContextWF cOut →
      (Hbindings : RecInfoBindings cOut out) →
      (Horigins : RecInfoTypeOrigins cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecursorCardinalityCertificate stats out decl →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultBindings (Q := Q) stats indTypes elimLevel k c Hc
    Hparams hparamsNodup
  intro out cOut hsize hcounts HcOut Hbindings Horigins HparamsOut HnoAlias
    Harities Hroot
  apply Hk out cOut HcOut Hbindings Horigins HparamsOut HnoAlias
  · exact RecursorCardinalityCertificate.ofResult Hdecl Hmaterialized
      hsize hcounts Harities
  · exact Hroot


end VerifyInductive
end Lean4Lean
