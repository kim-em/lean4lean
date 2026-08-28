import Lean4Lean.Verify.Inductive.Context

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

/-- The real delta body of a binary annotation wrapper translates to the same
abstract constant as its source head; beta reduction therefore identifies the
translated wrapper application with its first argument. -/
theorem BinaryTypeAnnotationWrapper.applicationDefEq
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx} {name : Name}
    (H : BinaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hDelta : Delta.WF venv Us.length) (hnoBV : Delta.NoBV)
    {levels : List Level} {first second : Expr} {out : VExpr}
    (htr : TrExprS venv Us Delta
      (.app (.app (.const name levels) first) second) out) :
    exists first', TrExprS venv Us Delta first first' ∧
      venv.IsDefEqU Us.length Delta.toCtx out first' := by
  rcases H.operational with
    ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  let .app hfnType hsecondType hfn hsecond := htr
  let .app hheadType hfirstType hhead hfirst := hfn
  let .const habstract hlevels harity := hhead
  have ⟨hname, hsafety, huvars, _htype⟩ :=
    Hchecking.tr.find?_uniq hlookup habstract
  subst name
  have hvalue :=
    (Hchecking.tr.of_value hlookup
      (hsafe ▸ DefinitionSafety.le_safe) hdelta).instL
      Hchecking.tr.wf (by trivial) hlevels (huvars.trans harity.symm)
  have hvalueWeak := hvalue.weakFV Hchecking.tr.wf
    (VLCtx.FVLift.from_nil hnoBV) hDelta
  rw [hvalue.wf.closedN Hchecking.tr.wf trivial |>.liftN_eq
    (Nat.zero_le _)] at hvalueWeak
  simp [VExpr.instL] at hvalueWeak
  rw [VLevel.inst_map_id] at hvalueWeak
  · have happFn :=
      TrExpr.app Hchecking.tr.wf hDelta hheadType hfirstType
        hvalueWeak (hfirst.trExpr Hchecking.tr.wf.ordered hDelta)
    have happ := TrExpr.app Hchecking.tr.wf hDelta hfnType hsecondType happFn
        (hsecond.trExpr Hchecking.tr.wf.ordered hDelta)
    have hfirstClosed : first.Closed := by
      simpa [hnoBV] using hfirst.closed
    have hsecondClosed : second.Closed := by
      simpa [hnoBV] using hsecond.closed
    have hbeta := happ.beta Hchecking.tr.wf hDelta
      (hreduces levels hfirstClosed hsecondClosed)
    exact ⟨_, hfirst,
      hbeta.uniq Hchecking.tr.wf
        (.refl Hchecking.tr.wf hDelta) (hfirst.trExpr Hchecking.tr.wf.ordered hDelta)⟩
  · exact (VerifyInductive.List.Forall₂.length_eq'
      (List.mapM_eq_some.1 hlevels)).symm.trans <|
      harity.trans huvars.symm

/-- Unary output-parameter wrappers are handled by the same real-body
unfolding argument. -/
theorem UnaryTypeAnnotationWrapper.applicationDefEq
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx} {name : Name}
    (H : UnaryTypeAnnotationWrapper env name)
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hDelta : Delta.WF venv Us.length) (hnoBV : Delta.NoBV)
    {levels : List Level} {arg : Expr} {out : VExpr}
    (htr : TrExprS venv Us Delta (.app (.const name levels) arg) out) :
    exists arg', TrExprS venv Us Delta arg arg' ∧
      venv.IsDefEqU Us.length Delta.toCtx out arg' := by
  rcases H.operational with
    ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  let .app hheadType hargType hhead harg := htr
  let .const habstract hlevels harity := hhead
  have ⟨hname, hsafety, huvars, _htype⟩ :=
    Hchecking.tr.find?_uniq hlookup habstract
  subst name
  have hvalue :=
    (Hchecking.tr.of_value hlookup
      (hsafe ▸ DefinitionSafety.le_safe) hdelta).instL
      Hchecking.tr.wf (by trivial) hlevels (huvars.trans harity.symm)
  have hvalueWeak := hvalue.weakFV Hchecking.tr.wf
    (VLCtx.FVLift.from_nil hnoBV) hDelta
  rw [hvalue.wf.closedN Hchecking.tr.wf trivial |>.liftN_eq
    (Nat.zero_le _)] at hvalueWeak
  simp [VExpr.instL] at hvalueWeak
  rw [VLevel.inst_map_id] at hvalueWeak
  · have happ :=
      TrExpr.app Hchecking.tr.wf hDelta hheadType hargType hvalueWeak
        (harg.trExpr Hchecking.tr.wf.ordered hDelta)
    have hargClosed : arg.Closed := by
      simpa [hnoBV] using harg.closed
    have hbeta :=
      happ.beta Hchecking.tr.wf hDelta (hreduces levels hargClosed)
    exact ⟨_, harg,
      hbeta.uniq Hchecking.tr.wf
        (.refl Hchecking.tr.wf hDelta) (harg.trExpr Hchecking.tr.wf.ordered hDelta)⟩
  · exact (VerifyInductive.List.Forall₂.length_eq'
      (List.mapM_eq_some.1 hlevels)).symm.trans <|
      harity.trans huvars.symm

theorem Expr.isAppOfArity_two_eq_true
    {e : Expr} {name : Name}
    (H : e.isAppOfArity name 2 = true) :
    ∃ levels first second,
      e = Expr.app (Expr.app (Expr.const name levels) first) second := by
  cases e <;> simp [Expr.isAppOfArity] at H
  case app fn second =>
    cases fn <;> simp [Expr.isAppOfArity] at H
    case app head first =>
      cases head <;> simp [Expr.isAppOfArity] at H
      case const found levels =>
        subst found
        exact ⟨levels, first, second, rfl⟩

theorem Expr.isAppOfArity_one_eq_true
    {e : Expr} {name : Name}
    (H : e.isAppOfArity name 1 = true) :
    ∃ levels arg, e = Expr.app (Expr.const name levels) arg := by
  cases e <;> simp [Expr.isAppOfArity] at H
  case app head arg =>
    cases head <;> simp [Expr.isAppOfArity] at H
    case const found levels =>
      subst found
      exact ⟨levels, arg, rfl⟩

/-- Semantic annotation consumption in any well-formed, binder-only checker
scope.  The result is independent of inductive-specific context packaging, so
the ordinary and generated-recursor callbacks are instances of one proof. -/
theorem consumeTypeAnnotationsSemantic
    {env : Environment} {venv : VEnv} {safety : DefinitionSafety}
    {Us : List Name} {Delta : VLCtx}
    (Hchecking : CheckingEnv.Valid safety env venv)
    (hDelta : Delta.WF venv Us.length) (hnoBV : Delta.NoBV)
    {dom : Expr} {source' : VExpr}
    (htr : TrExprS venv Us Delta dom source')
    (htype : venv.IsType Us.length Delta.toCtx source') :
    ∃ consumed',
      TrExprS venv Us Delta dom.consumeTypeAnnotationsVerified consumed' ∧
      venv.IsType Us.length Delta.toCtx consumed' ∧
      ∃ u, venv.IsDefEq Us.length Delta.toCtx
        source' consumed' (.sort u) := by
  fun_induction Expr.consumeTypeAnnotationsVerified dom generalizing source'
  case case1 name levels first second hannotation ih =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hannotation
    rcases hannotation with hopt | hauto
    · subst name
      rcases Hchecking.typeAnnotationWrappers.optParam.applicationDefEq
          Hchecking hDelta hnoBV htr with ⟨first', hfirst, hwrap⟩
      rcases htype with ⟨u, hsourceType⟩
      have hwrapAtSort :=
        hwrap.of_l Hchecking.tr.wf hDelta.toCtx hsourceType
      have hfirstType : venv.IsType Us.length Delta.toCtx first' :=
        ⟨u, hwrapAtSort.hasType.2⟩
      rcases ih hfirst hfirstType with
        ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
      have hconsumedAtSort := VEnv.IsDefEqU.of_l
        Hchecking.tr.wf hDelta.toCtx
        (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
          first' consumed') hwrapAtSort.hasType.2
      exact ⟨consumed', hconsumed, hconsumedType, u,
        hwrapAtSort.trans_l Hchecking.tr.wf hDelta.toCtx hconsumedAtSort⟩
    · subst name
      rcases Hchecking.typeAnnotationWrappers.autoParam.applicationDefEq
          Hchecking hDelta hnoBV htr with ⟨first', hfirst, hwrap⟩
      rcases htype with ⟨u, hsourceType⟩
      have hwrapAtSort :=
        hwrap.of_l Hchecking.tr.wf hDelta.toCtx hsourceType
      have hfirstType : venv.IsType Us.length Delta.toCtx first' :=
        ⟨u, hwrapAtSort.hasType.2⟩
      rcases ih hfirst hfirstType with
        ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
      have hconsumedAtSort := VEnv.IsDefEqU.of_l
        Hchecking.tr.wf hDelta.toCtx
        (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
          first' consumed') hwrapAtSort.hasType.2
      exact ⟨consumed', hconsumed, hconsumedType, u,
        hwrapAtSort.trans_l Hchecking.tr.wf hDelta.toCtx hconsumedAtSort⟩
  case case2 =>
    rcases htype with ⟨u, hsourceType⟩
    exact ⟨source', htr, ⟨u, hsourceType⟩, u, hsourceType⟩
  case case3 name levels arg hannotation ih =>
      simp only [Bool.or_eq_true, beq_iff_eq] at hannotation
      rcases hannotation with hout | hsemi
      · subst name
        rcases Hchecking.typeAnnotationWrappers.outParam.applicationDefEq
            Hchecking hDelta hnoBV htr with ⟨arg', harg, hwrap⟩
        rcases htype with ⟨u, hsourceType⟩
        have hwrapAtSort :=
          hwrap.of_l Hchecking.tr.wf hDelta.toCtx hsourceType
        have hargType : venv.IsType Us.length Delta.toCtx arg' :=
          ⟨u, hwrapAtSort.hasType.2⟩
        rcases ih harg hargType with
          ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
        have hconsumedAtSort := VEnv.IsDefEqU.of_l
          Hchecking.tr.wf hDelta.toCtx
          (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
            arg' consumed') hwrapAtSort.hasType.2
        exact ⟨consumed', hconsumed, hconsumedType, u,
          hwrapAtSort.trans_l Hchecking.tr.wf hDelta.toCtx hconsumedAtSort⟩
      · subst name
        rcases Hchecking.typeAnnotationWrappers.semiOutParam.applicationDefEq
            Hchecking hDelta hnoBV htr with ⟨arg', harg, hwrap⟩
        rcases htype with ⟨u, hsourceType⟩
        have hwrapAtSort :=
          hwrap.of_l Hchecking.tr.wf hDelta.toCtx hsourceType
        have hargType : venv.IsType Us.length Delta.toCtx arg' :=
          ⟨u, hwrapAtSort.hasType.2⟩
        rcases ih harg hargType with
          ⟨consumed', hconsumed, hconsumedType, v, hconsumedEq⟩
        have hconsumedAtSort := VEnv.IsDefEqU.of_l
          Hchecking.tr.wf hDelta.toCtx
          (⟨.sort v, hconsumedEq⟩ : venv.IsDefEqU Us.length Delta.toCtx
            arg' consumed') hwrapAtSort.hasType.2
        exact ⟨consumed', hconsumed, hconsumedType, u,
          hwrapAtSort.trans_l Hchecking.tr.wf hDelta.toCtx hconsumedAtSort⟩
  case case4 | case5 =>
    rcases htype with ⟨u, hsourceType⟩
    exact ⟨source', htr, ⟨u, hsourceType⟩, u, hsourceType⟩
/-- The ordinary inductive-checker annotation boundary is discharged by the
persisted production wrapper invariant. -/
theorem consumeTypeAnnotationsCompat : VerifyInductive.ConsumeTypeAnnotationsCompat := by
  intro c Hc dom source' htr htype
  rcases consumeTypeAnnotationsSemantic Hc.checking Hc.mlctx_wf.tr.wf
      Hc.mlctx.noBV htr htype with
    ⟨consumed', hconsumed, hconsumedType, u, hsourceEq⟩
  exact ⟨consumed', {
    source := htr
    consumed := hconsumed
    isType := hconsumedType
    source_defeq := ⟨u, hsourceEq⟩ }⟩

/-- The generated-recursor annotation boundary is the same semantic theorem
at the generated universe list. -/
theorem recursorConsumeTypeAnnotationsCompat :
    VerifyInductive.RecursorConsumeTypeAnnotationsCompat := by
  intro c recLparams R dom source' htr htype
  rcases consumeTypeAnnotationsSemantic R.checking R.mlctx_wf.tr.wf
      R.mlctx.noBV htr htype with
    ⟨consumed', hconsumed, hconsumedType, u, hsourceEq⟩
  exact ⟨consumed', {
    source := htr
    consumed := hconsumed
    isType := hconsumedType
    source_defeq := ⟨u, hsourceEq⟩ }⟩

end Lean4Lean
