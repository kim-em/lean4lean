import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.Environment.Recursors

/-!
# Recursor reduction

`reduceRecursor` reduces quotient eliminators and inductive recursors whose major premise is (or
converts to) a constructor application. Both are refinements of the stored equations of the abstract
environment: `VIotaRuleShape.iota_body` instantiates a stored rule at the actual arguments, and
`Quot.ind` reduces by proof irrelevance.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem Expr.isAppOfArity_three_eq_true {e : Expr} {name : Name}
    (H : e.isAppOfArity name 3 = true) :
    ∃ levels a₁ a₂ a₃, e = .app (.app (.app (.const name levels) a₁) a₂) a₃ := by
  cases e <;> simp [Expr.isAppOfArity] at H
  case app f a₃ =>
    cases f <;> simp [Expr.isAppOfArity] at H
    case app g a₂ =>
      cases g <;> simp [Expr.isAppOfArity] at H
      case app h a₁ =>
        cases h <;> simp [Expr.isAppOfArity] at H
        case const found levels =>
          subst found
          exact ⟨levels, a₁, a₂, a₃, rfl⟩

namespace TypeChecker

/-- Every visible recursor of the checking environment is aligned with the abstract environment.

TODO: derive from a `CheckingEnv` field, produced at the inductive installation boundary from the
recursor certificates (`CompletedRuleTranslationResult`) and the nested assembly, the same way
`projectionRegistry` is carried for projections. -/
theorem VContext.recursorRules (c : VContext) :
    RecursorRulesCoherent c.safety c.env.constants c.venv := by
  sorry

/-- When quotients are initialized, the abstract environment contains the quotient constants and
the `Quot.lift` equation.

TODO: derive from a `CheckingEnv` field recording the `quot` step of the environment trace
(`TrEnv'.quot` and `AddQuot`). -/
theorem VContext.quotCoherent (c : VContext) (h : c.env.quotInit = true) :
    QuotCoherent c.venv := by
  sorry

/-- Inductive type constants are rigid: no stored equation is headed by one.

TODO: derive from the environment trace once the nested auxiliary rules record their left-hand
side shape (see `IsDefEqU.structApp_inv`). -/
theorem VContext.inductRigid (c : VContext) {info : InductiveVal}
    (h : c.env.find? n = some (.inductInfo info)) : c.venv.Rigid n := by
  sorry

namespace Inner

variable {c : VContext} {s : VState}

theorem TrExprS.app_of_wf (hf : c.TrExprS f f') (ha : c.TrExprS a a')
    (hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (.app f' a')) :
    c.TrExprS (.app f a) (.app f' a') :=
  have ⟨_, _, h1, h2⟩ := hwf.app_inv c.Ewf.ordered c.Δwf.toCtx
  .app h1 h2 hf ha

/-- Assemble a translated application spine from translated pieces, given that the abstract spine
is well formed. -/
theorem TrExprS.mkAppList_of_wf : ∀ {args : List Expr} {args' : List VExpr} {f : Expr} {f' : VExpr},
    c.TrExprS f f' → List.Forall₂ c.TrExprS args args' →
    VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (VExpr.mkApps f' args') →
    c.TrExprS (f.mkAppList args) (VExpr.mkApps f' args')
  | [], _, _, _, hf, .nil, _ => hf
  | _ :: _, _, f, f', hf, .cons ha has, hwf =>
    have hwf' := VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx (f := .app f' _) hwf
    TrExprS.mkAppList_of_wf (f := .app f _) (f' := .app f' _) (TrExprS.app_of_wf hf ha hwf') has
      hwf

/-- The translated arguments of a constant application, indexed like the executable argument
array. -/
theorem AppStack.argsGet {e : Expr} {args' : List VExpr}
    (hargs : List.Forall₂ c.TrExprS e.getAppArgsList args') :
    e.getAppArgs.size = args'.length ∧
    ∀ i (hi : i < e.getAppArgs.size), c.TrExprS e.getAppArgs[i] (args'[i]'(by
      rw [← (Lean4Lean.List.Forall₂.length_eq hargs), ← Expr.getAppArgs_toList]; simpa using hi)) := by
  have hlen : e.getAppArgs.size = args'.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList, Array.length_toList]
  refine ⟨hlen, fun i hi => ?_⟩
  have := Lean4Lean.List.forall₂_getElem hargs i (by rw [← Expr.getAppArgs_toList]; simpa using hi)
    (by omega)
  simpa [← Expr.getAppArgs_toList] using this

/-- Free variables of the result of `mkAppRange` over a suffix of the argument array. -/
theorem mkAppRange_suffix_eq {e r : Expr} {i : Nat} (h : i ≤ e.getAppArgs.size) :
    mkAppRange r i e.getAppArgs.size e.getAppArgs = r.mkAppList (e.getAppArgsList.drop i) := by
  refine Expr.mkAppRange_eq (l₁ := e.getAppArgsList.take i) (l₃ := []) ?_ ?_ ?_
  · rw [Expr.getAppArgs_toList, List.append_nil, List.take_append_drop]
  · rw [List.length_take, ← Expr.getAppArgs_toList, Array.length_toList, Nat.min_eq_left h]
  · rw [List.take_append_drop, ← Expr.getAppArgs_toList, Array.length_toList]

theorem _root_.Lean4Lean.VExpr.instOuter_app_bvar (A : List VExpr) (i j : Nat)
    (hi : i < A.length) (hj : j < A.length) :
    (VExpr.app (.bvar i) (.bvar j)).instOuter A = .app A[A.length - 1 - i] A[A.length - 1 - j] := by
  simp only [VExpr.instOuter_eq_subst, VExpr.subst_app, VExpr.subst_bvar,
    VExpr.Subst.ofList_lt _ hi, VExpr.Subst.ofList_lt _ hj]

/-- Free variables of the arguments of an application are free variables of the application. -/
theorem _root_.Lean4Lean.FVarsIn.of_mem_getAppArgsList {P} {e a : Expr} (h : FVarsIn P e)
    (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  rw [← e.mkAppList_getAppArgsList, FVarsIn.mkAppList] at h
  exact h.2 a ha

/-- The translated arguments of the argument-list suffix. -/
theorem forall₂_drop {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (n : Nat) : List.Forall₂ R (l₁.drop n) (l₂.drop n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => exact .cons h (by simpa using ih 0)
    | succ n => exact ih n

/-- Inversion of the translation of a constant applied to three arguments. -/
theorem TrExprS.app3_inv {n : Name} {ls : List Level} {a1 a2 a3 : Expr} {e' : VExpr}
    (H : c.TrExprS (.app (.app (.app (.const n ls) a1) a2) a3) e') :
    ∃ ls' a1' a2' a3',
      c.TrExprS (.app (.app (.app (.const n ls) a1) a2) a3)
        (VExpr.mkApps (.const n ls') [a1', a2', a3']) ∧
      ls.mapM (VLevel.ofLevel c.lparams) = some ls' ∧
      (∃ ci, c.venv.constants n = some ci ∧ ls.length = ci.uvars) ∧
      c.TrExprS a1 a1' ∧ c.TrExprS a2 a2' ∧ c.TrExprS a3 a3' := by
  have ⟨fn', stk⟩ := AppStack.build (e := .const n ls) (as := [a1, a2, a3]) H
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have .const hlc _ hlen := stk.tr
  cases hargs with | cons ha1 h => ?_
  cases h with | cons ha2 h => ?_
  cases h with | cons ha3 h => ?_
  cases h
  exact ⟨ls', _, _, _, hfull, hls, ⟨_, hlc, hlen⟩, ha1, ha2, ha3⟩

/-- Reduction of `Quot.lift` applied to `Quot.mk`. -/
theorem quotReduceRecCont.lift.WF (he : c.TrExprS e e') {ls : List Level}
    (hfn : e.getAppFn = .const ``Quot.lift ls) (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRecCont e whnf 5 3) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h5; exact .pure nofun]
  -- the recursor spine
  have he'' : c.TrExprS ((Expr.const ``Quot.lift ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have hceq := he''.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  have .const hlc _ hlen := stk.tr
  rw [hq.lift] at hlc; cases hlc
  have hls'len : ls'.length = 2 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlen
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  refine (whnf.WF (hget 5 h5)).bind fun mk _ _ ⟨hb, mk', hmk, hmkdefeq⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  obtain ⟨lsm', a1', a2', a3', hmk3, hlsm, ⟨_, hlm, hlenm⟩, ha1, ha2, ha3⟩ :=
    TrExprS.app3_inv hmk
  replace hmkdefeq := (hmk3.uniq c.Ewf (.refl c.Ewf c.Δwf) hmk).trans c.Ewf c.Δwf hmkdefeq
  rw [hq.quotMk] at hlm; cases hlm
  have hlsm'len : lsm'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsm)).symm.trans hlenm
  have hlsm'w := VLevel.WF.of_mapM_ofLevel hlsm
  simp only [Expr.appArg!]
  rw [getElem!_pos e.getAppArgs 3 (by omega)]
  -- the abstract reduction
  have hsplit : args' = args'.take 5 ++ args'[5] :: args'.drop 6 := by
    rw [← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  have hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const ``Quot.lift ls') (args'.take 5 ++ args'[5] :: args'.drop 6)) := by
    rw [← hsplit]; exact hfull.wf c.Ewf c.Δwf
  have hmajor : c.IsDefEqU args'[5] (VExpr.mkApps (.const ``Quot.mk lsm') ([a1', a2'] ++ [a3'])) :=
    hmkdefeq.symm
  have hiota := VIotaRuleShape.iota_body c.Ewf c.Δwf.toCtx hq.liftRecursorShape (by decide)
    hq.mkConstructorShape hq.liftRuleShape hq.rigid rfl hls'w hls'len (pre := args'.take 5)
    (by simp; omega) hwf hlsm'len hlsm'w rfl rfl hmajor
  have hbody : ((hq.liftRuleShape.rhsBody.instL ls').instOuter
      ((args'.take 5).take 5 ++ [a3'])) = .app args'[3] a3' := by
    show ((VExpr.app (.bvar 2) (.bvar 0)).instL ls').instOuter _ = _
    rw [List.take_take, Nat.min_self]
    simp only [VExpr.instL]
    rw [VExpr.instOuter_app_bvar _ _ _ (by simp <;> omega) (by simp <;> omega)]
    simp only [List.length_append, List.length_take, List.length_singleton]
    rw [List.getElem_append_left (by simp <;> omega), List.getElem_take,
      List.getElem_append_right (by simp <;> omega)]
    simp only [List.length_take, List.getElem_singleton]
    have h3 : min 5 args'.length + 1 - 1 - 2 = 3 := by omega
    simp only [h3]
  rw [hbody, ← hsplit] at hiota
  have hdefeq : c.IsDefEqU e' (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    hceq.trans c.Ewf c.Δwf hiota
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    let ⟨_, h⟩ := hdefeq; ⟨_, h.hasType.2⟩
  have hr : c.TrExprS ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6))
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    TrExprS.mkAppList_of_wf (TrExprS.app_of_wf (hget 3 (by omega)) ha3
      (VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx hrwf)) (forall₂_drop hargs 6) hrwf
  have hfv : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨⟨?_, ?_⟩, fun a ha => hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)⟩
    · exact hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _)
    · have := hb P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact this.2
  have main : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) ∧
      c.TrExpr ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) e' :=
    ⟨hfv, (hr.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq.symm⟩
  split
  · rw [mkAppRange_suffix_eq (by omega)]
    exact .pure fun _ h => Option.some.inj h ▸ main
  · rename_i h6
    rw [List.drop_eq_nil_of_le (by rw [← Expr.getAppArgs_toList, Array.length_toList]; omega)] at main
    exact .pure fun _ h => Option.some.inj h ▸ main

/-- Reduction of `Quot.ind` applied to `Quot.mk`, by proof irrelevance. -/
theorem quotReduceRecCont.ind.WF (he : c.TrExprS e e') {ls : List Level}
    (hfn : e.getAppFn = .const ``Quot.ind ls) (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRecCont e whnf 4 3) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h4; exact .pure nofun]
  -- the eliminator spine
  have he'' : c.TrExprS ((Expr.const ``Quot.ind ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have hceq := he''.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  have .const hlc _ hlen := stk.tr
  rw [hq.ind] at hlc; cases hlc
  have hls'len : ls'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlen
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  refine (whnf.WF (hget 4 h4)).bind fun mk _ _ ⟨hb, mk', hmk, hmkdefeq⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  obtain ⟨lsm', a1', a2', a3', hmk3, hlsm, ⟨_, hlm, hlenm⟩, ha1, ha2, ha3⟩ :=
    TrExprS.app3_inv hmk
  replace hmkdefeq := (hmk3.uniq c.Ewf (.refl c.Ewf c.Δwf) hmk).trans c.Ewf c.Δwf hmkdefeq
  rw [hq.quotMk] at hlm; cases hlm
  have hlsm'len : lsm'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsm)).symm.trans hlenm
  have hlsm'w := VLevel.WF.of_mapM_ofLevel hlsm
  simp only [Expr.appArg!]
  rw [getElem!_pos e.getAppArgs 3 (by omega)]
  -- the abstract reduction: `Quot.ind p q ≡ p a` by proof irrelevance
  have hsplit : args' = args'.take 5 ++ args'.drop 5 := (List.take_append_drop _ _).symm
  have hwf5 : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5)) := by
    have := hfull.wf c.Ewf c.Δwf
    rw [hsplit, VExpr.mkApps_append] at this
    exact VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx this
  have hdefeq : c.IsDefEqU (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5))
      (.app args'[3] a3') := by
    have h5 : args'.take 5 = [args'[0], args'[1], args'[2], args'[3], args'[4]] := by
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.getElem_take]
        match i, h2 with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
    rw [h5] at hwf5 ⊢
    exact hq.ind_defeq c.Ewf c.Δwf.toCtx hls'w hls'len hlsm'w hlsm'len hwf5
      (hmk3.wf c.Ewf c.Δwf) hmkdefeq
  have hdefeq' : c.IsDefEqU e' (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) := by
    refine hceq.trans c.Ewf c.Δwf ?_
    have hwf' : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
        (VExpr.mkApps (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5)) (args'.drop 5)) := by
      rw [← VExpr.mkApps_append, ← hsplit]
      exact hfull.wf c.Ewf c.Δwf
    have := VEnv.IsDefEqU.mkApps_congr_left c.Ewf c.Δwf.toCtx hdefeq hwf'
    rw [← VExpr.mkApps_append, ← hsplit] at this
    exact this
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) :=
    let ⟨_, h⟩ := hdefeq'; ⟨_, h.hasType.2⟩
  have hr : c.TrExprS ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5))
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) :=
    TrExprS.mkAppList_of_wf (TrExprS.app_of_wf (hget 3 (by omega)) ha3
      (VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx hrwf)) (forall₂_drop hargs 5) hrwf
  have hfv : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨⟨?_, ?_⟩, fun a ha => hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)⟩
    · exact hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _)
    · have := hb P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact this.2
  have main : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) ∧
      c.TrExpr ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) e' :=
    ⟨hfv, (hr.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq'.symm⟩
  split
  · rw [mkAppRange_suffix_eq (by omega)]
    exact .pure fun _ h => Option.some.inj h ▸ main
  · rename_i h5
    rw [List.drop_eq_nil_of_le (by rw [← Expr.getAppArgs_toList, Array.length_toList]; omega)] at main
    exact .pure fun _ h => Option.some.inj h ▸ main

/-- Quotient reduction refines the abstract environment. -/
theorem quotReduceRec.WF (he : c.TrExprS e e') (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRec
  split <;> [rename_i fn ls hfn; exact .pure nofun]
  split
  · rename_i h; rw [beq_iff_eq] at h; subst h
    exact quotReduceRecCont.lift.WF he hfn hq
  split
  · rename_i h; rw [beq_iff_eq] at h; subst h
    exact quotReduceRecCont.ind.WF he hfn hq
  exact .pure nofun

theorem forall₂_take {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (n : Nat) : List.Forall₂ R (l₁.take n) (l₂.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => simp
    | succ n => exact .cons h (ih n)

/-- The final phase of inductive recursor reduction refines the stored rule, given a converted
major premise that translates to something definitionally equal to the original one. -/
theorem inductiveReduceRecTail.WF {info : RecursorVal} {recFn : Name} {ls : List Level}
    {ls' : List VLevel} {args' : List VExpr}
    (he : c.TrExprS e e') (hfn : e.getAppFn = .const recFn ls)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hls : ls.mapM (VLevel.ofLevel c.lparams) = some ls')
    (hargs : List.Forall₂ c.TrExprS e.getAppArgsList args')
    (hfull : c.TrExprS e (VExpr.mkApps (.const recFn ls') args'))
    (hmaj : info.getMajorIdx < e.getAppArgs.size)
    {major₂ : Expr} (hfv : c.FVarsBelow e.getAppArgs[info.getMajorIdx] major₂)
    (hm : c.TrExpr major₂ (args'[info.getMajorIdx]'(by
      rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList]; simpa using hmaj))) :
    ∀ r, inductiveReduceRecTail info ls e.getAppArgs major₂ = some r →
      c.FVarsBelow e r ∧ c.TrExpr r e' := by
  intro r hr
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  -- the rule for the constructor at the head of the major premise
  unfold inductiveReduceRecTail at hr
  simp only [bind, Option.bind] at hr
  split at hr <;> [rename_i rule hrule; cases hr]
  unfold getRecRuleFor at hrule
  split at hrule <;> [rename_i fn lsc hmfn; cases hrule]
  have hmem := List.mem_of_find?_eq_some hrule
  have hctor : rule.ctor = fn := by simpa using List.find?_some hrule
  subst hctor
  split at hr <;> [cases hr; rename_i hsizeM]
  split at hr <;> [cases hr; rename_i hlsLen]
  simp only [bne_iff_ne, ne_eq, Classical.not_not] at hsizeM hlsLen
  simp only [RecursorVal.getFirstIndexIdx] at hr
  -- the environment facts
  have hceq := he.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have hfullS : c.TrExprS ((Expr.const recFn ls).mkAppList e.getAppArgsList)
      (VExpr.mkApps (.const recFn ls') args') := by
    rwa [← hfn, e.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hfullS
  have .const hlc _ hlen := stk.tr
  obtain ⟨hname, hsafe, hlpLen, -⟩ := c.trenv.find?_uniq hinfo hlc
  have hname' : info.name = recFn := hname
  subst hname'
  have hfindC : c.env.constants.find? info.name = some (.recInfo info) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  obtain ⟨⟨indLevels, hcnp, ⟨Hrec⟩, hrigid, hrules⟩, -⟩ := c.recursorRules hfindC hsafe
  obtain ⟨df, ⟨Hrule⟩, hrhs, ctorUvars, hIL, ⟨Hctor⟩⟩ := hrules rule hmem
  have hls'len : ls'.length = info.levelParams.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlsLen
  have hmaj' : info.numParams + info.numMotives + info.numMinors + info.numIndices <
      args'.length := by
    simpa [RecursorVal.getMajorIdx, hsize] using hmaj
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  -- the converted major premise as a constructor application
  have ⟨m₂', hm₂, hmdefeq⟩ := hm
  have hm₂S : c.TrExprS ((Expr.const rule.ctor lsc).mkAppList major₂.getAppArgsList) m₂' := by
    rwa [← hmfn, major₂.mkAppList_getAppArgsList]
  have ⟨_, mstk⟩ := AppStack.build hm₂S
  obtain ⟨lsc', MA', hlsc, rfl, hMargs, hMfull⟩ := mstk.constantApplication
  have ⟨hMsize, hMget⟩ := AppStack.argsGet hMargs
  have .const hlcc _ hlenc := mstk.tr
  rw [Hctor.const] at hlcc; cases hlcc
  have hlsc'len : lsc'.length = ctorUvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsc)).symm.trans hlenc
  have hlsc'w := VLevel.WF.of_mapM_ofLevel hlsc
  have hmajor : c.IsDefEqU (args'[info.getMajorIdx]'(by omega))
      (VExpr.mkApps (.const rule.ctor lsc') (MA'.take info.numParams ++ MA'.drop info.numParams)) := by
    rw [List.take_append_drop]
    exact hmdefeq.symm.trans c.Ewf c.Δwf (hm₂S.uniq c.Ewf (.refl c.Ewf c.Δwf) hMfull)
  have hMlen : MA'.length = info.numParams + rule.nfields := by rw [← hMsize]; exact hsizeM
  -- the abstract reduction
  have hsplit : args' = args'.take info.getMajorIdx ++
      (args'[info.getMajorIdx]'(by omega)) :: args'.drop (info.getMajorIdx + 1) := by
    rw [← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  have hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const info.name ls') (args'.take info.getMajorIdx ++
        (args'[info.getMajorIdx]'(by omega)) :: args'.drop (info.getMajorIdx + 1))) := by
    rw [← hsplit]; exact hfull.wf c.Ewf c.Δwf
  have hiota := Hrule.iota c.Ewf c.Δwf.toCtx Hrec hcnp Hctor hrigid hIL hls'w hls'len
    (pre := args'.take info.getMajorIdx)
    (by simp [RecursorVal.getMajorIdx]; omega) hwf hlsc'len hlsc'w
    (by simp; omega) (by simp; omega) hmajor
  rw [← hsplit, List.take_take, Nat.min_eq_left (by simp [RecursorVal.getMajorIdx])] at hiota
  -- the instantiated rule right-hand side
  have hrhs₀ := hrhs.instL c.Ewf (by trivial) hls hlsLen.symm
  have hrhs₀' := hrhs₀.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
  have hclosed : (df.rhs.instL ls').ClosedN 0 :=
    VExpr.WF.closedN c.Ewf.ordered (hrhs₀.wf (Δ := [])) trivial
  rw [hclosed.liftN_eq (Nat.zero_le _)] at hrhs₀'
  have ⟨r₀', hr₀, hr₀defeq⟩ := hrhs₀'
  -- the executable result as an application spine
  generalize hfiiE : info.numParams + info.numMotives + info.numMinors = fii at *
  have hfii : fii ≤ e.getAppArgs.size := by
    simp [RecursorVal.getMajorIdx] at hmaj; omega
  have hr1 : mkAppRange (rule.rhs.instantiateLevelParams info.levelParams ls) 0
      fii e.getAppArgs =
      (rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList
        (e.getAppArgsList.take fii) := by
    refine Expr.mkAppRange_eq (l₁ := []) (l₃ := e.getAppArgsList.drop fii)
      ?_ rfl ?_
    · rw [Expr.getAppArgs_toList, List.nil_append, List.take_append_drop]
    · rw [List.nil_append, List.length_take, ← Expr.getAppArgs_toList, Array.length_toList,
        Nat.min_eq_left hfii]
  have hr2 : ∀ f, mkAppRange f (major₂.getAppArgs.size - rule.nfields) major₂.getAppArgs.size
      major₂.getAppArgs = f.mkAppList (major₂.getAppArgsList.drop info.numParams) := by
    intro f
    rw [mkAppRange_suffix_eq (by omega)]
    congr 2; omega
  generalize hA : e.getAppArgsList.take fii ++
    major₂.getAppArgsList.drop info.numParams ++ e.getAppArgsList.drop (info.getMajorIdx + 1) = A
  generalize hA' : args'.take fii ++ MA'.drop info.numParams ++
    args'.drop (info.getMajorIdx + 1) = A'
  have hAtr : List.Forall₂ c.TrExprS A A' := by
    rw [← hA, ← hA']
    exact ((forall₂_take hargs _).append' (forall₂_drop hMargs _)).append' (forall₂_drop hargs _)
  rw [hA'] at hiota
  have hdefeq : c.IsDefEqU e' (VExpr.mkApps r₀' A') := by
    refine hceq.trans c.Ewf c.Δwf (hiota.trans c.Ewf c.Δwf ?_)
    exact VEnv.IsDefEqU.mkApps_congr_left c.Ewf c.Δwf.toCtx hr₀defeq.symm
      (let ⟨_, h⟩ := hiota; ⟨_, h.hasType.2⟩)
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (VExpr.mkApps r₀' A') :=
    let ⟨_, h⟩ := hdefeq; ⟨_, h.hasType.2⟩
  have hrS : c.TrExprS ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A)
      (VExpr.mkApps r₀' A') :=
    TrExprS.mkAppList_of_wf hr₀ hAtr hrwf
  have hfvr : c.FVarsBelow e ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨hrhs₀.fvarsIn.mono nofun, fun a ha => ?_⟩
    rw [← hA] at ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact hfe.of_mem_getAppArgsList (List.mem_of_mem_take ha)
    · have hmaj' := hfv P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact hmaj'.of_mem_getAppArgsList (List.mem_of_mem_drop ha)
    · exact hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)
  have main : c.FVarsBelow e ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) ∧
      c.TrExpr ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) e' :=
    ⟨hfvr, (hrS.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq.symm⟩
  rw [hr1, hr2] at hr
  split at hr
  · rw [mkAppRange_suffix_eq (by omega), ← Expr.mkAppList_append, ← Expr.mkAppList_append,
      ← List.append_assoc, hA, Option.pure_def] at hr
    cases hr
    exact main
  · rename_i hlt
    have hle : e.getAppArgsList.length ≤ info.getMajorIdx + 1 := by
      rw [← Expr.getAppArgs_toList, Array.length_toList]; exact Nat.le_of_not_lt hlt
    rw [← Expr.mkAppList_append, Option.pure_def] at hr
    rw [List.drop_eq_nil_of_le (as := e.getAppArgsList) hle, List.append_nil] at hA
    rw [hA] at hr
    cases hr
    exact main

end Inner
end TypeChecker
end Lean4Lean
