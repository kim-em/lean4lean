import Lean4Lean.Verify.ExprUniverses
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Std.Basic

/-! Strict translation checks every universe parameter in the source syntax. -/

namespace Lean4Lean
open Lean

theorem VLevel.ofLevel_paramsIn (H : VLevel.ofLevel Us level = some target) :
    level.paramsIn Us = true := by
  induction level generalizing target with simp [VLevel.ofLevel, bind] at H
  | zero => rfl
  | succ _ ih => obtain ⟨target, h, _⟩ := H; exact ih h
  | max _ _ ih₁ ih₂ | imax _ _ ih₁ ih₂ =>
    obtain ⟨_, h₁, _, h₂, _⟩ := H
    simp [Level.paramsIn, ih₁ h₁, ih₂ h₂]
  | param name =>
    simpa [Level.paramsIn] using List.idxOf_lt_length_iff.mp H.1

theorem TrExprS.levelParamsIn (H : TrExprS env Us Δ e e') : e.levelParamsIn Us = true := by
  induction H with
  | sort hu => exact VLevel.ofLevel_paramsIn hu
  | const _ hlevels _ =>
    simp only [Expr.levelParamsIn, List.all_eq_true]
    intro level hlevel
    obtain ⟨target, _, htarget⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (List.mapM_eq_some.mp hlevels) _ hlevel
    exact VLevel.ofLevel_paramsIn htarget
  | bvar | fvar | lit => rfl
  | app _ _ _ _ ihFn ihArg | lam _ _ _ ihFn ihArg | forallE _ _ _ _ ihFn ihArg =>
    simp [Expr.levelParamsIn, ihFn, ihArg]
  | letE _ _ _ _ ihTy ihVal ihBody => simp [Expr.levelParamsIn, ihTy, ihVal, ihBody]
  | mdata _ ih | proj _ _ ih => exact ih

theorem TrExpr.levelParamsIn (H : TrExpr env Us Δ e target) : e.levelParamsIn Us = true := by
  obtain ⟨_, htr, _⟩ := H
  exact htr.levelParamsIn

theorem BetaReduce.levelParamsIn (H : BetaReduce e e')
    (hs : e.levelParamsIn params = true) : e'.levelParamsIn params = true := by
  induction H with
  | refl => exact hs
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | app _ ih =>
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hs ⊢
    exact ⟨ih hs.1, hs.2⟩
  | beta =>
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hs
    exact Expr.levelParamsIn_instantiate1 hs.1.2 hs.2
end Lean4Lean
