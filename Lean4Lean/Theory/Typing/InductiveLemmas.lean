import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

theorem addConsts_le {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConsts cis = some env') : env ≤ env' := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConsts] at H; subst env'; exact .rfl
  | cons ci cis ih =>
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConsts, hadd] at H
    | some env₁ =>
      simp [VEnv.addConsts, hadd] at H
      exact (VEnv.addConst_le hadd).trans (ih H)

theorem addDefEqs_le {env : VEnv} {dfs : List VDefEq} : env ≤ env.addDefEqs dfs := by
  induction dfs generalizing env with
  | nil => exact .rfl
  | cons df dfs ih =>
    exact VEnv.addDefEq_le.trans ih

theorem Ordered.addConsts {env env' : VEnv} {cis : List VConstVal} (H : Ordered env)
    (hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (hadd : env.addConsts cis = some env') : Ordered env' := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConsts] at hadd; subst env'; exact H
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConsts, hci] at hadd
    | some env₁ =>
      simp [VEnv.addConsts, hci] at hadd
      have hle := VEnv.addConst_le hci
      exact ih (.const H (hwf ci (by simp)) hci)
        (fun ci' hmem => (hwf ci' (by simp [hmem])).mono hle) hadd

theorem Ordered.addDefEqs {env : VEnv} {dfs : List VDefEq} (H : Ordered env)
    (hwf : ∀ df ∈ dfs, df.WF env) : Ordered (env.addDefEqs dfs) := by
  induction dfs generalizing env with
  | nil => exact H
  | cons df dfs ih =>
    exact ih (.defeq H (hwf df (by simp)))
      (fun df' hmem => (hwf df' (by simp [hmem])).mono VEnv.addDefEq_le)

theorem VInductBlock.WF.ordered (H : VInductBlock.WF env block)
    (henv : Ordered env) (hinstall : VInductBlock.install env block = some env') :
    Ordered env' := by
  rcases H with
    ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs,
      htypesWF, hctorsWF, hrecsWF, hrulesWF⟩
  have h1 := henv.addConsts htypesWF htypes
  have h2 := h1.addConsts hctorsWF hctors
  have h3 := h2.addConsts hrecsWF hrecs
  have h4 := h3.addDefEqs hrulesWF
  simp [VInductBlock.install, htypes, hctors, hrecs] at hinstall
  cases hinstall
  exact h4

theorem addInduct_WF (henv : Ordered env) (_hdecl : VInductDecl.WF env decl)
    (henv' : VEnv.AddInduct env decl env') : Ordered env' := by
  cases henv' with
  | intro _ _ hblock hinstall =>
    exact VInductBlock.WF.ordered hblock henv hinstall
