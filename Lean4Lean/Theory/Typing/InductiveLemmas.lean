import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

theorem addDefEqRules_le {env : VEnv} {dfs : List VDefEq} : env ≤ env.addDefEqRules dfs := by
  induction dfs generalizing env with
  | nil => exact .rfl
  | cons df dfs ih =>
      exact VEnv.addDefEq_le.trans ih

theorem Ordered.addConstVals {env env' : VEnv} {cis : List VConstVal} (H : Ordered env)
    (hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (hadd : env.addConstVals cis = some env') : Ordered env' := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConstVals] at hadd; subst env'; exact H
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at hadd
    | some env₁ =>
      simp [VEnv.addConstVals, hci] at hadd
      have hle := VEnv.addConst_le hci
      exact ih (.const H (hwf ci (by simp)) hci)
        (fun ci' hmem => (hwf ci' (by simp [hmem])).mono hle) hadd

theorem Ordered.addDefEqRules {env : VEnv} {dfs : List VDefEq} (H : Ordered env)
    (hwf : ∀ df ∈ dfs, df.WF env) : Ordered (env.addDefEqRules dfs) := by
  induction dfs generalizing env with
  | nil => exact H
  | cons df dfs ih =>
    exact ih (.defeq H (hwf df (by simp)))
      (fun df' hmem => (hwf df' (by simp [hmem])).mono VEnv.addDefEq_le)

theorem VInductBlock.WF.ordered (H : VInductBlock.WF env block)
    (hdecl : VInductDecl.WF env decl)
    (hcompile : VInductDecl.CompilesTo env decl block)
    (henv : Ordered env) (hinstall : VInductBlock.install env block = some env') :
    Ordered env' := by
  rcases H with
    ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs,
      htypesWF, hctorsWF, hrecsWF, hrulesWF⟩
  have h1 := henv.addConstVals htypesWF htypes
  have h2 := h1.addConstVals hctorsWF hctors
  have h3 := Ordered.inductProjections henv h2 hcompile.sourceNames
    hdecl.1.2.2.2.1
    hcompile.types hcompile.ctors
    hcompile.projections htypes hctors
  have h4 := h3.addConstVals hrecsWF hrecs
  have h5 := h4.addDefEqRules hrulesWF
  simp [VInductBlock.install, htypes, hctors, hrecs] at hinstall
  cases hinstall
  exact h5

theorem addInduct_WF (henv : Ordered env) (hdecl : VInductDecl.WF env decl)
    (henv' : VEnv.AddInduct env decl env') : Ordered env' := by
  cases henv' with
  | intro _ hcompile hblock hinstall =>
    exact VInductBlock.WF.ordered hblock hdecl hcompile henv hinstall
