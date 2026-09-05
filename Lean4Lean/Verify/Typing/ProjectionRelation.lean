import Lean4Lean.Verify.Typing.Projection
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean

open Lean

abbrev EnvTrProj (env : VEnv) (U : Nat) (Gamma : List VExpr)
    (structName : Name) (index : Nat) (major target : VExpr) : Prop :=
  TrProj (env := env) (U := U) Gamma structName index major target

namespace EnvTrProj

theorem mono
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : env ≤ env') :
    EnvTrProj env' U Gamma structName index major target := by
  cases H with
  | direct majorWF targetWF =>
      exact .direct (majorWF.mono Henv) (targetWF.mono Henv)

theorem defeqCtx
    (H : EnvTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    EnvTrProj env U GammaTwo structName index major target := by
  cases H with
  | direct majorWF targetWF =>
      exact .direct (majorWF.defeqDFC Henv Hctx) (targetWF.defeqDFC Henv Hctx)

theorem sourceWF
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma major := by
  cases H
  assumption

theorem targetWF
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma target := by
  cases H
  assumption

theorem wf
    (H : EnvTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma target :=
  H.targetWF

theorem noFreshConsts
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : OnCtx Gamma (env.IsType U)) :
    target.containsAnyConst names = false :=
  H.targetWF.noFreshConsts Henv Hfresh Hctx

theorem instL
    (H : EnvTrProj env U Gamma structName index major target)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    EnvTrProj env U' (Gamma.map (VExpr.instL substitution)) structName index
      (major.instL substitution) (target.instL substitution) := by
  cases H with
  | direct majorWF targetWF =>
      simpa [VExpr.instL] using TrProj.direct
        (majorWF.instL Hlevels) (targetWF.instL Hlevels)

theorem weakN
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    EnvTrProj env U Gamma' structName index (major.liftN n k)
      (target.liftN n k) := by
  cases H with
  | direct majorWF targetWF =>
      simpa [VExpr.liftN] using TrProj.direct
        (majorWF.weakN Henv W) (targetWF.weakN Henv W)

theorem weak'
    (H : EnvTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.Lift' n Gamma Gamma') :
    EnvTrProj env U Gamma' structName index (major.lift' n)
      (target.lift' n) := by
  cases H with
  | direct majorWF targetWF =>
      simpa [VExpr.lift'] using TrProj.direct
        (majorWF.weak' Henv W) (targetWF.weak' Henv W)

theorem instN
    (H : EnvTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    EnvTrProj env U Gamma structName index (major.inst substitution k)
      (target.inst substitution k) := by
  cases H with
  | direct majorWF targetWF =>
      simpa [VExpr.inst] using TrProj.direct
        (majorWF.instN Henv W Hsubstitution)
        (targetWF.instN Henv W Hsubstitution)

end EnvTrProj

end Lean4Lean
