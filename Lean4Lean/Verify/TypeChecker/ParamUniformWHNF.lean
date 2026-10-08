import Lean4Lean.Verify.TypeChecker

/-!
# Hit-shape preservation by the verified type checker

The nested-inductive restoration needs: when `whnf` or `inferType` is run on a term in which every
occurrence of a *head* constant (an auxiliary family or constructor, or a constructor mentioning
one) is applied to the parameter fvars `As` at the levels `ls` (`Expr.HitShape`), then the result
has the same property. The invariant is carried by `VState.WF` and `Methods.WF`
(`Lean4Lean/Verify/TypeChecker/Basic.lean`); this file states the consumer-facing results for
the `M`-level entry points.

Hypotheses (bundled in `VContext.HitScope pfx heads As ls P`):

* `EnvHitShape c.env heads As.length ls` (`Lean4Lean/Verify/ParamUniformEnv.lean`): constants other
  than heads, all definition values and all recursor rules avoid the heads; head types at `ls` are
  parameter telescopes around bound-variable hit shapes; recursors in the environment never
  eliminate head families or families with head constructors; projections in the environment
  respect `projHitOK`; and the checker's own primitive constants are not heads.
* `HitParams pfx As`: the parameters are fvars that the checker's name generator (prefix `pfx`,
  `` `_kernel_fresh `` for a run from the initial state) never produces.
* an up-set `P` of the local context whose declarations are in hit shape.

The input must additionally satisfy `Expr.ProjsOK (projHitOK c.env heads)` (no projections on
heads or on families with head constructors), which is preserved as well.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- `whnf` preserves hit shape (`VContext.HitBelow`), together with its correctness clauses. -/
theorem whnf.hitShape {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (whnf e) fun e₁ _ =>
      (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.HitBelow s.ngen.namePrefix e e₁ :=
  (Inner.whnf.WF_fhit he rfl).run

/-! ### Using the invariant -/

/-- The name generator of the initial checker state. -/
@[simp] theorem VState.initial_namePrefix : ({} : State).ngen.namePrefix = `_kernel_fresh := rfl

end Lean4Lean.TypeChecker
