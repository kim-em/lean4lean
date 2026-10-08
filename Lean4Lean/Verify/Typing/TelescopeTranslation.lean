import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Environment

/-!
# Telescope-closed translations

`TelTr env Us Δ e e'` says that `e` translates to `e'` (`TrExprS`), and that the same holds after
deleting any binders of the leading `forallE` spine of `e` that the rest of the telescope does not
use. At a spine binder `∀ (x : d), b` there are two branches:

* *keep*: the body translates under the binder;
* *delete*: if `b` does not mention the binder (`b = b₀.liftLooseBVars' 0 1`), and its
  translation is a lift `b₀'.lift` (which it always is, the translation being syntactic), then
  `b₀` translates to `b₀'` without the binder.

Constructor types of every checker-built environment are telescope-closed: the verified checker's
own acceptance run of the constructor type, read in the local context without the unused binder,
derives the deleted telescope (`docs/inductives/STRENGTHENING_PLAN_2026-10-08.md`). The projection
walk of `inferProj` uses the delete branch at its non-dependent fields.
-/

namespace Lean4Lean
open Lean

variable (env : VEnv) (Us : List Name) in
inductive TelTr : VLCtx → Expr → VExpr → Prop
  | mk {Δ : VLCtx} {e : Expr} {e' : VExpr} :
    TrExprS env Us Δ e e' →
    (∀ {n d b bi d' b'}, e = .forallE n d b bi → e' = .forallE d' b' →
      TelTr ((none, .vlam d') :: Δ) b b') →
    (∀ {n d b bi d' b' b₀ b₀'}, e = .forallE n d b bi → e' = .forallE d' b' →
      b = Expr.liftLooseBVars' b₀ 0 1 → b' = VExpr.lift b₀' → TelTr Δ b₀ b₀') →
    TelTr Δ e e'

namespace TelTr

theorem toTrExprS : TelTr env Us Δ e e' → TrExprS env Us Δ e e'
  | ⟨h, _, _⟩ => h

theorem keep : TelTr env Us Δ (.forallE n d b bi) (.forallE d' b') →
    TelTr env Us ((none, .vlam d') :: Δ) b b'
  | ⟨_, h, _⟩ => h rfl rfl

theorem delete : TelTr env Us Δ (.forallE n d b bi) (.forallE d' b') →
    b = Expr.liftLooseBVars' b₀ 0 1 → b' = VExpr.lift b₀' → TelTr env Us Δ b₀ b₀'
  | ⟨_, _, h⟩, hb, hb' => h rfl rfl hb hb'

end TelTr

/-- Every constructor of the kernel environment `env` that the abstract environment `venv`
models has a telescope-closed type translation. This is the environment invariant that the
projection walk of `inferProj` reads at its non-dependent fields. -/
def CtorTelescopes (env : Lean.Kernel.Environment) (venv : VEnv) : Prop :=
  ∀ {name : Name} {ci : ConstructorVal} {ci' : VConstant},
    env.find? name = some (.ctorInfo ci) → venv.constants name = some ci' →
    TelTr venv ci.levelParams [] ci.type ci'.type

end Lean4Lean
