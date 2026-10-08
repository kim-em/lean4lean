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

variable (env : VEnv) (Us : List Name) in
/-- Depth-bounded telescope-closed translation. `TelTrN env Us n Δ e e'` certifies the first `n`
binders of the leading `forallE` spine of `e`: at depth zero it is just `TrExprS`; at positive depth
`e` is *syntactically* a `forallE` (no `mdata` or `let` wrapper can hide a binder from the
certificate), its body is certified at depth `n - 1` under the binder (*keep*), and if the body
does not mention the binder then its translation is a lift and the lowered body is certified at
depth `n - 1` without the binder (*delete*).

Unlike `TelTr`, this certificate only speaks about binders already present in `e`: substituting a
term for a variable does not create obligations for spines exposed inside the substituted term,
so it is closed under substitution, weakening and level instantiation by ordinary transport
(`Verify/Typing/TelescopeTranslationLemmas.lean`). A constructor of `n` parameters and `m` fields
carries it at depth `n + m`, which is exactly what the projection walk of `inferProj` consumes. -/
inductive TelTrN : Nat → VLCtx → Expr → VExpr → Prop
  | zero {Δ : VLCtx} {e : Expr} {e' : VExpr} :
    TrExprS env Us Δ e e' → TelTrN 0 Δ e e'
  | succ {k : Nat} {Δ : VLCtx} {n d b bi d' b'} :
    TrExprS env Us Δ (.forallE n d b bi) (.forallE d' b') →
    TelTrN k ((none, .vlam d') :: Δ) b b' →
    (∀ b₀, b = Expr.liftLooseBVars' b₀ 0 1 → ∃ b₀', b' = VExpr.lift b₀') →
    (∀ b₀ b₀', b = Expr.liftLooseBVars' b₀ 0 1 → b' = VExpr.lift b₀' → TelTrN k Δ b₀ b₀') →
    TelTrN (k + 1) Δ (.forallE n d b bi) (.forallE d' b')

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

end Lean4Lean
