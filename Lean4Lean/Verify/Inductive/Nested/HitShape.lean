import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.ExprHitShape

/-!
# Hit shapes for nested restoration

`ElimNestedInductive.Result.restoreNested` (`Lean4Lean/Inductive/Add.lean`) opens the first
`nparams` binders of a stored term to free variables `As` (`openRestoreParams`) and then runs
`Expr.replace (restoreNestedNode ..)`. At a node whose application head is `.const c _` with `c`
an auxiliary family or auxiliary constructor, `restoreNestedNode` returns the restored head
applied to `args.drop nparams`: it ignores the first `nparams` arguments and the universe levels
of the node. The abstract `InductiveSignature.Restoration.expr`
(`Lean4Lean/Theory/Inductive/Restoration.lean`) instead substitutes the actual first `nparams`
arguments and uses the actual levels. The two agree when, at every node headed by such a
constant (a *hit*), the first `nparams` arguments are literally the parameter variables and the
levels are literally the declaration's level parameters. This file defines that syntactic
condition.

* `Expr.HitShape heads params ls e` is the free-variable form, for terms whose parameter
  telescope has been opened to `params` (in practice `params = As.toList`, a list of fvars).
* `Expr.HitShapeB heads nparams ls d e` is the bound-variable form, for stored terms whose
  parameter telescope is closed; `d` counts the binders passed since the parameter telescope, so
  the parameter `i < nparams` is `.bvar (d + (nparams - 1 - i))` (see `Expr.hitParamBVars`).
* `Expr.LeadingBinders k e body` says `e` is `k` `forallE`/`lam` binders around `body`, and
  `Expr.HitShapeTele heads nparams ls e` says `e` is a parameter telescope of `nparams` binders
  around a `HitShapeB _ nparams _ 0` body (domains unconstrained, since restoration never
  traverses them).

Both shape predicates are inductive. A hit is introduced only by the `hitHead` constructor,
which builds `mkAppList (.const c ls) params` for `c ∈ heads`; further arguments are added by
the unrestricted `app` constructor. Consequently a spine headed by `.const c us` with
`c ∈ heads` has shape exactly when `us = ls`, its argument list is `params ++ rest`, and every
argument in `rest` has shape (`HitShape.getAppFn_const_hit_inv`,
`HitShape.of_getAppFn_const_hit`). An under-applied head constant, or a bare one when
`params ≠ []`, never has shape. The parameter arguments themselves are not required to have
shape; for the intended fvar parameters this is automatic.

The predicates say nothing about the trailing arguments beyond recursive shape, and nothing
about head constants outside `heads`.

The predicates and their structural lemmas live in `Lean4Lean/Verify/ExprHitShape.lean` (so that
the hit-shape invariant of the verified type checker can use them); this file adds the facts about
the executable parameter opening `openRestoreParams`.
-/

namespace Lean.Expr

open Lean4Lean

/-- The executable parameter opening `openRestoreParams k` on a term with `k` leading binders
appends `k` fresh fvars to `As` and returns the stripped body reverse-instantiated by them. -/
theorem openRestoreParams_eq {k : Nat} {e body : Expr} (H : LeadingBinders k e body)
    (lctx : LocalContext) (As : Array Expr) (ngen : NameGenerator)
    (out : LocalContext × Array Expr × Expr) (ngen' : NameGenerator)
    (hout : Lean4Lean.ElimNestedInductive.Result.openRestoreParams k lctx As e ngen =
      (out, ngen')) :
    ∃ fvs : List FVarId, fvs.length = k ∧ out.2.1.toList = As.toList ++ fvs.map .fvar ∧
      out.2.2 = body.instantiateRevList (fvs.map .fvar) 0 := by
  induction k generalizing e body lctx As ngen with
  | zero =>
    cases H
    simp [Lean4Lean.ElimNestedInductive.Result.openRestoreParams] at hout
    cases hout
    exact ⟨[], rfl, by simp, rfl⟩
  | succ k ih =>
    have step : ∀ {b : Expr} {n : Name} {t : Expr} {bi : BinderInfo}, LeadingBinders k b body →
        Lean4Lean.ElimNestedInductive.Result.openRestoreParams k
          (lctx.mkLocalDecl ⟨ngen.curr⟩ n t bi) (As.push (.fvar ⟨ngen.curr⟩))
          (b.instantiate1 (.fvar ⟨ngen.curr⟩)) ngen.next = (out, ngen') →
        ∃ fvs : List FVarId, fvs.length = k + 1 ∧
          out.2.1.toList = As.toList ++ fvs.map .fvar ∧
          out.2.2 = body.instantiateRevList (fvs.map .fvar) 0 := by
      intro b n t bi Hb hout
      rw [Expr.instantiate1_eq] at hout
      obtain ⟨fvs, hlen, hAs, hbody⟩ :=
        ih (Hb.instantiate1' (.fvar ⟨ngen.curr⟩) 0) _ _ _ hout
      refine ⟨⟨ngen.curr⟩ :: fvs, by simp [hlen], by simp [hAs], ?_⟩
      rw [hbody, Nat.zero_add, ← hlen]
      have := Expr.instantiateRevList_instantiate1'_fvars body ⟨ngen.curr⟩ fvs 0 0
      simp only [Nat.zero_add, Nat.add_zero] at this
      rw [this]; rfl
    cases H with
    | forallE Hb =>
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen, bind, StateT.bind, pure, StateT.pure] at hout
      exact step Hb hout
    | lam Hb =>
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen, bind, StateT.bind, pure, StateT.pure] at hout
      exact step Hb hout

/-- Opening the parameter telescope exactly as `restoreNested` does yields `nparams` fvars and a
body in free-variable form over them. -/
theorem HitShapeTele.openRestoreParams {heads : List Name} {n : Nat} {ls : List Level}
    {e : Expr} (H : HitShapeTele heads n ls e) (lctx : LocalContext) (ngen : NameGenerator)
    (out : LocalContext × Array Expr × Expr) (ngen' : NameGenerator)
    (hout : Lean4Lean.ElimNestedInductive.Result.openRestoreParams n lctx #[] e ngen =
      (out, ngen')) :
    out.2.1.size = n ∧ (∀ a ∈ out.2.1.toList, ∃ fv, a = .fvar fv) ∧
      HitShape heads out.2.1.toList ls out.2.2 := by
  obtain ⟨body, Hlead, Hbody⟩ := H
  obtain ⟨fvs, hlen, hAs, hbody⟩ := openRestoreParams_eq Hlead lctx #[] ngen out ngen' hout
  simp only [List.nil_append] at hAs
  subst hlen
  refine ⟨by rw [← Array.length_toList, hAs, List.length_map], by simp [hAs], ?_⟩
  rw [hAs, hbody]
  exact Hbody.instantiateRevList_fvars

end Lean.Expr
