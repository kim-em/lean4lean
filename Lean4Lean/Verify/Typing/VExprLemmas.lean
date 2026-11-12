import Lean4Lean.Theory.Typing.Injectivity

/-! # Abstract expression lemmas

Lemmas about `VExpr` application spines, forall arities and forall telescopes.
-/

namespace Lean4Lean
open Lean
variable {venv : VEnv}

/-- A lift over more binders than the instantiation depth is cancelled one step. -/
@[simp] theorem _root_.Lean4Lean.VExpr.inst_liftN_lt (e a : VExpr) {k m : Nat} (h : k < m) :
    (VExpr.liftN m e).inst a k = VExpr.liftN (m - 1) e := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 + k := ⟨m - 1 - k, by omega⟩
  rw [← VExpr.liftN'_liftN_lo e (n + 1) k, VExpr.inst_liftN', VExpr.liftN'_liftN_lo]
  congr 1; omega

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem VExpr.piArity_mkApps_const (n : Name) (ls : List VLevel) :
    ∀ (args : List VExpr) (f : VExpr), (f = .const n ls ∨ ∃ a b, f = .app a b) →
      (VExpr.mkApps f args).piArity = 0
  | [], f, h => by
    rcases h with rfl | ⟨a, b, rfl⟩ <;> rfl
  | a :: as, f, _ => VExpr.piArity_mkApps_const n ls as (.app f a) (.inr ⟨_, _, rfl⟩)

theorem VExpr.piArity_wrapForalls_mkApps_const (doms args : List VExpr) (n : Name)
    (ls : List VLevel) :
    (VExpr.wrapForalls doms (VExpr.mkApps (.const n ls) args)).piArity = doms.length := by
  induction doms with
  | nil => exact VExpr.piArity_mkApps_const n ls args _ (.inl rfl)
  | cons d ds ih => simp [VExpr.wrapForalls, VExpr.piArity] at ih ⊢; exact ih

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Rebuilding an expression from its application head and left-to-right
argument list is exact. -/
theorem VExpr.mkApps_getAppFnArgs (e : VExpr) :
    let (fn, args) := e.getAppFnArgs
    VExpr.mkApps fn args = e := by
  exact _root_.Lean4Lean.VExpr.mkApps_getAppFnArgs e

/-- A successful `takeForalls` peels exactly `arity` binders. -/
theorem VExpr.takeForalls_rebuild
    (H : type.takeForalls arity = some (domains, result)) :
    type = VExpr.wrapForalls domains result ∧ domains.length = arity := by
  induction arity generalizing type domains result with
  | zero =>
    change some ([], type) = some (domains, result) at H
    have hp : ([], type) = (domains, result) := Option.some.inj H
    cases hp
    exact ⟨rfl, rfl⟩
  | succ arity ih =>
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls arity with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rcases out with ⟨tailDomains, tailResult⟩
        rw [VExpr.takeForalls, htail] at H
        change some (domain :: tailDomains, tailResult) =
          some (domains, result) at H
        have hp : (domain :: tailDomains, tailResult) =
            (domains, result) := Option.some.inj H
        cases hp
        rcases ih htail with ⟨hrebuild, hlength⟩
        exact ⟨by simp [VExpr.wrapForalls, hrebuild], by simp [hlength]⟩
    | _ => simp [VExpr.takeForalls] at H

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem VExpr.piArity_eq_forallArity : ∀ e : VExpr, e.piArity = e.forallArity
  | .forallE _ b => by simp [VExpr.piArity, VExpr.forallArity, VExpr.piArity_eq_forallArity b]
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .proj _ _ _ => rfl

end VerifyInductive

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Changing only the domains of a closed telescope along a context
conversion preserves the telescope up to definitional equality. -/
theorem VExpr.wrapForalls_domains_defeqCtx {env : VEnv} {U : Nat} (henv : env.WF) :
    ∀ {P Q : List VExpr} {Y : VExpr},
      VEnv.IsDefEqCtx env U [] P.reverse Q.reverse →
      env.IsType U Q.reverse Y →
      env.IsDefEqU U [] (VExpr.wrapForalls P Y) (VExpr.wrapForalls Q Y) := by
  suffices H : ∀ L : List VExpr, ∀ {P Q : List VExpr} {Y : VExpr}, P.reverse = L →
      VEnv.IsDefEqCtx env U [] P.reverse Q.reverse →
      env.IsType U Q.reverse Y →
      env.IsDefEqU U [] (VExpr.wrapForalls P Y) (VExpr.wrapForalls Q Y) from
    fun {P Q Y} hPQ hY => H P.reverse (P := P) (Q := Q) (Y := Y) rfl hPQ hY
  intro L
  induction L with
  | nil =>
    intro P Q Y hP hPQ hY
    have hP' : P = [] := by simpa using hP
    subst hP'
    have hlen := hPQ.length_eq
    have hQ : Q = [] := by simpa using hlen.symm
    subst hQ
    obtain ⟨u, h⟩ := hY
    exact ⟨_, h⟩
  | cons A L' ih =>
    intro P Q Y hP hPQ hY
    have hP' : P = L'.reverse ++ [A] := by
      rw [← List.reverse_reverse P, hP]; simp
    subst hP'
    rcases List.eq_nil_or_concat Q with hQ | ⟨Q', B, hQ⟩
    · subst hQ
      have hlen := hPQ.length_eq
      simp at hlen
    rw [List.concat_eq_append] at hQ
    subst hQ
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.reverse_reverse] at hPQ hY
    cases hPQ with
    | succ hctx hAB =>
    have hAB' := hAB.defeqDFC henv.ordered hctx
    have hQctx : OnCtx Q'.reverse (env.IsType U) := (hctx.symm henv.ordered).isType
    obtain ⟨v, hYB⟩ := hY
    have hYA : env.HasType U (A :: Q'.reverse) Y (.sort v) :=
      hYB.defeqDFC henv.ordered (.succ .zero hAB'.symm)
    have hforallA : env.IsType U Q'.reverse (.forallE A Y) :=
      ⟨_, .forallEDF hAB'.hasType.1 hYA⟩
    have hfirst := ih (P := L'.reverse) (by simp) (by simpa using hctx) hforallA
    obtain ⟨level, hsecond⟩ := VExpr.wrapForalls_defeq (domains := Q') (Γ := [])
      (by simpa using hQctx)
      (by simpa using (VEnv.IsDefEq.forallEDF hAB' hYA))
    simp only [VExpr.wrapForalls_append]
    exact hfirst.trans henv trivial ⟨_, by simpa [VExpr.wrapForalls] using hsecond⟩

/-- Closing definitionally equal bodies over definitionally equal telescopes gives
definitionally equal types. -/
theorem VExpr.wrapForalls_defeqCtx {env : VEnv} {U : Nat} (henv : env.WF)
    {P Q : List VExpr} {X Y : VExpr}
    (hPQ : VEnv.IsDefEqCtx env U [] P.reverse Q.reverse)
    (hY : env.IsType U Q.reverse Y)
    (hXY : env.IsDefEqU U Q.reverse X Y) :
    env.IsDefEqU U [] (VExpr.wrapForalls P X) (VExpr.wrapForalls Q Y) := by
  have hQP := hPQ.symm henv.ordered
  have hXY' := hXY.defeqDFC henv.ordered hQP
  have hY' := hY.defeqDFC henv.ordered hQP
  obtain ⟨u, hYty⟩ := hY'
  have hXYsort := hXY'.of_r henv hPQ.isType hYty
  obtain ⟨level, hbody⟩ := VExpr.wrapForalls_defeq (domains := P) (Γ := [])
    (by simpa using hPQ.isType) (by simpa using hXYsort)
  exact VEnv.IsDefEqU.trans henv trivial ⟨_, hbody⟩
    (VExpr.wrapForalls_domains_defeqCtx henv hPQ hY)

/-- Application spines of equal length are injective in head and arguments. -/
theorem VExpr.mkApps_inj {f g : VExpr} {l₁ l₂ : List VExpr} (hlen : l₁.length = l₂.length)
    (h : VExpr.mkApps f l₁ = VExpr.mkApps g l₂) : f = g ∧ l₁ = l₂ := by
  induction l₁ generalizing f g l₂ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => simp at hlen
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b l₂ =>
      have h' : VExpr.mkApps (.app f a) l₁ = VExpr.mkApps (.app g b) l₂ := h
      obtain ⟨hfg, hl⟩ := ih (by simpa using hlen) h'
      cases hfg
      exact ⟨rfl, by rw [hl]⟩

theorem VExpr.forallArity_app (f a : VExpr) : (VExpr.app f a).forallArity = 0 := rfl

end Lean4Lean.VerifyInductive

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Applying a complete telescope to as many arguments as it has domains
undoes a weakening of the residual by those binders.  The domain values may
be dependent; they disappear from the conclusion because the weakened
residual does not depend on any of the newly inserted variables. -/
theorem VExpr.applyForallType_wrapForalls_liftN
    (domains args : List VExpr) (result : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains (result.liftN domains.length 0)) args =
      result := by
  induction args generalizing domains result with
  | nil =>
      have hdomains : domains = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst domains
      simp [VExpr.applyForallType, VExpr.wrapForalls]
  | cons arg args ih =>
      cases domains with
      | nil => simp at hlength
      | cons domain domains =>
          have htail : args.length = domains.length := by
            simpa using Nat.succ.inj hlength
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (result.liftN (domains.length + 1) 0)).inst arg) args = result
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [VExpr.inst_liftN_lo]
          simpa only [VExpr.instForallDomains_length] using
            ih (VExpr.instForallDomains domains arg 0) result (by
              simpa using htail)

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A type definitionally equal to a sort has no outer forall binders: if
`type.takeForalls n` succeeds then `n = 0`. -/
theorem VExpr.takeForalls_eq_zero_of_defEqSort
    {env : VEnv} {U : Nat} {ctx : List VExpr}
    {type : VExpr} {n : Nat} {domains : List VExpr}
    {result : VExpr} {u : VLevel}
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType U))
    (Htake : type.takeForalls n = some (domains, result))
    (Hsort : env.IsDefEqU U ctx type (.sort u)) :
    n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases type <;> simp [VExpr.takeForalls] at Htake
    case forallE domain body =>
      exact False.elim
        (VEnv.IsDefEqU.sort_forallE_inv henv hctx Hsort.symm)

end VerifyInductive

end Lean4Lean
