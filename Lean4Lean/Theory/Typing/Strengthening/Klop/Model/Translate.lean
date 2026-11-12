import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Values

/-! # The value of a term

`pval e` is the untyped proof value of a term: a syntactic translation in which variables,
λ and application are kept, binder domains are dropped, `Eq.refl` is `λ α a. r`, `Eq.rec` is
`λ α a M m b h. case h m bot`, and everything else (sorts, Π-types, projections, every other
constant) is `bot`. It commutes with lifting (`pval_liftN`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening
open PVal

/-- The value of `Eq.refl`: `λ α a. r`. -/
def reflVal : PVal := .lam (.lam .r)

/-- The value of `Eq.rec`: `λ α a M m b h. case h m bot`. -/
def recVal : PVal :=
  .lam (.lam (.lam (.lam (.lam (.lam (.case (.var 0) (.var 2) .bot))))))

/-- The value of a constant. -/
def constVal (c : Name) : PVal :=
  if c = ``Eq.refl then reflVal else if c = ``Eq.rec then recVal else .bot

/-- The value of a term. -/
def pval : VExpr → PVal
  | .bvar i => .var i
  | .sort _ => .bot
  | .const c _ => constVal c
  | .app f a => .app (pval f) (pval a)
  | .proj _ _ _ => .bot
  | .lam _ b => .lam (pval b)
  | .forallE _ _ => .bot

theorem constVal_liftN (c : Name) (n k : Nat) : (constVal c).liftN n k = constVal c := by
  unfold constVal
  split
  · rfl
  · split
    · simp [recVal, PVal.liftN, liftVar]
    · rfl

theorem pval_liftN (e : VExpr) (n k : Nat) : pval (e.liftN n k) = (pval e).liftN n k := by
  induction e generalizing k with
  | bvar i => rfl
  | sort => rfl
  | const c ls => exact (constVal_liftN c n k).symm
  | app f a ihf iha => simp [VExpr.liftN, pval, PVal.liftN, ihf, iha]
  | proj => rfl
  | lam A b _ ihb => simp [VExpr.liftN, pval, PVal.liftN, ihb]
  | forallE => rfl

end VEnv.Strengthening
end Lean4Lean
