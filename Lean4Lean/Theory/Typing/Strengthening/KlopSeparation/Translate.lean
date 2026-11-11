import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Values

/-! # The value of a term

`pval e` is the untyped proof value of a term (`FIRST_PRINCIPLES.md` §28): a syntactic
translation in which variables, λ and application are kept, binder domains are dropped,
`Eq.refl` is `λ α a. r`, `Eq.rec` is `λ α a M m b h. case h m bot`, and everything else
(sorts, Π-types, projections, every other constant) is `bot`. It commutes with lifting and
with instantiation on the nose (`pval_liftN`, `pval_inst`) and ignores universe levels
(`pval_instL`).
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

theorem constVal_inst (c : Name) (e : PVal) (k : Nat) : (constVal c).inst e k = constVal c := by
  unfold constVal
  split
  · rfl
  · split
    · simp [recVal, PVal.inst]
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

/-- **Substitution lemma for values.** -/
theorem pval_inst (e a : VExpr) (k : Nat) : pval (e.inst a k) = (pval e).inst (pval a) k := by
  induction e generalizing k with
  | bvar i =>
    simp only [VExpr.inst, VExpr.instVar, pval, PVal.inst]
    split
    · rfl
    · split
      · exact pval_liftN ..
      · rfl
  | sort => rfl
  | const c ls => exact (constVal_inst c _ k).symm
  | app f x ihf ihx => simp [VExpr.inst, pval, PVal.inst, ihf, ihx]
  | proj => rfl
  | lam A b _ ihb => simp [VExpr.inst, pval, PVal.inst, ihb]
  | forallE => rfl

theorem pval_instL (e : VExpr) (ls : List VLevel) : pval (e.instL ls) = pval e := by
  induction e with
  | bvar i => rfl
  | sort => rfl
  | const c us => rfl
  | app f x ihf ihx => simp [VExpr.instL, pval, ihf, ihx]
  | proj => rfl
  | lam A b _ ihb => simp [VExpr.instL, pval, ihb]
  | forallE => rfl

/-- `Eq.refl α a` has a value reducing to `r`. -/
theorem pval_refl_toR (α a : VExpr) (w : VLevel) :
    PVal.ToR (pval (.app (.app (.const ``Eq.refl [w]) α) a)) := by
  refine .head (.appL .beta) (.head .beta ?_)
  exact .rfl

/-- `Eq.rec α a M m b h` reduces to `case h m bot` on values. -/
theorem pval_rec_steps (α a M m b h : VExpr) (ls : List VLevel) :
    PVal.Steps (pval (.app (.app (.app (.app (.app (.app (.const ``Eq.rec ls) α) a) M) m) b) h))
      (.case (pval h) (pval m) .bot) := by
  have e1 : constVal ``Eq.rec = recVal := by simp [constVal]
  simp only [pval, e1, recVal]
  refine .head (.appL (.appL (.appL (.appL (.appL .beta))))) ?_
  refine .head (.appL (.appL (.appL (.appL .beta)))) ?_
  refine .head (.appL (.appL (.appL .beta))) ?_
  refine .head (.appL (.appL .beta)) ?_
  refine .head (.appL .beta) ?_
  refine .head .beta ?_
  simp [PVal.inst, PVal.liftN_zero, PVal.inst_liftN]
  exact .rfl

end VEnv.Strengthening
end Lean4Lean
