import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Interp

/-! # Weakening and substitution for the interpretation

`den` is compositional, so lifting a term corresponds to reindexing the valuation
(`den_liftN`) and instantiating a variable corresponds to extending it by the denotation of
the substituted term (`den_inst`). No typing is involved.
-/

namespace Lean4Lean
namespace VEnv.Strengthening
namespace UniverseTower
variable (𝕋 : UniverseTower)

/-- **Weakening.** -/
theorem den_liftN (e : VExpr) (n k : Nat) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ (e.liftN n k) = 𝕋.den (fun i => ρ (liftVar n i k)) e := by
  have hcons : ∀ (d : 𝕋.S) (k : Nat) (ρ : Nat → 𝕋.S),
      (fun i => 𝕋.cons d ρ (liftVar n i (k + 1))) = 𝕋.cons d (fun i => ρ (liftVar n i k)) := by
    intro d k ρ
    funext i
    cases i with
    | zero => simp [cons]
    | succ i => simp [cons]
  induction e generalizing k ρ with
  | bvar i => rfl
  | sort => rfl
  | const => rfl
  | app f a ihf iha => simp only [VExpr.liftN, den, ihf, iha]
  | proj => rfl
  | lam A b ihA ihb => simp only [VExpr.liftN, den, ihA, ihb, hcons]
  | forallE A B ihA ihB => simp only [VExpr.liftN, den, ihA, ihB, hcons]

theorem den_lift (e : VExpr) (d : 𝕋.S) (ρ : Nat → 𝕋.S) :
    𝕋.den (𝕋.cons d ρ) e.lift = 𝕋.den ρ e := by
  rw [VExpr.lift, den_liftN]
  congr 1
  funext i
  simp [cons]

/-- The valuation obtained by inserting the denotation of `a` at variable `k`. -/
noncomputable def instVal (ρ : Nat → 𝕋.S) (a : VExpr) (k : Nat) : Nat → 𝕋.S := fun i =>
  if i < k then ρ i else if i = k then 𝕋.den ρ (a.liftN k) else ρ (i - 1)

theorem instVal_cons (d : 𝕋.S) (ρ : Nat → 𝕋.S) (a : VExpr) (k : Nat) :
    𝕋.instVal (𝕋.cons d ρ) a (k + 1) = 𝕋.cons d (𝕋.instVal ρ a k) := by
  funext i
  cases i with
  | zero => simp [instVal, cons]
  | succ j =>
    simp only [instVal, cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
      Nat.add_sub_cancel]
    split
    · rfl
    · split
      · rw [VExpr.liftN_succ, den_lift]
      · cases j with
        | zero => omega
        | succ j' => rfl

/-- **Substitution.** -/
theorem den_inst (e a : VExpr) (k : Nat) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ (e.inst a k) = 𝕋.den (𝕋.instVal ρ a k) e := by
  induction e generalizing k ρ with
  | bvar i =>
    simp only [VExpr.inst, VExpr.instVar, den, instVal]
    split
    · rfl
    · split
      · rfl
      · rfl
  | sort => rfl
  | const => rfl
  | app f x ihf ihx => simp only [VExpr.inst, den, ihf, ihx]
  | proj => rfl
  | lam A b ihA ihb => simp only [VExpr.inst, den, ihA, ihb, instVal_cons]
  | forallE A B ihA ihB => simp only [VExpr.inst, den, ihA, ihB, instVal_cons]

/-- Substitution for the outermost variable. -/
theorem den_inst0 (e a : VExpr) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ (e.inst a) = 𝕋.den (𝕋.cons (𝕋.den ρ a) ρ) e := by
  rw [den_inst]
  congr 1
  funext i
  cases i with
  | zero => simp [instVal, cons, VExpr.liftN_zero]
  | succ j => simp [instVal, cons]

/-- Semantic β: the denotation of a β-redex is that of its contractum, when the argument
denotes an element of the domain. -/
theorem den_beta (A e a : VExpr) (ρ : Nat → 𝕋.S)
    (ha : 𝕋.mem (𝕋.den ρ a) (𝕋.El (𝕋.den ρ A))) :
    𝕋.den ρ (.app (.lam A e) a) = 𝕋.den ρ (e.inst a) := by
  rw [den_inst0]
  show 𝕋.mkApp (𝕋.mkLam _ _) _ = _
  rw [𝕋.mkApp_mkLam ha]

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
