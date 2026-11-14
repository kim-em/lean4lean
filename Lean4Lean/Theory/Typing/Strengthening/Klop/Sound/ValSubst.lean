import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Unif

/-! # Substitution on proof values

`PVal.subst_up_inst`: instantiating the bound variable of a value substituted under a binder
is substitution by the extended assignment, `(t.subst (up σ)).inst u = t.subst (consV u σ)`.
This is what turns a β-step on the value of an abstraction into the value of its body at the
extended valuation.
-/

namespace Lean4Lean
namespace VEnv.Strengthening
namespace PVal

theorem liftN_liftN (e : PVal) (n1 n2 : Nat) : (e.liftN n1).liftN n2 = e.liftN (n1 + n2) := by
  have key : ∀ (e : PVal) (k1 k2 : Nat), k1 ≤ k2 → k2 ≤ n1 + k1 →
      (e.liftN n1 k1).liftN n2 k2 = e.liftN (n1 + n2) k1 := by
    intro e
    induction e with
    | var i =>
      intro k1 k2 h1 h2
      simp only [liftN, liftVar]
      congr 1
      split
      · rw [if_pos (by omega)]
      · rw [if_neg (by omega)]; omega
    | lam b ih => intro k1 k2 h1 h2; simp [liftN, ih (k1 + 1) (k2 + 1) (by omega) (by omega)]
    | app f a ihf iha => intro k1 k2 h1 h2; simp [liftN, ihf k1 k2 h1 h2, iha k1 k2 h1 h2]
    | r => intros; rfl
    | bot => intros; rfl
    | case s u v ihs ihu ihv =>
      intro k1 k2 h1 h2; simp [liftN, ihs k1 k2 h1 h2, ihu k1 k2 h1 h2, ihv k1 k2 h1 h2]
  exact key e 0 0 (Nat.le_refl _) (Nat.zero_le _)

/-- The substitution `σ` under `k` binders. -/
def upN (k : Nat) (σ : Nat → PVal) : Nat → PVal := fun i =>
  if i < k then .var i else (σ (i - k)).liftN k

theorem upN_zero (σ : Nat → PVal) : upN 0 σ = σ := by
  funext i; simp [upN, liftN_zero]

theorem up_upN (k : Nat) (σ : Nat → PVal) : up (upN k σ) = upN (k + 1) σ := by
  funext i
  cases i with
  | zero => simp [up, upN]
  | succ i =>
    simp only [up, upN, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
    split
    · simp [liftN, liftVar, Nat.add_comm]
    · rw [liftN_liftN]

theorem up_eq_upN (σ : Nat → PVal) : up σ = upN 1 σ := by
  rw [← up_upN, upN_zero]

/-- Extend an assignment by a value for variable `0`. -/
def scons (u : PVal) (σ : Nat → PVal) : Nat → PVal
  | 0 => u
  | i + 1 => σ i

theorem subst_upN_inst (t u : PVal) (σ : Nat → PVal) (k : Nat) :
    (t.subst (upN k (up σ))).inst u k = t.subst (upN k (scons u σ)) := by
  induction t generalizing k with
  | var i =>
    simp only [subst, upN]
    split
    · rename_i h; simp [inst, h]
    · rename_i h
      by_cases hik : i = k
      · subst hik
        simp [up, scons, liftN, liftVar, inst]
      · obtain ⟨j, hj⟩ : ∃ j, i - k = j + 1 := ⟨i - k - 1, by omega⟩
        rw [hj]
        simp only [up, scons]
        rw [liftN_liftN, Nat.add_comm 1 k]
        exact inst_liftN _ _ _ _ _ (Nat.zero_le _) (by omega)
  | lam b ih => simp only [subst, inst, up_upN, ih]
  | app f a ihf iha => simp only [subst, inst, ihf, iha]
  | r => rfl
  | bot => rfl
  | case s x y ihs ihx ihy => simp only [subst, inst, ihs, ihx, ihy]

/-- **β on substituted values.** -/
theorem subst_up_inst (t u : PVal) (σ : Nat → PVal) :
    (t.subst (up σ)).inst u = t.subst (scons u σ) := by
  have := subst_upN_inst t u σ 0
  rwa [upN_zero, upN_zero] at this

end PVal

theorem consV_eq_scons (u : PVal) (w : Nat → PVal) :
    SetModel.consV u w = PVal.scons u w := by
  funext i; cases i <;> rfl

/-- The value of an abstraction applied to a value reduces to the value of the body at the
extended assignment. -/
theorem PVal.step_lam_app (b : VExpr) (A : VExpr) (w : Nat → PVal) (u : PVal) :
    PVal.Step (.app ((pval (.lam A b)).subst w) u)
      ((pval b).subst (SetModel.consV u w)) := by
  have : (pval (.lam A b)).subst w = .lam ((pval b).subst (PVal.up w)) := rfl
  rw [this, consV_eq_scons, ← PVal.subst_up_inst]
  exact .beta

end VEnv.Strengthening
end Lean4Lean
