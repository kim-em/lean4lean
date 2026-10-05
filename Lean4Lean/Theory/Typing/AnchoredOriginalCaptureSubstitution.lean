import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Simultaneous inverse-substitution syntax for an original capture spine.
All operands are substituted at once, so a traversal can stay in the original
typing tree instead of inventing typings of intermediate residual templates.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr
set_option backward.isDefEq.respectTransparency false

def CaptureSelected (arguments : List VExpr) (depth : Nat) (template : VExpr) : Prop :=
  ∃ index, index < arguments.length ∧ template = .bvar (depth + index)

theorem capture_selected (arguments : List VExpr) (depth index : Nat)
    (bound : index < arguments.length) :
    (VExpr.bvar (depth + index)).subst ((Subst.ofList arguments).liftN depth) =
      arguments[arguments.length - 1 - index].lift' (.skipN .refl depth) := by
  simp only [subst_bvar, Subst.liftN_apply, show ¬depth + index < depth by omega,
    if_false, Nat.add_sub_cancel_left, Subst.ofList, dif_pos bound]
  exact (lift'_consN_skipN (k := 0)).symm

theorem capture_local (arguments : List VExpr) (bound : index < depth) :
    (VExpr.bvar index).subst ((Subst.ofList arguments).liftN depth) = .bvar index := by
  simp only [subst_bvar, Subst.liftN_apply, bound, if_pos]

theorem capture_external (arguments : List VExpr) (depth index : Nat)
    (bound : depth ≤ index) :
    (VExpr.bvar (index + arguments.length)).subst ((Subst.ofList arguments).liftN depth) =
      .bvar index := by
  rw [subst_bvar, Subst.liftN_apply, if_neg (by omega)]
  rw [Subst.ofList, dif_neg (show ¬index + arguments.length - depth < arguments.length by omega)]
  have equal : index + arguments.length - depth - arguments.length = index - depth := by omega
  rw [equal]
  simp only [VExpr.liftN, liftVar_base']
  congr 1
  omega

private theorem unselected_var (arguments : List VExpr) (depth index : Nat)
    (notSelected : ¬CaptureSelected arguments depth (.bvar index)) :
    (VExpr.bvar index).subst ((Subst.ofList arguments).liftN depth) =
      .bvar (if index < depth then index else index - arguments.length) := by
  by_cases localIndex : index < depth
  · simpa only [localIndex, if_pos] using capture_local arguments localIndex
  · have outside : depth + arguments.length ≤ index := by
      by_cases h : depth + arguments.length ≤ index
      · exact h
      · exact False.elim (notSelected ⟨index - depth, by omega, by congr 1; omega⟩)
    have equal : index - arguments.length + arguments.length = index := by omega
    simpa only [equal, localIndex, if_false] using
      capture_external arguments depth (index - arguments.length) (by omega)

theorem capture_bvar_inv
    (equal : VExpr.bvar index = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) :
    template = .bvar (if index < depth then index else index + arguments.length) := by
  cases template <;> simp only [subst, reduceCtorEq] at equal
  rename_i slot
  have h := unselected_var arguments depth slot notSelected
  have eqIndex := VExpr.bvar.inj (equal.trans h)
  by_cases localIndex : slot < depth
  · simp only [localIndex, if_pos] at eqIndex
    subst index
    simp only [localIndex, if_pos]
  · have outside : depth + arguments.length ≤ slot := by
      by_cases h : depth + arguments.length ≤ slot
      · exact h
      · exact False.elim (notSelected ⟨slot - depth, by omega, by congr 1; omega⟩)
    simp only [localIndex, if_false] at eqIndex
    have resultOutside : ¬index < depth := by omega
    simp only [resultOutside, if_false]
    congr 1
    omega

theorem capture_const_inv
    (equal : VExpr.const name levels = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) : template = .const name levels := by
  cases template <;> simp only [subst, reduceCtorEq, const.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · obtain ⟨rfl, rfl⟩ := equal; rfl

theorem capture_sort_inv
    (equal : VExpr.sort level = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) : template = .sort level := by
  cases template <;> simp only [subst, reduceCtorEq, sort.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · exact equal.symm ▸ rfl

theorem capture_app_inv
    (equal : VExpr.app f a = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) :
    ∃ f₀ a₀, template = .app f₀ a₀ ∧
      f = f₀.subst ((Subst.ofList arguments).liftN depth) ∧
      a = a₀.subst ((Subst.ofList arguments).liftN depth) := by
  cases template <;> simp only [subst, reduceCtorEq, app.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · exact ⟨_, _, rfl, equal⟩

theorem capture_lam_inv
    (equal : VExpr.lam A body = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) :
    ∃ A₀ body₀, template = .lam A₀ body₀ ∧
      A = A₀.subst ((Subst.ofList arguments).liftN depth) ∧
      body = body₀.subst ((Subst.ofList arguments).liftN (depth + 1)) := by
  cases template <;> simp only [subst, reduceCtorEq, lam.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · exact ⟨_, _, rfl, equal⟩

theorem capture_pi_inv
    (equal : VExpr.forallE A body = template.subst ((Subst.ofList arguments).liftN depth))
    (notSelected : ¬CaptureSelected arguments depth template) :
    ∃ A₀ body₀, template = .forallE A₀ body₀ ∧
      A = A₀.subst ((Subst.ofList arguments).liftN depth) ∧
      body = body₀.subst ((Subst.ofList arguments).liftN (depth + 1)) := by
  cases template <;> simp only [subst, reduceCtorEq, forallE.injEq] at equal
  · have h := unselected_var arguments depth _ notSelected
    exact (VExpr.noConfusion (equal.trans h))
  · exact ⟨_, _, rfl, equal⟩

theorem capture_realization_cons (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

theorem capture_tail_cons (depth : Nat) (τ σ : Subst) (anchor : VExpr)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ) :
    Subst.lift_l (.skipN .refl (depth + 1)) (τ.cons anchor) = σ := by
  rw [← tail]
  funext index
  simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_comm]

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
