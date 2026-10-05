import Lean4Lean.Theory.Typing.NativeCaptureAbstraction
import Lean4Lean.Theory.Typing.AnchoredNativeSyntax

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- Source contexts are in reverse declaration order. -/
def nativePrefixPlan (offset : Nat) : (domains : List VExpr) → CapturePlan domains
  | [] => .nil
  | _ :: rest => (nativePrefixPlan (offset + 1) rest).index offset

@[simp] theorem nativePrefixPlan_count (offset : Nat) (domains : List VExpr) :
    (nativePrefixPlan offset domains).count = 0 := by
  induction domains generalizing offset with
  | nil => rfl
  | cons _ _ ih => exact ih _

@[simp] theorem nativePrefixPlan_added (offset : Nat) (domains : List VExpr) (arguments : Subst) :
    (nativePrefixPlan offset domains).added arguments = [] := by
  induction domains generalizing offset with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem captures_at (offset : Nat) (domains : List VExpr) (arguments : Subst) (i : Nat) :
    (nativePrefixPlan offset domains).captures arguments i =
      if i < domains.length then arguments (i + offset) else .bvar (i - domains.length) := by
  induction domains generalizing offset i with
  | nil => simp [nativePrefixPlan, CapturePlan.captures, Subst.id]
  | cons A rest ih =>
    cases i with
    | zero => simp [nativePrefixPlan, CapturePlan.captures, Subst.cons, liftN_zero]
    | succ i =>
      simp only [nativePrefixPlan, CapturePlan.captures, Subst.cons, ih, List.length_cons,
        Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The equality includes the unused tail: the finite tuple has the same
ordinary shifted-identity tail as the deterministic capture plan. -/
theorem nativePrefixPlan_captures (offset : Nat) (domains : List VExpr) (values : List VExpr)
    (length : values.length = offset + domains.length) :
    (nativePrefixPlan offset domains).captures (nativeCaptureSubst values) =
      Subst.lift_l (.skipN .refl offset) (nativeCaptureSubst values) := by
  funext i
  rw [captures_at]
  simp only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar]
  change (if i < domains.length then nativeCaptureSubst values (i + offset)
    else .bvar (i - domains.length)) = nativeCaptureSubst values (i + offset)
  split
  · rfl
  · rw [nativeCaptureSubst, dif_neg (by omega)]
    congr 1 <;> omega

theorem nativeCaptureSubst_prefix (values : List VExpr) (count : Nat)
    (bound : count ≤ values.length) :
    Subst.lift_l (.skipN .refl (values.length - count)) (nativeCaptureSubst values) =
      nativeCaptureSubst (values.take count) := by
  funext i
  simp only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar]
  have len : (values.take count).length = count := by simp [Nat.min_eq_left bound]
  by_cases hi : i < count
  · rw [nativeCaptureSubst, dif_pos (by omega), nativeCaptureSubst, dif_pos (by omega)]
    simp only [len]
    rw [List.getElem_take]
    congr 1 <;> omega
  · rw [nativeCaptureSubst, dif_neg (by omega), nativeCaptureSubst, dif_neg (by omega)]
    simp only [len]
    congr 1 <;> omega

@[simp] theorem nativeCaptureSubst_append (values : List VExpr) (value : VExpr) :
    nativeCaptureSubst (values ++ [value]) = (nativeCaptureSubst values).cons value := by
  funext i
  cases i with
  | zero => simp [nativeCaptureSubst, Subst.cons]
  | succ i =>
    simp only [nativeCaptureSubst, List.length_append, List.length_singleton, Subst.cons]
    by_cases hi : i < values.length
    · rw [dif_pos (by omega), dif_pos hi, List.getElem_append_left (by omega)]
      congr 1 <;> omega
    · rw [dif_neg (by omega), dif_neg hi]
      congr 1 <;> omega


end Lean4Lean.AnchoredSource.Adapted
