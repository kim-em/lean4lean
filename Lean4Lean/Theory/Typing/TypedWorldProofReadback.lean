import Lean4Lean.Theory.Inductive.SaturatedNativeSubstitution

/-! Canonical readback copies the complement of a fixed variable insertion
in its ORIGINAL slot order. It does not assert that sequential copying of
two insertion histories preserves that order. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

abbrev proofCount := Lift.depth

def proofReadback : Lift → Subst → Subst
  | .refl, σ => σ
  | .skip ρ, σ => (proofReadback ρ σ).lift
  | .cons ρ, σ => (proofReadback ρ σ.tail).cons (σ.head.liftN (proofCount ρ))

def replayContext (base : List VExpr) : List VExpr → Lift → Subst → List VExpr
  | _, .refl, _ => base
  | P :: context, .skip ρ, σ =>
    P.subst (proofReadback ρ σ) :: replayContext base context ρ σ
  | _ :: context, .cons ρ, σ => replayContext base context ρ σ.tail
  | [], _, _ => base

/-- The known generated prefix is retained in the complete canonical copy.
Only the older base is read back by the caller's chosen substitution. -/
def proofFrontMap : Nat → Lift → Lift
  | 0, ρ => .skipN .refl (proofCount ρ)
  | _ + 1, .refl => .refl
  | n + 1, .skip ρ => (proofFrontMap (n + 1) ρ).skip
  | n + 1, .cons ρ => (proofFrontMap n ρ).cons

theorem proofReadback_lift_l (ρ : Lift) (σ : Subst) :
    Subst.lift_l ρ (proofReadback ρ σ) =
      σ.lift_r (.skipN .refl (proofCount ρ)) := by
  induction ρ generalizing σ with
  | refl => funext i; simp only [proofReadback, proofCount, Lift.depth,
      Lift.skipN, Subst.lift_r, lift'_refl, Subst.lift_l, Lift.liftVar]
  | skip ρ ih =>
    funext i
    have h := congrFun (ih σ) i
    change (proofReadback ρ σ (ρ.liftVar i)).lift =
      (σ i).lift' (.skipN .refl (proofCount ρ + 1))
    rw [show proofReadback ρ σ (ρ.liftVar i) =
      (σ i).lift' (.skipN .refl (proofCount ρ)) from h]
    rw [lift_eq_lift', ← lift'_comp]
    rfl
  | cons ρ ih =>
    funext i
    cases i with
    | zero => exact lift'_consN_skipN (e := σ.head) (k := 0) |>.symm
    | succ i =>
      exact congrFun (ih σ.tail) i

/-- Chosen base readback and canonical complement copies commute on every
raw expression, including terms outside the finite declaration telescope. -/
theorem proofReadback_commute (ρ : Lift) (σ : Subst) (e : VExpr) :
    (e.lift' ρ).subst (proofReadback ρ σ) =
      (e.subst σ).lift' (.skipN .refl (proofCount ρ)) := by
  rw [subst_lift', proofReadback_lift_l, ← lift'_subst]

@[simp] theorem proofReadback_skipN (n : Nat) (σ : Subst) :
    proofReadback (.skipN .refl n) σ = σ.liftN n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Lift.skipN, proofReadback, ih, Subst.liftN]

theorem replayContext_front (Γ Δ added : List VExpr) (σ : Subst) :
    replayContext Γ (added ++ Δ) (.skipN .refl added.length) σ =
      InductiveSignature.NativeRecursorData.substAdded σ added ++ Γ := by
  induction added with
  | nil => simp [replayContext, InductiveSignature.NativeRecursorData.substAdded]
  | cons domain rest ih =>
    simp only [List.cons_append, List.length_cons, Lift.skipN, replayContext,
      proofReadback_skipN, InductiveSignature.NativeRecursorData.substAdded, ih]

private theorem lift'_skip (e : VExpr) (ρ : Lift) :
    e.lift' ρ.skip = (e.lift' ρ).lift := by
  rw [lift_eq_lift', ← lift'_comp]
  rfl

/-- Factor the already generated front through the total canonical
readback. Unlike sequential complement copying, this preserves slot order. -/
theorem proofReadback_front (n : Nat) (ρ : Lift) (σ : Subst) (e : VExpr) :
    (e.lift' ρ).subst (proofReadback ((Lift.skipN .refl n).comp ρ) σ) =
      (e.subst (σ.liftN n)).lift' (proofFrontMap n ρ) := by
  induction ρ generalizing n σ e with
  | refl => simp only [Lift.comp, lift'_refl, proofReadback_skipN]
            cases n <;> simp only [proofFrontMap, proofCount, Lift.depth, Lift.skipN, lift'_refl]
  | skip ρ ih =>
    cases n with
    | zero => simpa only [Lift.skipN, Lift.refl_comp, Subst.liftN, proofFrontMap] using
        proofReadback_commute ρ.skip σ e
    | succ n =>
      simp only [Lift.comp, proofReadback, proofFrontMap, lift'_skip, lift_subst_lift]
      rw [ih]
  | cons ρ ih =>
    cases n with
    | zero => simpa only [Lift.skipN, Lift.refl_comp, Subst.liftN, proofFrontMap] using
        proofReadback_commute ρ.cons σ e
    | succ n =>
      rw [subst_lift', lift'_subst]
      apply congrArg (e.subst ·)
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        have h := ih n σ (.bvar i)
        change ((proofReadback ((Lift.skipN .refl n).comp ρ) σ) (ρ.liftVar i)).lift =
          ((σ.liftN n) i).lift.lift' (proofFrontMap n ρ).cons
        rw [show (proofReadback ((Lift.skipN .refl n).comp ρ) σ) (ρ.liftVar i) =
          ((σ.liftN n) i).lift' (proofFrontMap n ρ) from h]
        simp only [lift_eq_lift', ← lift'_comp, Lift.comp, Lift.refl_comp]

/-- The retained generated prefix and the factored post-map agree on all
original base slots with the one total canonical complement copy. -/
theorem proofFrontMap_base (n : Nat) (ρ : Lift) :
    (Lift.skipN .refl n).comp (proofFrontMap n ρ) =
      .skipN .refl (n + proofCount ρ) := by
  induction ρ generalizing n with
  | refl => cases n <;> simp [proofFrontMap]
  | skip ρ ih =>
    cases n with
    | zero => simp [proofFrontMap]
    | succ n => simpa only [proofFrontMap, Lift.comp, ih, proofCount,
        Lift.depth, Nat.add_succ, Lift.skipN] using congrArg Lift.skip (ih (n + 1))
  | cons ρ ih =>
    cases n with
    | zero => simp [proofFrontMap]
    | succ n => simpa only [proofFrontMap, Lift.skipN, Lift.comp, proofCount,
        Lift.depth, Nat.succ_add] using congrArg Lift.skip (ih n)

theorem proofReadback_front_lift_l (n : Nat) (ρ : Lift) (σ : Subst) :
    Subst.lift_l ρ (proofReadback ((Lift.skipN .refl n).comp ρ) σ) =
      (σ.liftN n).lift_r (proofFrontMap n ρ) := by
  funext i
  exact proofReadback_front n ρ σ (.bvar i)

end Lean4Lean.VEnv
