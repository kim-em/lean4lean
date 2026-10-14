import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWeakening

/-! # Raw substitution algebra for annotated proof shapes

These laws do not assign a type to the proof marker. They supply substitution
stability of erased computation; typed erasure commutation is a separate theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- A substitution can absorb an insertion by agreeing on the shifted indices. -/
theorem subst_liftN_agree (e : ProofShape) {σ τ : Subst}
    (H : ∀ i, τ (liftVar n i k) = σ i) :
    (e.liftN n k).subst τ = e.subst σ := by
  induction e generalizing σ τ k with
  | proof | sort | const => rfl
  | bvar i => exact H i
  | app f a ihf iha => simp only [liftN, subst, ihf H, iha H]
  | proj s i m ih => simp only [liftN, subst, ih H]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, τ.lift (liftVar n i (k+1)) = σ.lift i := by
      intro i
      cases i with
      | zero => simp [liftVar, Subst.lift]
      | succ i =>
        have hi : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
          simp [liftVar]; split <;> omega
        rw [hi]
        simp only [Subst.lift, H]
    simp only [liftN, subst, ihA H, ihb HB]

/-- Insertion after substitution shifts each image of that substitution. -/
theorem liftN_subst (e : ProofShape) (σ : Subst) :
    (e.subst σ).liftN n k = e.subst (fun i => (σ i).liftN n k) := by
  induction e generalizing σ k with
  | proof | bvar | sort | const => rfl
  | app f a ihf iha => simp only [subst, liftN, ihf, iha]
  | proj s i m ih => simp only [subst, liftN, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HH : (fun i => (σ.lift i).liftN n (k+1)) = Subst.lift (fun i => (σ i).liftN n k) := by
      funext i
      cases i with
      | zero => simp [Subst.lift, liftN, liftVar]
      | succ i =>
        simp only [Subst.lift]
        exact (liftN_comm (σ i) n 1 k 0 (Nat.zero_le _)).symm
    simp only [subst, liftN, ihA, ihb, HH]

/-- Lifting both a term and its substitution preserves the substitution result. -/
theorem lift_subst_lift (e : ProofShape) (σ : Subst) :
    (e.liftN 1).subst σ.lift = (e.subst σ).liftN 1 := by
  rw [liftN_subst]
  apply subst_liftN_agree
  intro i
  simp [liftVar, Subst.lift, Nat.add_comm]

/-- Compose simultaneous substitutions. -/
def Subst.comp (σ τ : Subst) : Subst := fun i => (σ i).subst τ

/-- Composition commutes with entering a binder. -/
theorem Subst.comp_lift (σ τ : Subst) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact (lift_subst_lift (σ i) τ).symm

/-- Consecutive erased substitutions compose pointwise. -/
theorem subst_subst (e : ProofShape) (σ τ : Subst) :
    (e.subst σ).subst τ = e.subst (σ.comp τ) := by
  induction e generalizing σ τ <;> simp only [subst, *, Subst.comp_lift]
  rfl

/-- Identity substitution. -/
def Subst.id : Subst := .bvar

/-- The identity map remains the identity under a binder. -/
theorem Subst.id_lift : Subst.id.lift = Subst.id := by
  funext i
  cases i <;> simp [Subst.id, Subst.lift, liftN, liftVar, Nat.add_comm]

/-- Identity substitution leaves every proof shape unchanged. -/
theorem subst_id (e : ProofShape) : e.subst Subst.id = e := by
  induction e <;> simp only [subst, Subst.id_lift, *]
  rfl

/-- Extend a substitution with the image of the newest variable. -/
def Subst.cons (σ : Subst) (a : ProofShape) : Subst
  | 0 => a
  | i+1 => σ i

/-- A single beta argument followed by unchanged older variables. -/
def Subst.one (a : ProofShape) : Subst := Subst.id.cons a

/-- Enter several binders before applying a substitution. -/
def Subst.liftN (σ : Subst) : Nat → Subst
  | 0 => σ
  | k+1 => (σ.liftN k).lift

/-- Zero-variable insertion does not change a shape. -/
theorem liftN_zero (e : ProofShape) : e.liftN 0 k = e := by
  induction e generalizing k <;> simp [liftN, liftVar, *]

/-- Consecutive insertions at the outer boundary add their sizes. -/
theorem liftN_add (e : ProofShape) : (e.liftN n k).liftN m k = e.liftN (n+m) k := by
  induction e generalizing k <;> simp only [liftN, *]
  simp only [liftVar]
  split <;> rename_i h
  · rfl
  · rw [if_neg (by omega)]
    congr 1
    omega

/-- Instantiation is a lifted one-variable simultaneous substitution. -/
theorem inst_eq_subst (e a : ProofShape) : e.inst a k = e.subst ((Subst.one a).liftN k) := by
  induction e generalizing k with
  | proof | sort | const => rfl
  | app f x ihf ihx => simp only [inst, subst, ihf, ihx]
  | proj s i m ih => simp only [inst, subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp only [inst, subst, ihA, ihb, Subst.liftN]
  | bvar i =>
    induction k generalizing i with
    | zero => cases i <;> simp [inst, subst, Subst.liftN, Subst.one, Subst.cons, Subst.id, liftN_zero]
    | succ k ih =>
      cases i with
      | zero => simp [inst, subst, Subst.liftN, Subst.lift]
      | succ i =>
        simp only [inst, Nat.succ_lt_succ_iff, Nat.succ.injEq, subst, Subst.liftN, Subst.lift]
        simp only [subst] at ih
        rw [← ih]
        simp only [inst]
        split <;> rename_i h
        · simp [liftN, liftVar, Nat.add_comm]
        · split <;> rename_i hh
          · exact (liftN_add a).symm
          · simp [liftN, liftVar]
            congr 1
            omega

/-- Substitution after lifting drops the newly supplied image. -/
theorem lift_subst_cons (e : ProofShape) (σ : Subst) (a : ProofShape) :
    (e.liftN 1).subst (σ.cons a) = e.subst σ := by
  apply subst_liftN_agree
  intro i
  simp [liftVar, Subst.cons, Nat.add_comm]

/-- Simultaneous substitution commutes with beta instantiation. -/
theorem subst_inst (e a : ProofShape) (σ : Subst) :
    (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  simp only [inst_eq_subst, Subst.liftN, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change σ i = ((σ i).liftN 1).subst (Subst.id.cons (a.subst σ))
    rw [lift_subst_cons, subst_id]

end Lean4Lean.VEnv.Strengthening.ProofShape
