import Lean4Lean.Theory.Typing.Strengthening.ProofShapeSubstitution

/-! # Raw retraction algebra for annotated proof shapes

This syntax-only algebra is independent of the recursive comparison relation,
so new comparison rules can establish substitution and thinning stability.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

namespace ProofShape
/-- General variable thinning on annotated proof shapes. -/
def lift' : ProofShape → Lift → ProofShape
  | .proof, _ => .proof
  | .bvar i, ρ => .bvar (ρ.liftVar i)
  | .sort u, _ => .sort u
  | .const c ls, _ => .const c ls
  | .app f a, ρ => .app (f.lift' ρ) (a.lift' ρ)
  | .proj s i m, ρ => .proj s i (m.lift' ρ)
  | .lam A b, ρ => .lam (A.lift' ρ) (b.lift' ρ.cons)
  | .forallE A B, ρ => .forallE (A.lift' ρ) (B.lift' ρ.cons)

/-- Composition of arbitrary thinnings agrees with sequential renaming. -/
theorem lift'_comp (e : ProofShape) :
    e.lift' (ρ.comp τ) = (e.lift' ρ).lift' τ := by
  induction e generalizing ρ τ with
  | proof | sort | const => rfl
  | bvar => exact congrArg ProofShape.bvar (Lift.liftVar_comp ..)
  | app _ _ ihf iha => simp only [lift', ihf, iha]
  | proj _ _ _ ih => simp only [lift', ih]
  | lam _ _ ihA ihb =>
    simp only [lift']
    exact congr (congrArg ProofShape.lam ihA) (ihb (ρ := ρ.cons) (τ := τ.cons))
  | forallE _ _ ihA ihb =>
    simp only [lift']
    exact congr (congrArg ProofShape.forallE ihA) (ihb (ρ := ρ.cons) (τ := τ.cons))

/-- A thinning with no inserted variables fixes every proof shape. -/
theorem lift'_depth_zero (e : ProofShape) (H : ρ.depth = 0) : e.lift' ρ = e := by
  induction e generalizing ρ <;> simp_all [lift', Lift.depth, Lift.liftVar_depth_zero]

/-- General thinning is a raw substitution by renamed variables. -/
theorem lift'_eq_subst (e : ProofShape) (ρ : Lift) :
    e.lift' ρ = e.subst (fun i => .bvar (ρ.liftVar i)) := by
  induction e generalizing ρ with
  | proof | bvar | sort | const => rfl
  | app f a ihf iha => simp only [lift', subst, ihf, iha]
  | proj s i m ih => simp only [lift', subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HH : (fun i => bvar (ρ.cons.liftVar i)) =
        Subst.lift (fun i => bvar (ρ.liftVar i)) := by
      funext i
      cases i <;> simp [Lift.liftVar, Subst.lift, ProofShape.liftN, _root_.Lean4Lean.liftVar] <;> omega
    simp only [lift', subst, ihA, ihb, HH]

/-- A raw left inverse uses a proof marker at skipped variables. No typing is
claimed for these images, which never occur in a thinned source endpoint. -/
def Subst.retract : Lift → Subst
  | .refl => .id
  | .skip ρ => (retract ρ).cons .proof
  | .cons ρ => (retract ρ).lift

/-- Retained variables are recovered exactly by the raw inverse. -/
theorem Subst.retract_liftVar (ρ : Lift) (i : Nat) :
    Subst.retract ρ (ρ.liftVar i) = .bvar i := by
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simpa only [retract, Lift.liftVar, cons] using ih i
  | cons ρ ih =>
    cases i <;> simp [retract, Lift.liftVar, Subst.lift, ih, ProofShape.liftN, _root_.Lean4Lean.liftVar] <;> omega

/-- Substitution absorbs general thinning whenever it agrees on retained variables. -/
theorem subst_lift'_agree (e : ProofShape) {σ τ : Subst}
    (H : ∀ i, τ (ρ.liftVar i) = σ i) :
    (e.lift' ρ).subst τ = e.subst σ := by
  induction e generalizing ρ σ τ with
  | proof | sort | const => rfl
  | bvar i => exact H i
  | app f a ihf iha => simp only [lift', subst, ihf H, iha H]
  | proj s i m ih => simp only [lift', subst, ih H]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, τ.lift (ρ.cons.liftVar i) = σ.lift i := by
      intro i
      cases i <;> simp only [Lift.liftVar, Subst.lift, H]
    simp only [lift', subst, ihA H, ihb HB]

/-- Retraction removes all inserted variables from every original proof shape. -/
theorem subst_retract_lift' (e : ProofShape) (ρ : Lift) :
    (e.lift' ρ).subst (Subst.retract ρ) = e := by
  rw [subst_lift'_agree e (Subst.retract_liftVar ρ)]
  exact ProofShape.subst_id e

/-- Any relation stable under raw substitution reflects through thinning. -/
theorem relation_lift'_reflect {R : ProofShape → ProofShape → Prop} {a b : ProofShape} {ρ : Lift}
    (hsubst : ∀ {a b} (σ : Subst), R a b → R (a.subst σ) (b.subst σ))
    (H : R (a.lift' ρ) (b.lift' ρ)) : R a b := by
  simpa only [subst_retract_lift'] using hsubst (Subst.retract ρ) H
/-- Substitution-stable relations are invariant under arbitrary thinning. -/
theorem relation_lift'_iff {R : ProofShape → ProofShape → Prop} {a b : ProofShape} {ρ : Lift}
    (hsubst : ∀ {a b} (σ : Subst), R a b → R (a.subst σ) (b.subst σ)) :
    R (a.lift' ρ) (b.lift' ρ) ↔ R a b := by
  refine ⟨relation_lift'_reflect hsubst, fun H => ?_⟩
  simpa only [lift'_eq_subst] using hsubst (fun i => .bvar (ρ.liftVar i)) H
/-- Single-block insertion is the corresponding general thinning. -/
theorem lift'_consN_skipN (e : ProofShape) :
    e.lift' (.consN (.skipN .refl n) k) = e.liftN n k := by
  induction e generalizing k with
  | proof | sort | const => rfl
  | bvar => exact congrArg ProofShape.bvar (Lift.liftVar_consN_skipN ..)
  | app _ _ ihf iha => simp only [lift', ProofShape.liftN, ihf, iha]
  | proj _ _ _ ih => simp only [lift', ProofShape.liftN, ih]
  | lam A b ihA ihb =>
    exact congr (congrArg ProofShape.lam ihA) (ihb (k := k+1))
  | forallE A b ihA ihb =>
    exact congr (congrArg ProofShape.forallE ihA) (ihb (k := k+1))

/-- General thinning is injective, witnessed by its raw substitution retraction. -/
theorem lift'_inj {a b : ProofShape} (H : a.lift' ρ = b.lift' ρ) : a = b := by
  simpa only [subst_retract_lift'] using congrArg (·.subst (Subst.retract ρ)) H

/-- Thinning commutes with shifting under one retained binder. -/
theorem lift'_liftN_one (e : ProofShape) :
    (e.lift' ρ).liftN 1 = (e.liftN 1).lift' ρ.cons := by
  rw [← lift'_consN_skipN (n := 1) (k := 0),
    ← lift'_consN_skipN (e := e) (n := 1) (k := 0)]
  simp only [Lift.consN, Lift.skipN_one, ← lift'_comp, Lift.comp, Lift.refl_comp]

/-- Renaming commutes with beta instantiation, including proof-marker images. -/
theorem lift'_inst (B a : ProofShape) :
    (B.inst a).lift' ρ = (B.lift' ρ.cons).inst (a.lift' ρ) := by
  have Hσ : (fun i => bvar (ρ.cons.liftVar i)) =
      Subst.lift (fun i => bvar (ρ.liftVar i)) := by
    funext i
    cases i <;> simp [Lift.liftVar, Subst.lift, ProofShape.liftN, _root_.Lean4Lean.liftVar] <;> omega
  simp only [lift'_eq_subst, subst_inst, Hσ]

/-- Invert an application after arbitrary thinning. -/
theorem lift'_app_inv {e : ProofShape} (H : e.lift' ρ = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f₀.lift' ρ = f ∧ a₀.lift' ρ = a := by
  cases e <;> simp_all [lift']
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

/-- Invert a projection after arbitrary thinning. -/
theorem lift'_proj_inv {e : ProofShape} (H : e.lift' ρ = .proj s i m) :
    ∃ m₀, e = .proj s i m₀ ∧ m₀.lift' ρ = m := by
  cases e <;> simp_all [lift']

/-- Invert a lambda after arbitrary thinning. -/
theorem lift'_lam_inv {e : ProofShape} (H : e.lift' ρ = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A₀.lift' ρ = A ∧ b₀.lift' ρ.cons = b := by
  cases e <;> simp_all [lift']
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

/-- Invert a Pi after arbitrary thinning. -/
theorem lift'_forallE_inv {e : ProofShape} (H : e.lift' ρ = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A₀.lift' ρ = A ∧ B₀.lift' ρ.cons = B := by
  cases e <;> simp_all [lift']
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

/-- Thinning cannot create a sort head. -/
theorem lift'_sort_inv {e : ProofShape} (H : e.lift' ρ = .sort u) : e = .sort u := by
  cases e <;> simp_all [lift']

/-- Thinning cannot create a constant head. -/
theorem lift'_const_inv {e : ProofShape} (H : e.lift' ρ = .const c ls) : e = .const c ls := by
  cases e <;> simp_all [lift']

/-- Raw substitution stability also reflects a single inserted block. -/
theorem relation_liftN_reflect {R : ProofShape → ProofShape → Prop} {a b : ProofShape}
    (hsubst : ∀ {a b} (σ : Subst), R a b → R (a.subst σ) (b.subst σ))
    (H : R (a.liftN n k) (b.liftN n k)) : R a b :=
  relation_lift'_reflect (ρ := .consN (.skipN .refl n) k) hsubst (by simpa only [lift'_consN_skipN] using H)
end ProofShape

end Lean4Lean.VEnv.Strengthening
