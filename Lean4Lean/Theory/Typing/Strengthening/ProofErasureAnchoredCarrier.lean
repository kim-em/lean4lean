import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution

/-! # Carrier heads outside the binders being instantiated

Only the head is protected. Its arguments may mention local variables, contain
redexes, or diverge. This gives an inert-carrier invariant for beta exposure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
namespace ProofShape

/-- The carrier is headed by a variable outside the first `cut` binders. -/
def AnchoredCarrier (cut : Nat) (A : ProofShape) : Prop :=
  ∃ i args, cut ≤ i ∧ A = mkApps (.bvar i) args

/-- A substitution keeps the protected suffix variable-headed. -/
def PreservesCarrierHeads (cut cut' : Nat) (τ : Subst) : Prop :=
  ∀ i, cut ≤ i → ∃ j, cut' ≤ j ∧ τ i = .bvar j

/-- Lifting under a binder shifts the protected suffix on both sides. -/
theorem PreservesCarrierHeads.lift (H : PreservesCarrierHeads cut cut' τ) :
    PreservesCarrierHeads (cut + 1) (cut' + 1) τ.lift := by
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    obtain ⟨j, hj, E⟩ := H i (by omega)
    refine ⟨j + 1, by omega, ?_⟩
    simp [Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm]

/-- Removing the innermost binder preserves every head beyond that binder,
even when the substituted argument is a function or a structure type. -/
theorem PreservesCarrierHeads.one (a : ProofShape) :
    PreservesCarrierHeads (cut + 1) cut (Subst.one a) := by
  intro i hi
  cases i with
  | zero => omega
  | succ i => exact ⟨i, by omega, rfl⟩

/-- Protected carrier heads survive simultaneous substitution. -/
theorem AnchoredCarrier.subst (H : AnchoredCarrier cut A)
    (W : PreservesCarrierHeads cut cut' τ) : AnchoredCarrier cut' (A.subst τ) := by
  obtain ⟨i, args, hi, rfl⟩ := H
  obtain ⟨j, hj, E⟩ := W i hi
  refine ⟨j, args.map (·.subst τ), hj, ?_⟩
  simp only [subst_mkApps, ProofShape.subst, E]

/-- Ordinary computation preserves the protected head and its index. -/
theorem AnchoredCarrier.compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : AnchoredCarrier cut A) (R : ScopedCompute Step Δ A B) :
    AnchoredCarrier cut B := by
  obtain ⟨i, args, hi, rfl⟩ := H
  obtain ⟨args', E, _⟩ := R.bvar_spine hhead
  exact ⟨i, args', hi, E⟩

variable [Params]
open private variableHead variableHead_mkApps
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure

/-- Protected neutral heads never become structural carrier shapes. -/
theorem AnchoredCarrier.not_exposed (H : AnchoredCarrier cut A) : ¬ CarrierExposure A := by
  obtain ⟨i, args, _, E⟩ := H
  intro HX
  cases HX with
  | record | function =>
    have HE := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at HE
    cases HE

/-- The protected-head invariant discharges the inert branch of recursive
transport without exact recovery or domain-alignment assumptions. -/
theorem AnchoredCarrier.inert
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : AnchoredCarrier cut A) :
    ∀ {B}, ScopedCompute Step Δ A B → ¬ CarrierExposure B :=
  fun R => (H.compute hhead R).not_exposed

end ProofShape
end Lean4Lean.VEnv.Strengthening
