import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport

/-! # Single steps for context-indexed erased computation

A step acts at one occurrence. Simultaneous binder computation decomposes by
computing the body before the domain, so its body uses exactly the source binder.
No context-conversion or native-transport assumption is needed for decomposition.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- One primitive or beta contraction in one compatible occurrence. Binder
body steps use the unchanged annotation; annotation steps leave the body fixed. -/
inductive ScopedStep (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | primitive : Step Δ e e' → ScopedStep Step Δ e e'
  | beta : ScopedStep Step Δ (.app (.lam A b) x) (b.inst x)
  | appL : ScopedStep Step Δ f f' → ScopedStep Step Δ (.app f x) (.app f' x)
  | appR : ScopedStep Step Δ x x' → ScopedStep Step Δ (.app f x) (.app f x')
  | proj : ScopedStep Step Δ m m' → ScopedStep Step Δ (.proj c i m) (.proj c i m')
  | lamDomain : ScopedStep Step Δ A A' → ScopedStep Step Δ (.lam A b) (.lam A' b)
  | lamBody : ScopedStep Step (A :: Δ) b b' → ScopedStep Step Δ (.lam A b) (.lam A b')
  | piDomain : ScopedStep Step Δ A A' → ScopedStep Step Δ (.forallE A B) (.forallE A' B)
  | piBody : ScopedStep Step (A :: Δ) B B' → ScopedStep Step Δ (.forallE A B) (.forallE A B')

/-- A single occurrence step is a compatible computation. -/
theorem ScopedStep.compute (R : ScopedStep Step Δ e e') : ScopedCompute Step Δ e e' := by
  induction R with
  | primitive R => exact .base R
  | beta => exact .beta .beta
  | appL _ ih => exact .app ih .refl
  | appR _ ih => exact .app .refl ih
  | proj _ ih => exact .proj ih
  | lamDomain _ ih => exact .lam ih .refl
  | lamBody _ ih => exact .lam .refl ih
  | piDomain _ ih => exact .forallE ih .refl
  | piBody _ ih => exact .forallE .refl ih

/-- Finite single-step paths retain the same ambient context. -/
abbrev ScopedSteps (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) := ReflTransGen (ScopedStep Step Δ)

/-- Mapping a one-occurrence context through a finite path. -/
theorem ScopedSteps.map (H : ScopedSteps Step Δ a b)
    (F : ProofShape → ProofShape)
    (hF : ∀ {a b}, ScopedStep Step Δ a b → ScopedStep Target Θ (F a) (F b)) :
    ScopedSteps Target Θ (F a) (F b) := by
  induction H with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail (hF R)

/-- Every finite single-step path composes to compatible computation. -/
theorem ScopedSteps.compute (H : ScopedSteps Step Δ a b) : ScopedCompute Step Δ a b := by
  induction H with
  | rfl => exact .refl
  | tail _ R ih => exact ih.trans R.compute

/-- Compatible computation is exactly a finite sequence of one-occurrence
steps. At binders, bodies compute first so changing the annotation never asks
for an unproved forward context transport. -/
theorem ScopedCompute.steps (H : ScopedCompute Step Δ a b) : ScopedSteps Step Δ a b := by
  induction H using ScopedCompute.rootBeta_induction with
  | refl => exact .rfl
  | base R => exact .tail .rfl (.primitive R)
  | beta => exact .tail .rfl .beta
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @app Δ f f' x x' _ _ ihf ihx =>
    exact (ScopedSteps.map ihf (fun f => .app f x) (fun R => .appL R)).trans
      (ScopedSteps.map ihx (fun x => .app f' x) (fun R => .appR R))
  | proj _ ih => exact ScopedSteps.map ih _ (fun R => .proj R)
  | @lam Δ A A' b b' _ _ ihA ihb =>
    exact (ScopedSteps.map ihb (fun b => .lam A b) (fun R => .lamBody R)).trans
      (ScopedSteps.map ihA (fun A => .lam A b') (fun R => .lamDomain R))
  | @forallE Δ A A' B B' _ _ ihA ihB =>
    exact (ScopedSteps.map ihB (fun B => .forallE A B) (fun R => .piBody R)).trans
      (ScopedSteps.map ihA (fun A => .forallE A B') (fun R => .piDomain R))

/-- The single-step presentation neither enlarges nor restricts computation. -/
theorem scopedCompute_iff_steps : ScopedCompute Step Δ a b ↔ ScopedSteps Step Δ a b :=
  ⟨ScopedCompute.steps, ScopedSteps.compute⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
