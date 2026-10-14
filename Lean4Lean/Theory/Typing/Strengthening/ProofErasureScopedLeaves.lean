import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSubstitution

/-! # Atomic leaves of scoped comparison

Compatible and computational cases remain visible to induction on the enclosing
scoped certificate. Structure heads are represented by recursive field guards.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean Params

/-- Atomic reflexivity, universe comparison, and displayed function eta. -/
inductive ScopedLeaf : Bool → ProofShape → ProofShape → Prop where
  | refl : ScopedLeaf mode a a
  | sort : u ≈ v → ScopedLeaf mode (.sort u) (.sort v)
  | const : List.Forall₂ (· ≈ ·) ls ls' → ScopedLeaf mode (.const c ls) (.const c ls')
  | etaL : EtaHead a b → ScopedLeaf true a b
  | etaR : EtaHead b a → ScopedLeaf true a b

/-- Atomic leaves have the earlier primitive-free contextual interpretation. -/
theorem ScopedLeaf.context [Params] (H : ScopedLeaf mode a b) :
    ContextCompare (fun _ _ => False) Δ mode a b := by
  cases H with
  | refl => exact .refl
  | sort H => exact .base (.base (.sort H))
  | const H => exact .base (.base (.const H))
  | etaL H => exact .base (.base (.etaL H))
  | etaR H => exact .base (.base (.etaR H))

/-- Atomic leaves substitute without any context or typing premise. -/
theorem ScopedLeaf.subst (H : ScopedLeaf mode a b) : ScopedLeaf mode (a.subst τ) (b.subst τ) := by
  cases H with
  | refl => exact .refl
  | sort H => exact .sort H
  | const H => exact .const H
  | etaL H => exact .etaL H.subst
  | etaR H => exact .etaR H.subst

/-- An inferred leaf also checks at a common endpoint type. -/
theorem ScopedLeaf.common (H : ScopedLeaf mode a b) : ScopedLeaf true a b := by
  cases H with
  | refl => exact .refl
  | sort H => exact .sort H
  | const H => exact .const H
  | etaL H => exact .etaL H
  | etaR H => exact .etaR H

end Lean4Lean.VEnv.Strengthening.ProofShape
