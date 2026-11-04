import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPiRoot

/-! # Constant computation preserving universe equivalence

A rigid constant may still take explicit universe steps. Exposure needs its
family and pointwise universe equivalence preserved, rather than literal
primitive inertness. This property is stable under finite scoped computation.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- Root steps from this constant only vary its universe arguments. -/
def ConstantRootLevels (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (family : Lean.Name) : Prop :=
  ∀ {Δ ls out}, Step Δ (.const family ls) out →
    ∃ ls', out = .const family ls' ∧ List.Forall₂ (· ≈ ·) ls ls'

private theorem beta_constant (R : BetaRed a b) (E : a = .const family ls) :
    b = .const family ls := by
  induction R with
  | refl => exact E
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ E)
  | app | proj | lam | forallE | beta => cases E

/-- A computation from a constant preserves the family and equivalent levels
when every primitive root does. No termination or global confluence is used. -/
theorem ScopedCompute.const_levels_inv
    (hn : ConstantRootLevels Step family)
    (R : ScopedCompute Step Δ (.const family ls) out) :
    ∃ ls', out = .const family ls' ∧ List.Forall₂ (· ≈ ·) ls ls' := by
  generalize E : ProofShape.const family ls = source at R
  induction R generalizing ls with
  | base H => exact hn (E ▸ H)
  | beta H => exact ⟨ls, beta_constant H E.symm, .rfl (fun _ _ => by rfl)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ls₁, rfl, HL⟩ := ih₁ E
    obtain ⟨ls₂, HE, HL'⟩ := ih₂ rfl
    exact ⟨ls₂, HE, HL.trans (fun _ _ _ H K => H.trans K) HL'⟩
  | app | proj | lam | forallE => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
