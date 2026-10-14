import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbe

/-! # Inverting finite erased computation under lambda binders -/
namespace Lean4Lean.VEnv.Strengthening.ProofShape

/-- Beta preserves a lambda head and reduces its annotation and body separately. -/
theorem BetaRed.lam_inv (R : BetaRed (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ BetaRed A A' ∧ BetaRed b b' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | refl => exact ⟨_, _, E.symm, .refl, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨A₁, b₁, rfl, HA, HB⟩ := ih1 E
    obtain ⟨A₂, b₂, HE, RA, RB⟩ := ih2 rfl
    exact ⟨_, _, HE, HA.trans RA, HB.trans RB⟩
  | lam RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | forallE | beta => cases E

/-- If primitive roots exclude lambdas, every finite computation preserves the
lambda and supplies independent finite annotation and body paths. -/
theorem Compute.lam_inv (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : Compute Step (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ Compute Step A A' ∧ Compute Step b b' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨A', b', HE, HA, HB⟩ := H.lam_inv
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨A₁, b₁, rfl, HA, HB⟩ := ih1 E
    obtain ⟨A₂, b₂, HE, RA, RB⟩ := ih2 rfl
    exact ⟨_, _, HE, HA.trans RA, HB.trans RB⟩
  | lam RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | forallE => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
