import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure

/-! # Pi computation with the precise root exclusion

Domain exposure only excludes primitive steps at Pi roots. Sort conversion is
compatible with this property, although it violates the older PrimitiveHead
interface. The domain computation remains in the original ambient context.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-- Pi computation retains its domain path whenever no primitive starts at a
Pi. This permits primitive sort conversion and does not constrain codomains. -/
theorem ScopedCompute.forallE_domain_inv_of_no_root
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (R : ScopedCompute Step Δ (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ ScopedCompute Step Δ A A' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (hn (E ▸ H)).elim
  | beta H =>
    obtain ⟨A', B', HE, HA, _⟩ := beta_forallE_parts (E ▸ H)
    exact ⟨A', B', HE, .beta HA⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA'⟩ := ih₂ rfl
    exact ⟨A₂, B₂, HE, HA.trans HA'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA⟩
  | app | proj | lam => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
