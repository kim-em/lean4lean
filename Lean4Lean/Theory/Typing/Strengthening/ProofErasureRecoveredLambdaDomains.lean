import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredCompositionBarrier

/-! # Domain reflection for inferred comparison of retained lambdas

A recovered Pi of a literal lambda computes its displayed domain. Consequently
recovered eta cannot hide the domain comparison of two lambda endpoints in
inferred mode, even when their bodies are not constant probes.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

private theorem BetaRed.lam_shape (R : BetaRed (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ BetaRed A A' := by
  generalize E : ProofShape.lam A b = e at R
  induction R generalizing A b with
  | refl => exact ⟨_, _, E.symm, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, rfl, H1⟩ := ih1 E
    obtain ⟨_, _, E2, H2⟩ := ih2 rfl
    exact ⟨_, _, E2, H1.trans H2⟩
  | lam RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | app | proj | forallE | beta => cases E

private theorem BetaRed.forallE_shape (R : BetaRed (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ BetaRed A A' := by
  generalize E : ProofShape.forallE A B = e at R
  induction R generalizing A B with
  | refl => exact ⟨_, _, E.symm, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, rfl, H1⟩ := ih1 E
    obtain ⟨_, _, E2, H2⟩ := ih2 rfl
    exact ⟨_, _, E2, H1.trans H2⟩
  | forallE RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | app | proj | lam | beta => cases E

/-- Computation preserves a literal lambda head and computes its domain. -/
theorem Compute.lam_shape (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : Compute Step (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ Compute Step A A' := by
  generalize E : ProofShape.lam A b = e at R
  induction R generalizing A b with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨_, _, E, R⟩ := H.lam_shape
    exact ⟨_, _, E, .beta R⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, rfl, H1⟩ := ih1 E
    obtain ⟨_, _, E2, H2⟩ := ih2 rfl
    exact ⟨_, _, E2, H1.trans H2⟩
  | lam RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | app | proj | forallE => cases E

/-- Computation preserves a literal Pi head and computes its domain. -/
theorem Compute.forallE_shape (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : Compute Step (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute Step A A' := by
  generalize E : ProofShape.forallE A B = e at R
  induction R generalizing A B with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨_, _, E, R⟩ := H.forallE_shape
    exact ⟨_, _, E, .beta R⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, _, rfl, H1⟩ := ih1 E
    obtain ⟨_, _, E2, H2⟩ := ih2 rfl
    exact ⟨_, _, E2, H1.trans H2⟩
  | forallE RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | app | proj | lam => cases E

variable [Params]

/-- Every recovered type of a literal lambda is a Pi whose domain is reached
by computation from the displayed domain. Oracle entries cannot alter it. -/
theorem TypeRecovery.lam_shape (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : TypeRecovery Step σ (.lam A b) out) :
    ∃ D C, out = .forallE D C ∧ Compute Step A D := by
  generalize E : ProofShape.lam A b = e at R
  induction R with
  | lam R => cases E; exact ⟨_, _, rfl, .refl⟩
  | convert _ RC ih =>
    obtain ⟨_, _, rfl, HD⟩ := ih E
    obtain ⟨_, _, E', HD'⟩ := RC.forallE_shape hroot
    exact ⟨_, _, E', HD.trans HD'⟩
  | bvar | sort | const | app | forallE | proj => cases E

/-- Inferred context-free comparison of lambdas compares their domains. -/
theorem Compare.lam_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : Compare Step false (.lam A a) (.lam B b)) : Compare Step false A B := by
  generalize Ea : ProofShape.lam A a = x at H
  generalize Eb : ProofShape.lam B b = y at H
  generalize Em : false = mode at H
  induction H generalizing A B a b with
  | refl => cases Ea.trans Eb.symm; exact .refl
  | lam HA _ => cases Em; cases Ea; cases Eb; exact HA
  | etaLams HD _ => cases Em; cases Ea; cases Eb; exact HD
  | etaL | etaR | structL | structR => cases Em
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.lam_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.lam_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm Em)
  | sort | const | app | proj | forallE => cases Ea

/-- Inferred contextual comparison likewise reflects the displayed lambda
domains. Recovered eta contributes a computational domain path, which can be
prepended directly; no transitivity of comparison is assumed. -/
theorem RecoveredCompare.lam_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : RecoveredCompare Step σ τ false (.lam A a) (.lam B b)) :
    RecoveredCompare Step σ τ false A B := by
  generalize Ea : ProofShape.lam A a = x at H
  generalize Eb : ProofShape.lam B b = y at H
  generalize Em : false = mode at H
  induction H generalizing A B a b with
  | base H => cases Ea; cases Eb; cases Em; exact .base (H.lam_domains hroot)
  | lam HA _ => cases Em; cases Ea; cases Eb; exact HA
  | etaL HR HD _ =>
    cases Em; cases Ea; cases Eb
    obtain ⟨_, _, E, RD⟩ := HR.lam_shape hroot
    cases E
    exact .compute .refl RD HD
  | etaR HR HD _ =>
    cases Em; cases Ea; cases Eb
    obtain ⟨_, _, E, RD⟩ := HR.lam_shape hroot
    cases E
    exact .compute RD .refl HD
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.lam_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.lam_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm Em)
  | app | proj | forallE => cases Ea

end Lean4Lean.VEnv.Strengthening.ProofShape
