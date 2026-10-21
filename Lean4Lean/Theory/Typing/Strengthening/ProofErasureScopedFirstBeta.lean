import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation

/-! # The first head beta of a lambda application

Before the head beta contracts, the lambda and argument compute separately.
The witness retains the exact contractum and the entire remaining computation.
No confluence, typing, or substitution closure is needed for this decomposition.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape

private theorem scoped_lam_shape
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.lam A b) out) : ∃ A' b', out = .lam A' b' := by
  generalize E : ProofShape.lam A b = source at R
  induction R generalizing A b with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    cases E
    obtain ⟨A', b', E, _, _⟩ := H.lam_inv
    exact ⟨A', b', E⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A', b', rfl⟩ := ih₁ E
    exact ih₂ rfl
  | lam => cases E; exact ⟨_, _, rfl⟩
  | app | proj | forallE => cases E

private theorem beta_first_head (R : BetaRed (.app (.lam A b) x) out) :
    (∃ A' b' x', out = .app (.lam A' b') x' ∧
      BetaRed (.lam A b) (.lam A' b') ∧ BetaRed x x') ∨
    (∃ A' b' x', BetaRed (.lam A b) (.lam A' b') ∧ BetaRed x x' ∧
      BetaRed (b'.inst x') out) := by
  generalize E : ProofShape.app (.lam A b) x = source at R
  induction R generalizing A b x with
  | refl => exact .inl ⟨A, b, x, E.symm, .refl, .refl⟩
  | beta => cases E; exact .inr ⟨_, _, _, .refl, .refl, .refl⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', x', rfl, RF, RX⟩ | ⟨A', b', x', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', x'', EO, RF', RX'⟩ | ⟨A'', b'', x'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', x'', EO, RF.trans RF', RX.trans RX'⟩
      · exact .inr ⟨A'', b'', x'', RF.trans RF', RX.trans RX', RT⟩
    · exact .inr ⟨A', b', x', RF, RX, RT.trans R₂⟩
  | app RF RX =>
    cases E
    obtain ⟨A', b', EO, _, _⟩ := RF.lam_inv
    subst EO
    exact .inl ⟨_, _, _, rfl, RF, RX⟩
  | proj | lam | forallE => cases E

/-- Either a lambda application retains its application boundary after separate
computations, or its head beta contracts after those computations. In the
second case the exact contractum still computes to the original final output. -/
theorem ScopedCompute.lambda_app_or_beta
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.app (.lam A b) x) out) :
    (∃ A' b' x', out = .app (.lam A' b') x' ∧
      ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧ ScopedCompute Step Δ x x') ∨
    (∃ A' b' x', ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute Step Δ x x' ∧ ScopedCompute Step Δ (b'.inst x') out) := by
  generalize E : ProofShape.app (.lam A b) x = source at R
  induction R generalizing A b x with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    cases E
    rcases beta_first_head H with ⟨A', b', x', EO, RF, RX⟩ | ⟨A', b', x', RF, RX, RT⟩
    · exact .inl ⟨A', b', x', EO, .beta RF, .beta RX⟩
    · exact .inr ⟨A', b', x', .beta RF, .beta RX, .beta RT⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', x', rfl, RF, RX⟩ | ⟨A', b', x', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', x'', EO, RF', RX'⟩ | ⟨A'', b'', x'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', x'', EO, RF.trans RF', RX.trans RX'⟩
      · exact .inr ⟨A'', b'', x'', RF.trans RF', RX.trans RX', RT⟩
    · exact .inr ⟨A', b', x', RF, RX, RT.trans R₂⟩
  | app RF RX =>
    cases E
    obtain ⟨A', b', EO⟩ := scoped_lam_shape hhead RF
    subst EO
    exact .inl ⟨_, _, _, rfl, RF, RX⟩
  | proj | lam | forallE => cases E

/-- A literal universe output forces the head-beta alternative, with the
complete tail to that same universe retained. -/
theorem ScopedCompute.lambda_app_sort
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.app (.lam A b) x) (.sort v)) :
    ∃ A' b' x', ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute Step Δ x x' ∧ ScopedCompute Step Δ (b'.inst x') (.sort v) := by
  rcases R.lambda_app_or_beta hhead with ⟨_, _, _, E, _, _⟩ | H
  · cases E
  · exact H

end Lean4Lean.VEnv.Strengthening.ProofShape
