import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionObservations
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure

/-! # Reselecting native heads after controlled expansion

A native lambda output remains beta-exposable as a Pi after every conversion.
More generally an existing native Pi certificate can follow any expanded type
computation and reselect a Pi at the same stage. Domains need not be pure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Native lambda recovery starts with a Pi observation and preserves it through
every selected-type conversion whenever primitive computation does so. -/
theorem ProofShape.ScopedTypeRecovery.lambda_headObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → HeadObservation S a o → HeadObservation S b o)
    (R : ScopedTypeRecovery Step Δ (.lam A b) out) : HeadObservation S out .pi := by
  generalize E : ProofShape.lam A b = source at R
  induction R with
  | lam => cases E; exact Obs.pi
  | convert _ RC ih => exact RC.headObservation hstep (ih E)
  | bvar | sort | const | app | forallE | proj => cases E

/-- Native recovery of a literal sort keeps a sort observation through all
conversions, even when the displayed output is an expanded application. -/
theorem ProofShape.ScopedTypeRecovery.sort_headObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → HeadObservation S a o → HeadObservation S b o)
    (R : ScopedTypeRecovery Step Δ (.sort u) out) : HeadObservation S out .sort := by
  generalize E : ProofShape.sort u = source at R
  induction R with
  | sort => cases E; exact Obs.sort
  | convert _ RC ih => exact RC.headObservation hstep (ih E)
  | bvar | const | lam | app | forallE | proj => cases E

/-- Native Pi formation likewise keeps a sort observation, without constraints
on either its domain or its dependent codomain syntax. -/
theorem ProofShape.ScopedTypeRecovery.forallE_headObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → HeadObservation S a o → HeadObservation S b o)
    (R : ScopedTypeRecovery Step Δ (.forallE A B) out) : HeadObservation S out .sort := by
  generalize E : ProofShape.forallE A B = source at R
  induction R with
  | forallE => cases E; exact Obs.sort
  | convert _ RC ih => exact RC.headObservation hstep (ih E)
  | bvar | sort | const | lam | app | proj => cases E

/-- An existing native lambda certificate reselects a literal Pi by beta at
its unchanged expanded stage; no no-Pi-root assumption is used. -/
theorem expansion_stage_native_lambda_pi
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) Δ (.lam A b) out) :
    ∃ A' B', ProofShape.BetaRed out (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedExpansionStage D stage) Δ (.lam A b) (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := (R.lambda_headObservation
    (erased_expansion_stage_headObservation stage) (S := fun _ _ => False)).pi_exposure
  exact ⟨A', B', RB, R.convert (.beta RB)⟩

/-- Full-union native lambda selection has the same exact beta exposure. -/
theorem expansion_union_native_lambda_pi
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ (.lam A b) out) :
    ∃ A' B', ProofShape.BetaRed out (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedExpansionUnion D) Δ (.lam A b) (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := (R.lambda_headObservation erased_expansion_union_headObservation
    (S := fun _ _ => False)).pi_exposure
  exact ⟨A', B', RB, R.convert (.beta RB)⟩

/-- A native Pi can follow an arbitrary later selected-type computation and
recover another literal Pi at that same stage. The selected type beta-reduces
to the new native output; its domains need not belong to a pure fragment. -/
theorem expansion_stage_native_pi_selection
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) Δ source (.forallE A B))
    (RS : ScopedCompute (ErasedExpansionStage D stage) Δ (.forallE A B) selected) :
    ∃ A' B', ScopedTypeRecovery (ErasedExpansionStage D stage) Δ source (.forallE A' B') ∧
      ProofShape.BetaRed selected (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := expansion_stage_pi_persistence RS
  exact ⟨A', B', (R.convert RS).convert (.beta RB), RB⟩

/-- The selection repair also works at arbitrary finite depth in the union. -/
theorem expansion_union_native_pi_selection
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) Δ source (.forallE A B))
    (RS : ScopedCompute (ErasedExpansionUnion D) Δ (.forallE A B) selected) :
    ∃ A' B', ScopedTypeRecovery (ErasedExpansionUnion D) Δ source (.forallE A' B') ∧
      ProofShape.BetaRed selected (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := expansion_union_pi_persistence RS
  exact ⟨A', B', (R.convert RS).convert (.beta RB), RB⟩

/-- For an actual retained lambda, reselected native Pi syntax has actual lower
representatives and a typing of the original lambda at that Pi. -/
theorem proofErase_expansion_stage_native_lambda_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ (.lam A b) T)
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out) :
    ∃ A' B', env.HasType univs Γ (.lam A b) (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (.lam A b)) (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      ProofShape.BetaRed out (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) := by
  have hn : ¬ IsProof Γ (.lam A b) := fun hp => R.ne_proof (proofErase_eq_proof.2 hp)
  have EE : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  obtain ⟨X, Y, RB, RN⟩ := expansion_stage_native_lambda_pi (EE ▸ R)
  rw [← EE] at RN
  obtain ⟨A', B', hf', EA, EB⟩ := proofErase_scoped_recovered_pi_descend
    (erased_expansion_stage_descent heq hs stage) hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at EA EB
  rw [← EA, ← EB] at RN RB
  exact ⟨A', B', hf', RN, RB⟩

/-- An actual lambda can select a whole-Pi beta expansion as its native type.
That output is not syntactically a Pi, but the new exposure theorem reselects
a Pi at stage zero. The domain A is arbitrary well-formed syntax. -/
theorem expansion_native_whole_pi_example
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ∃ out, ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.sort .zero))) out ∧
      (∀ X Y, out ≠ .forallE X Y) ∧
      ∃ X Y, ProofShape.BetaRed out (.forallE X Y) ∧
        ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
          (proofErase Γ (.lam A (.sort .zero))) (.forallE X Y) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb : env.HasType univs (A :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hf := HasType.lam hA hb
  have EE : proofErase Γ (.lam A (.sort .zero)) = .lam (proofErase Γ A) (.sort .zero) := by
    rw [show proofErase Γ (.lam A (.sort .zero)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf)]
    rw [show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓA hb)]
  have RN : ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.sort .zero))) (.forallE (proofErase Γ A) (.sort (.succ .zero))) := by
    rw [EE]
    exact .lam (.sort (by trivial))
  have RE := RN.convert (ScopedCompute.base (Or.inr (ConstantExpansion.intro
    (a := .forallE (proofErase Γ A) (.sort (.succ .zero))) (by intro E; cases E))))
  refine ⟨_, RE, ?_, ?_⟩
  · intro X Y E
    cases E
  · obtain ⟨X, Y, RB, RPi⟩ := expansion_stage_native_lambda_pi (EE ▸ RE)
    exact ⟨X, Y, RB, EE ▸ RPi⟩

end Lean4Lean.VEnv.Strengthening
