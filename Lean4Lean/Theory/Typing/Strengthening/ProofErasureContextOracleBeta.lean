import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointOracleBetaTransport

/-! # Interpreted beta changes of context annotations

An identity interpretation and pointwise beta paths of the type oracle extend
under a beta-reduced binder. Source realizations supply the domain typing;
forward beta replay constructs the new binder, without inverse weakening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private identity_cons from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointOracleBetaTransport
variable [Params]

/-- A typed domain-sort witness survives pure beta reduction of its erasure. -/
theorem ProofShape.DomainSort.beta (H : DomainSort Δ A u) (R : ProofShape.BetaRed A A') :
    DomainSort Δ A' u := by
  obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := H
  obtain ⟨e', RE, EE⟩ := proofErase_beta_replay hΓ ht (Ee ▸ R)
  exact ⟨Γ, e', hΓ, EΓ, (beta_eq hΓ ht RE).hasType.2, EE⟩

private theorem beta_cons (R : ProofShape.BetaRed A A') :
    ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨B', RB, EB'⟩ := proofErase_beta_replay hΓ hB (EB ▸ R)
    have W : ContextSubstitution (proofEraseCtx (B :: Γ)) (proofEraseCtx (B' :: Γ)) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx hΓ (.succ .zero (beta_eq hΓ hB RB))
    have H := W (Γ := B :: Γ) ⟨hΓ, u, hB⟩ rfl
    simpa only [proofEraseCtx, EB', EΓ] using H

/-- Interpreted identity context changes extend under independently
beta-reduced domains. Only realized source contexts need domain typings. -/
theorem ProofShape.ContextSubstitution.cons_beta
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) (R : ProofShape.BetaRed A A') :
    ContextSubstitution (A :: Δ) (A' :: Δ') ProofShape.Subst.id := by
  have H : ContextSubstitution (A :: Δ) (A' :: Δ') (fun i => (ProofShape.Subst.id i).subst ProofShape.Subst.id) :=
    ContextSubstitution.comp (beta_cons (Δ := Δ) R) (identity_cons (A := A') W)
  intro Γ hΓ EΓ
  simpa only [ProofShape.subst_id] using H hΓ EΓ

/-- Identity context transport together with beta reduction of every oracle
entry. This is evidence about the two contexts, not a checker closure axiom. -/
structure ContextOracleBeta (Δ Δ' : List ProofShape) : Prop where
  interpretation : ContextSubstitution Δ Δ' ProofShape.Subst.id
  entries : ∀ i, ProofShape.BetaRed (contextOracle Δ i) (contextOracle Δ' i)

/-- The context evidence extends under a beta-reduced binder domain. -/
theorem ContextOracleBeta.cons (W : ContextOracleBeta Δ Δ') (R : ProofShape.BetaRed A A') :
    ContextOracleBeta (A :: Δ) (A' :: Δ') := by
  refine ⟨ContextSubstitution.cons_beta W.interpretation R, ?_⟩
  intro i
  cases i with
  | zero => exact R.liftN
  | succ i => exact (W.entries i).liftN

/-- Ambient sort witnesses transport with a beta-reduced domain. -/
theorem ContextOracleBeta.sort (W : ContextOracleBeta Δ Δ') (S : DomainSort Δ A u)
    (R : ProofShape.BetaRed A A') : DomainSort Δ' A' u := by
  have H := ContextSubstitution.sort W.interpretation (S.beta R)
  simpa only [ProofShape.subst_id] using H

end Lean4Lean.VEnv.Strengthening
