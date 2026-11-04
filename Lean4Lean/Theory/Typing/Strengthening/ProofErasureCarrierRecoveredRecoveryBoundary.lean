import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnitImages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion

/-! # Native lookup convergence is necessary at distinct variable endpoints

Recovered-carrier comparison removes the old variable-injectivity obstruction
only when the native lookup types can compute to a common raw result. The
conditional typed identity peak below isolates the remaining test: instantiate
two convertible positive carrier typings whose native lookup types do not join.
The companion ConvertedUnitBoundary module supplies such a typed instance
from a closed positive empty structure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Distinct variables can compare in the enlarged language only if their
native lookup types have a common computational result. This necessary
condition includes every compatible and computation wrapper of the grammar. -/
theorem ProofShape.CarrierRecoveredCompare.bvar_lookup_join
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : CarrierRecoveredCompare Step Δ mode (.bvar i) (.bvar j)) :
    i = j ∨ ∃ T, ScopedCompute Step Δ (contextOracle Δ i) T ∧
      ScopedCompute Step Δ (contextOracle Δ j) T := by
  generalize EA : ProofShape.bvar i = a at H
  generalize EB : ProofShape.bvar j = b at H
  induction H generalizing i j with
  | base H => exact .inl ((EA.symm ▸ EB.symm ▸ H).bvar_injective hhead)
  | recovered RA RB H =>
    cases EA
    cases EB
    exact .inr ⟨_, RA.bvar_compute, RB.bvar_compute⟩
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).bvar_fixed hhead).symm ((EB ▸ RB).bvar_fixed hhead).symm
  | symm H ih =>
    rcases ih EB EA with E | ⟨T, RA, RB⟩
    · exact .inl E.symm
    · exact .inr ⟨T, RB, RA⟩
  | app | proj | lam | forallE => cases EA

/-- Nonjoining native lookup types exclude every recovered-carrier comparison
between distinct variable endpoints, including comparison at the full union. -/
theorem ProofShape.CarrierRecoveredCompare.not_of_unjoined_lookup
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) (hne : i ≠ j)
    (hn : ¬ ∃ T, ScopedCompute Step Δ (contextOracle Δ i) T ∧
      ScopedCompute Step Δ (contextOracle Δ j) T) :
    ¬ CarrierRecoveredCompare Step Δ mode (.bvar i) (.bvar j) := by
  intro H
  exact (H.bvar_lookup_join hhead).elim hne hn

private theorem positive_identity
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ u)))
    (hx : env.HasType univs Γ x A) :
    env.HasType univs Γ (.app (.lam A (.bvar 0)) x) A ∧
    proofErase Γ (.app (.lam A (.bvar 0)) x) =
      .app (.lam (proofErase Γ A) (.bvar 0)) (proofErase Γ x) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hb : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hF := HasType.lam hA hb
  have ht : env.HasType univs Γ (.app (.lam A (.bvar 0)) x) A := by
    simpa only [VExpr.inst_lift] using hF.app hx
  have hn := not_proof_at_positive_type hΓ hA ht
  refine ⟨ht, ?_⟩
  rw [show proofErase Γ (.app (.lam A (.bvar 0)) x) = .app _ _ from if_neg hn,
    show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from
      if_neg (not_isProof_fn hΓ hF hx hn),
    show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_proof_at_positive_type hΓA (hA.weak henv) hb)]

/-- Conditional typed beta obstruction for the enlarged grammar. A positive
common carrier guard compares two identity applications, but their variable
reducts cannot compare if their native lookup types do not join. The remaining
missing instance is exactly the nonjoining-lookup premise together with these
typed positive-carrier hypotheses; the companion ConvertedUnitBoundary
module discharges them from a closed positive empty structure. -/
theorem carrier_recovered_identity_beta_of_unjoined_lookup
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ u)))
    (hi : env.HasType univs Γ (.bvar i) A) (hj : env.HasType univs Γ (.bvar j) A)
    (hne : i ≠ j)
    (HC : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)))
    (hn : ¬ ∃ T, ScopedCompute Target (proofEraseCtx Γ) (contextOracle (proofEraseCtx Γ) i) T ∧
      ScopedCompute Target (proofEraseCtx Γ) (contextOracle (proofEraseCtx Γ) j) T) :
    ∃ a b, env.HasType univs Γ a A ∧ env.HasType univs Γ b A ∧
      CarrierRecoveredCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) ∧
      ProofShape.BetaRed (proofErase Γ a) (proofErase Γ (.bvar i)) ∧
      ProofShape.BetaRed (proofErase Γ b) (proofErase Γ (.bvar j)) ∧
      ¬ CarrierRecoveredCompare Target (proofEraseCtx Γ) true
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  obtain ⟨ha, Ea⟩ := positive_identity hΓ hA hi
  obtain ⟨hb, Eb⟩ := positive_identity hΓ hA hj
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hA hi)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hA hj)
  refine ⟨_, _, ha, hb, ?_, ?_, ?_, ?_⟩
  · rw [Ea, Eb]
    have HR : ScopedTypeRecovery Step (proofEraseCtx Γ)
        (.lam (proofErase Γ A) (.bvar 0))
        (.forallE (proofErase Γ A) ((proofErase Γ A).liftN 1)) := .lam .bvar
    exact .base (.appCarrier HR (.leaf .refl) HC)
  · rw [Ea]
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one,
      ProofShape.Subst.cons, ProofShape.Subst.liftN] using
      (ProofShape.BetaRed.beta (A := proofErase Γ A) (b := .bvar 0) (a := proofErase Γ (.bvar i)))
  · rw [Eb]
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one,
      ProofShape.Subst.cons, ProofShape.Subst.liftN] using
      (ProofShape.BetaRed.beta (A := proofErase Γ A) (b := .bvar 0) (a := proofErase Γ (.bvar j)))
  · rw [Ei, Ej]
    exact CarrierRecoveredCompare.not_of_unjoined_lookup hhead hne hn

end Lean4Lean.VEnv.Strengthening
