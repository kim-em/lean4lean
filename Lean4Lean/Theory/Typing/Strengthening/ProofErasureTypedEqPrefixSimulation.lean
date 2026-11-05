import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedFirstStageSimulation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixAnnotationRetention

/-! # Typed Eq-prefix cases of first-stage simulation

A raw prefix with a typed realization supplies the actual canonical argument
typings. Lower-stage simulation can therefore be used on its carrier and
endpoints. When those paths expose a stage-zero guard, the exact prefix result
is available in stage one, including the original proof-domain annotation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Operational guard exposure discharges a typed raw Eq-prefix simulation
case. The canonical source realization supplies all necessary sort witnesses;
no sort witness for an arbitrary raw prefix is postulated. -/
theorem first_stage_typed_eq_prefix_of_computed_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (Rα : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ α α')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ b b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) Δ α' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (eqProofType w α a b) (m.liftN 1)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Eα, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
  have hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Ee
    cases Ee
  have H := first_stage_eq_prefix_of_computed_guard heq hs hΓ ht hn
    (by simpa only [EΓ, Eα] using Rα)
    (by simpa only [EΓ, Ea] using Ra) .refl
    (by simpa only [EΓ, Eb] using Rb)
    (by simpa only [EΓ] using HG)
  simpa only [EΓ, Ee, Eα, Ea, Eb, Em] using H

/-- A typed lower-stage simulation hypothesis can be applied to the carrier
and both endpoints of a retained Eq prefix. Thus lower-stage guard exposure
already gives the exact first-stage contraction, without increasing depth. -/
theorem first_stage_typed_eq_prefix_of_lower_guard_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (Rα : ScopedCompute Source Δ α α')
    (Ra : ScopedCompute Source Δ a a')
    (Rb : ScopedCompute Source Δ b b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) Δ α' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (eqProofType w α a b) (m.liftN 1)) := by
  apply first_stage_typed_eq_prefix_of_computed_guard heq hs HT (HG := HG)
  all_goals
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Eα, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
    obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  · exact hcompute ⟨Γ, α₀, _, hΓ, EΓ, hα, Eα⟩ Rα
  · exact hcompute ⟨Γ, a₀, _, hΓ, EΓ, ha, Ea⟩ Ra
  · exact hcompute ⟨Γ, b₀, _, hΓ, EΓ, hb, Eb⟩ Rb

/-- The lower-stage endpoint-join case of the typed Eq-prefix induction is
settled: a common reduct supplies a reflexive stage-zero guard, and typed
simulation of the two paths gives the exact original prefix result. Arbitrary
recursive carrier certificates need not supply such a join and remain open. -/
theorem first_stage_typed_eq_prefix_of_lower_endpoint_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (Ra : ScopedCompute Source Δ a shared) (Rb : ScopedCompute Source Δ b shared) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (eqProofType w α a b) (m.liftN 1)) :=
  first_stage_typed_eq_prefix_of_lower_guard_exposure heq hs hcompute HT .refl Ra Rb
    (.carrierChecked (.leaf .refl))

end Lean4Lean.VEnv.Strengthening
