import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation

/-! # Eq computation closed under certified computational joins

The indices may themselves compute using certified Eq and general singleton
primitives. A certified common output constructs the next Eq certificate,
without imposing a bound on nesting or assuming arbitrary endpoint transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_prefix_certified_with_family eqTypeProbe_compute_of_prefix
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
variable [Params]

/-- Certified computation of the two indices to one output certifies the
reflexive/requested Eq family comparison and all its future residuals. -/
theorem proofErase_certified_join_eq_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hw : w.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort w))
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp w α a a)) (proofErase Γ (eqApp w α a b)) := by
  apply proofErase_certified_join_family heq hs hΓ (HasType.eqApp heq hw hα ha ha)
    (HasType.eqApp heq hw hα ha hb)
    (shared := ProofShape.eqProofType w (proofErase Γ α) shared shared)
  · rw [proofErase_eqProofType heq hw hΓ hα ha ha]
    exact .app (.app (.app .refl .refl) RA) RA
  · rw [proofErase_eqProofType heq hw hΓ hα ha hb]
    exact .app (.app (.app .refl .refl) RA) RB

/-- The generated Eq prefix computes with a certified family guard whenever
its indices have a certified computational join. Existing certified primitive
paths can therefore be used to build further certified Eq primitives. -/
theorem proofErase_certified_join_eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (RA : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) shared)
    (RB : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) shared) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_joint_carrier_reflect (erased_beta_stable_joint_descent heq hs)
    hΓ ha hb (.carrierChecked (.compute RA RB (.leaf .refl)))
  exact eq_prefix_certified_with_family heq hregistry hΓ ht hnp hab.toU
    (proofErase_certified_join_eq_family heq hs hw hΓ hα ha hb RA RB)

/-- A type probe with certifiably joined proposition indices computes to its exact
minor in the certified relation. The equality proof may be arbitrary. -/
theorem eqTypeProbe_compute_certified_of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (RP : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ P) shared)
    (RQ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ Q) shared) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  exact eqTypeProbe_compute_of_prefix heq hΓ hS hP hQ hq
    (proofErase_certified_join_eq_prefix heq hs hregistry hΓ ht hn RP RQ)

end Lean4Lean.VEnv.Strengthening
