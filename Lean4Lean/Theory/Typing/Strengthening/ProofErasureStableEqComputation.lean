import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilySpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation

/-! # Certified Eq primitives from future comparisons without joins

A future certificate for the index comparison can be placed in the literal Eq
family and then in its generated singleton guard. Head eta is one constructive
source; the indices need not compute to a common shape.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_prefix_certified_with_family eqTypeProbe_compute_of_prefix
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
variable [Params]

/-- A future comparison of typed indices certifies the corresponding Eq
family comparison. The repeated carrier and left index retain their own
reflexive certificates through independent beta reductions. -/
theorem proofErase_stable_eq_family
    (heq : env.HasCanonicalEq) (hw : w.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort w))
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp w α a a)) (proofErase Γ (eqApp w α a b)) := by
  rw [proofErase_eqProofType heq hw hΓ hα ha ha, proofErase_eqProofType heq hw hΓ hα ha hb]
  exact BetaStableFamily.const_spine (.cons
    (proofErase_beta_join_family hΓ hα hα .refl .refl) (.cons
      (proofErase_beta_join_family hΓ ha ha .refl .refl) (.cons H .nil)))

/-- A future index-comparison certificate constructs the exact certified Eq
prefix. Its base comparison supplies actual index equality by reflection;
no separate semantic equality or computational join is a premise. -/
theorem proofErase_stable_eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs)
    hΓ ha hb (.carrierChecked H.base)
  exact eq_prefix_certified_with_family heq hregistry hΓ ht hnp hab.toU
    (proofErase_stable_eq_family heq hw hΓ hα ha hb H)

/-- Future comparison of proposition indices computes their type probe to
its exact minor in the certified relation, whether or not the indices join. -/
theorem eqTypeProbe_compute_certified_of_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  exact eqTypeProbe_compute_of_prefix heq hΓ hS hP hQ hq
    (proofErase_stable_eq_prefix heq hs hregistry hΓ ht hn H)

end Lean4Lean.VEnv.Strengthening
