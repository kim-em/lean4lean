import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedJoinEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathProbeBoundary

/-! # Checking transport across certified Eq type probes

A certified join of the indices computes the probe to its minor. Carrier
checking and body comparison therefore pull back from the minor to the probe.
This reaches the closed example excluded by every old Pi/Box/beta path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BetaRed.forallE_shape
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredLambdaDomains
variable [Params]

/-- All certified carrier guards at the minor also check at the Eq probe,
provided its proposition indices have a certified computational join. -/
theorem eqTypeProbe_certified_carrier_of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (RP : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ P) shared)
    (RQ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ Q) shared)
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ S) a b) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) a b :=
  .carrierCompute (eqTypeProbe_compute_certified_of_join heq hs hregistry hΓ hS hP hQ hq RP RQ) H

/-- Every certified body comparison under the minor survives replacement of
that binder by the Eq probe. Its endpoints stay fixed, and the result retains
certificates for subsequent transport. This is the reverse-computation direction. -/
theorem eqTypeProbe_certified_context_of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (RP : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ P) shared)
    (RQ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ Q) shared)
    (ha : env.HasType univs (S :: Γ) a T) (hb : env.HasType univs (S :: Γ) b T)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (S :: Γ)) mode
      (proofErase (S :: Γ) a) (proofErase (S :: Γ) b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (eqTypeProbe u S P Q q :: Γ)) mode
      (proofErase (eqTypeProbe u S P Q q :: Γ) a)
      (proofErase (eqTypeProbe u S P Q q :: Γ) b) := by
  have HPQ := proofErase_joint_carrier_reflect (erased_beta_stable_joint_descent heq hs)
    hΓ hP hQ (.carrierChecked (.compute RP RQ (.leaf .refl)))
  exact proofErase_joint_context_compute_back (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) hΓ
    (eqTypeProbe_defeq heq hΓ hS hP hQ hq HPQ.toU)
    (eqTypeProbe_compute_certified_of_join heq hs hregistry hΓ hS hP hQ hq RP RQ) ha hb H

/-- Certified primitive computation reaches a closed type conversion excluded
by every Pi/Box/beta path. This discharges the earlier reflexive-probe obstacle;
it does not assert coverage of arbitrary definitional equality. -/
theorem certified_probe_beyond_box_beta_paths
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∃ A B, env.IsDefEq univs [] A B (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx []) (proofErase [] B) (proofErase [] A) ∧
      ¬ TypeChangePath (BoxTypeChange family) [] (.succ .zero) A B := by
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType univs [] P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hS : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq := HasType.eqReflApp heq (by trivial) hS hP
  have HE := eqTypeProbe_defeq heq (by trivial) hS hP hP hq ⟨_, hP⟩
  exact ⟨_, _, HE.symm,
    eqTypeProbe_compute_certified_of_beta_join heq hregistry (by trivial) hS hP hP hq .refl .refl,
    no_box_path_to_sort_probe heq (by trivial) hP hP hq⟩

/-- A closed nested Eq computation whose outer proposition indices have no
beta join. The inner certified primitive supplies their computational join,
so the general construction is strictly broader than beta-joined indices. -/
theorem certified_nested_probe_without_beta_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∃ P Q q, env.HasType univs [] P (.sort .zero) ∧
      env.HasType univs [] Q (.sort .zero) ∧
      env.HasType univs [] q (eqApp (.succ .zero) (.sort .zero) P Q) ∧
      (¬ ∃ shared, ProofShape.BetaRed (proofErase [] P) shared ∧
        ProofShape.BetaRed (proofErase [] Q) shared) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx [])
        (proofErase [] (eqTypeProbe (.succ .zero) (.sort .zero) P Q q))
        (proofErase [] (.sort .zero)) := by
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType univs [] P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hS : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hr := HasType.eqReflApp heq (by trivial) hS hP
  let Q := eqTypeProbe .zero P P P (eqReflApp (.succ .zero) (.sort .zero) P)
  have hQ : env.HasType univs [] Q (.sort .zero) :=
    eqTypeProbe_typed heq (by trivial) hP hP hP hr
  have HE : env.IsDefEq univs [] Q P (.sort .zero) :=
    eqTypeProbe_defeq heq (by trivial) hP hP hP hr hP.toU
  have hq := (IsDefEq.eqApp_r heq (by trivial) hS hP HE.symm).defeq hr
  have RQ : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx [])
      (proofErase [] Q) (proofErase [] P) :=
    eqTypeProbe_compute_certified_of_beta_join heq hregistry (by trivial) hP hP hP hr .refl .refl
  refine ⟨P, Q, _, hP, hQ, hq, ?_,
    eqTypeProbe_compute_certified_of_join heq hs hregistry (by trivial) hS hP hQ hq .refl RQ⟩
  rintro ⟨shared, RP, RQ⟩
  have EP : proofErase [] P = .forallE (proofErase [] (.sort .zero))
      (proofErase [VExpr.sort .zero] (.bvar 0)) := if_neg (not_isProof_of_sort (by trivial) hP)
  rw [EP] at RP
  obtain ⟨A, B, ES, _⟩ := BetaRed.forallE_shape RP
  rw [eqTypeProbe_erase heq (by trivial) hP hP hP hr] at RQ
  obtain ⟨args, EQ, _⟩ := RQ.const_spine
  have EC := congrArg ProofShape.constHead (ES.symm.trans EQ)
  simp only [ProofShape.constHead, constHead_mkApps] at EC
  cases EC

end Lean4Lean.VEnv.Strengthening
