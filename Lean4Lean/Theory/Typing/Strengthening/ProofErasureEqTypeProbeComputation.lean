import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe

/-! # The primitive stage needed by a type-valued Eq probe

Core computation cannot change the probe's head, even at definitionally equal
indices. An actual stage-n endpoint comparison computes it to its minor at
stage n+1. Thus a semantic typing conversion cannot be assigned cost zero in
an induction that constructs explicit carrier guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
open private core_computed_probe_prefix_excluded
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
open private eq_general
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral
variable [Params]

/-- A checked endpoint guard computes the arbitrary type-valued probe to its
minor at the next primitive stage. No semantic exposure or beta law is used. -/
theorem eqTypeProbe_compute_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HC : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q)) :
    ScopedCompute (ErasedJointStage D (stage+1)) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  have HG := eq_general heq (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs stage) hregistry hΓ ht hn (.carrierChecked HC)
  have hE := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hL := HasType.lam hE (hS.weak henv)
  have hLq : env.HasType univs Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q)
      (.sort u) := hL.app hq
  have EB : proofErase Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q) =
      .app (proofErase Γ (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift)) .proof := by
    rw [show proofErase Γ (.app (.lam (eqApp (.succ .zero) (.sort .zero) P Q) S.lift) q) =
        .app _ _ from if_neg (not_isProof_of_sort hΓ hLq),
      proofErase_eq_proof.2 ⟨_, hq, hE⟩]
  have HB := proofErase_beta_forward hΓ hLq
    (VExpr.BetaRed.beta (A := eqApp (.succ .zero) (.sort .zero) P Q) (b := S.lift) (a := q))
  rw [EB, VExpr.inst_lift] at HB
  have hfull := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have EF : proofErase Γ (eqTypeProbe u S P Q q) =
      .app (proofErase Γ (eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q)) .proof := by
    rw [show proofErase Γ (eqTypeProbe u S P Q q) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hfull), proofErase_eq_proof.2 ⟨_, hq, hE⟩]
    rfl
  rw [EF]
  exact ScopedCompute.trans (ScopedCompute.app (.base (.inr (.inl HG))) .refl) (.beta HB)

/-- No stage-zero path changes the Eq.rec head of a typed type probe.
Argument computations are unrestricted, and the equality major may be any
proof. This statement does not exclude later singleton computation. -/
theorem eqTypeProbe_zero_head
    (heq : env.HasCanonicalEq)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (R : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) out) : out.constHead = some ``Eq.rec := by
  by_contra hne
  rw [eqTypeProbe_erase heq hΓ hS hP hQ hq] at R
  obtain ⟨k, args, out, _, HA, H⟩ := R.head_occurrence hne
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact core_computed_probe_prefix_excluded (erased_joint_stage_head 0)
    (hregistry.trans hlookup) (hr.eqRec_target heq hn).2.1 hRec HA H

end Lean4Lean.VEnv.Strengthening
