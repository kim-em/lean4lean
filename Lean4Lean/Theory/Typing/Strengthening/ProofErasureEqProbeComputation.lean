import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral

/-! # Constructing the Eq probe's finite computation from its endpoint guard

A plain finite-stage proposition comparison licenses the actual generated
singleton prefix. One application and one beta contraction then return Prop.
No future beta-stability certificate or semantic head premise is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
open private eq_general
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral
variable [Params]

/-- The plain endpoint certificate already gives a general generated singleton
step for the probe prefix at the same guard stage. It does not need the
stronger beta/substitution-stable family certificate used by certification. -/
theorem eqSortProbe_general_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (HC : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q)) :
    JointSingletonPrimitive (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))) (.sort .zero) Q))
      (.lam (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q)) (.sort .zero)) := by
  obtain ⟨T, ht, hn⟩ := probe_prefix_typed heq hΓ hP hQ
  have HG := eq_general heq (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs stage) hregistry hΓ ht hn (JointCheck.carrierChecked HC)
  simp only [VExpr.lift, VExpr.liftN] at HG
  have hE := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
  have hL := HasType.lam hE (HasType.sort (l := .zero) (by trivial))
  have hnL := not_isProof_function_to_sort hΓ hL
  rw [show proofErase Γ (.lam (eqApp (.succ .zero) (.sort .zero) P Q) (.sort .zero)) =
      .lam _ _ from if_neg hnL,
    show proofErase (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓE (HasType.sort (by trivial)))] at HG
  exact HG

/-- A stage-n endpoint comparison produces an exact Prop result at stage n+1.
The only primitive is the general singleton from eqSortProbe_general_prefix;
the rest is compatible application and beta. The proof major may be neutral. -/
theorem eqSortProbe_compute_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HC : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q)) :
    ScopedCompute (ErasedJointStage D (stage+1)) (proofEraseCtx Γ)
      (proofErase Γ (eqSortProbe P Q q)) (.sort .zero) := by
  have HG := eqSortProbe_general_prefix heq hs hregistry hΓ hP hQ HC
  have ht := eqSortProbe_typed heq hΓ hP hQ hq
  have HE : proofErase Γ (eqSortProbe P Q q) =
      .app (proofErase Γ (eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))) (.sort .zero) Q)) .proof := by
    rw [show proofErase Γ (eqSortProbe P Q q) = .app _ _ from if_neg (not_isProof_of_sort hΓ ht),
      proofErase_eq_proof.2 ⟨_, hq, HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩]
    rfl
  rw [HE]
  refine ScopedCompute.trans (ScopedCompute.app (.base (.inr (.inl HG))) .refl) ?_
  exact .beta .beta

/-- A union endpoint certificate has a finite stage, and the probe's exact
sort computation needs only its immediate successor. -/
theorem eqSortProbe_compute_of_comparison
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HC : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q)) :
    ∃ stage, ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (eqSortProbe P Q q)) (.sort .zero) := by
  obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
  exact ⟨stage+1, eqSortProbe_compute_stage heq hs hregistry hΓ hP hQ hq HC⟩

end Lean4Lean.VEnv.Strengthening
