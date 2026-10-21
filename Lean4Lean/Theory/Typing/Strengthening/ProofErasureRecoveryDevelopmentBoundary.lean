import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # One identity development can destroy assigned-type recovery permanently

Every typed term has an exactly recoverable identity-redex expansion. In the
eta-converted variable example, contracting this single head redex leaves a
variable for which no recovered type joins the assigned type, even after
further computation. A common type comparison remains available.
Thus complete developments cannot simply preserve the exact-recovery invariant,
even allowing arbitrary later stages and computation of the resulting image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A typed identity-redex expansion has exact assigned-type recovery at stage
zero, but no type recovered after its beta contraction computationally joins
that assigned type in the entire joint union. Both endpoints are non-proof and
have the same actual type. This refutes preservation of computed exact recovery
through even one identity development, not strengthening or computational
confluence. It applies to every definition collection and well-formed base. -/
theorem identity_development_recovery_no_join (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' x A native, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' x A ∧ ¬ IsProof Γ' x ∧
      let y := VExpr.app (.lam A (.bvar 0)) x
      env.HasType univs Γ' y A ∧ ¬ IsProof Γ' y ∧
      env.IsDefEq univs Γ' y x A ∧
      BetaRed (proofErase Γ' y) (proofErase Γ' x) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ')
        (proofErase Γ' y) (proofErase Γ' A) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ') (proofErase Γ' x) native ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ') false (proofErase Γ' A) native ∧
      ∀ image out shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' x) image →
        ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') image out →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' A) shared →
        ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') out shared := by
  obtain ⟨Γ', x, A, native, rfl, hΓ', hx, hn, RN, HN, Hno⟩ :=
    EtaRecoveryJoinBoundary.typed_join_failure D hΓ
  obtain ⟨hy, HE, RB, HR⟩ := proofErase_identity_recovery_cover
    (Step := ErasedJointStage D 0) hΓ' hx
  have hny : ¬ IsProof Γ' (.app (.lam A (.bvar 0)) (.bvar 0)) :=
    fun hp => hn ((isProof_congr hΓ' HE).1 hp)
  refine ⟨Γ', .bvar 0, A, native, hΓ', hx, hn, hy, hny, HE, RB, HR hny, RN, HN, ?_⟩
  intro image out shared RX RO RA RB
  have EX : proofErase Γ' (.bvar 0) = .bvar 0 := if_neg hn
  rw [EX] at RX
  have EI := RX.bvar_fixed erased_joint_union_head
  rw [EI, ← EX] at RO
  exact Hno out shared RO RA RB

end Lean4Lean.VEnv.Strengthening
