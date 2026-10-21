import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableSupply
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # The original-recovery square permits unrecoverable computed images

The eta-converted neutral variable cannot recover its assigned type. Its
identity expansion does recover that type, and the directed square transports
every typed body path through this beta computation without image recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The original-recovery square has a typed non-proof example whose computed
argument has no exact assigned-type recovery anywhere in the joint union.
Every typed body path still transports to its output instantiated by that
argument. Thus the square does not implicitly require recovery preservation. -/
theorem proofErase_joint_inst_square_without_image_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' x A y, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' x A ∧ env.HasType univs Γ' y A ∧ ¬ IsProof Γ' x ∧
      ProofShape.BetaRed (proofErase Γ' y) (proofErase Γ' x) ∧
      ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' y) (proofErase Γ' A) ∧
      (¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ')
        (proofErase Γ' x) (proofErase Γ' A)) ∧
      ∀ {b B out}, env.HasType univs (A :: Γ') b B →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ')) (proofErase (A :: Γ') b) out →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
          (proofErase Γ' (b.inst y)) (out.inst (proofErase Γ' x)) := by
  obtain ⟨Γ', x, A, _, _, hΓ', hx, hnx, _, _, Hno⟩ :=
    EtaRecoveryJoinBoundary.typed_join_failure D hΓ
  obtain ⟨hy, HE, RY, HR⟩ := proofErase_identity_recovery_cover
    (Step := ErasedJointUnion D) hΓ' hx
  have hny : ¬ IsProof Γ' (.app (.lam A (.bvar 0)) x) := by
    intro hp
    have hp' := (isProof_congr hΓ' HE).1 hp
    exact hnx hp'
  have HRy := HR hny
  refine ⟨Γ', x, A, _, hΓ', hx, hy, hnx, RY, HRy, ?_, ?_⟩
  · intro H
    exact Hno _ _ H .refl .refl
  · intro b B out hb RB
    obtain ⟨u, hA⟩ := hx.isType henv hΓ'
    exact proofErase_joint_union_compute_inst_square heq hs ⟨hΓ', u, hA⟩ hb hy
      (fun _ => HRy) RB (.beta RY)

/-- Recoverable native walks are a genuine restriction on typed walks.
An eta-converted variable already gives a one-argument typed telescope walk
that lacks the retained exact recovery required by the constructive theorem. -/
theorem typed_native_walk_not_recoverable (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A x, OnCtx Γ' (env.IsType univs) ∧
      InstForallsC env univs Γ' (.forallE A (.sort .zero)) [x] (.sort .zero) ∧
      ¬ RecoverableNativeWalk D Γ' (.forallE A (.sort .zero)) [x] (.sort .zero) := by
  obtain ⟨Γ', x, A, _, _, hΓ', hx, hnx, _, _, Hno⟩ :=
    EtaRecoveryJoinBoundary.typed_join_failure D hΓ
  refine ⟨Γ', A, x, hΓ', .cons hx .nil, ?_⟩
  intro HW
  cases HW with
  | cons _ HR _ => exact Hno _ _ (HR hnx) .refl .refl

end Lean4Lean.VEnv.Strengthening
