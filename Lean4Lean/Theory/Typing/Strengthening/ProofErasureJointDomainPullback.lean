import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveringPrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedContextConversion

/-! # Pulling certificates back along computation of binder annotations

If A computes to B, a variable declared at A recovers B. Thus certificates
under B can be used under A, with identical raw endpoints. This direction
supports binder computation diagrams; it asserts neither transport in the
opposite direction nor transport along arbitrary type conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

namespace ProofShape
/-- Interpreted identity substitution is exactly recoverable when each target
oracle computes to the source oracle. The orientation is contravariant. -/
theorem RecoveringSubstitution.of_oracle_compute
    (W : ContextSubstitution Δ Δ' Subst.id)
    (R : ∀ i, ScopedCompute Image Δ' (contextOracle Δ' i) (contextOracle Δ i)) :
    RecoveringSubstitution Image Δ Δ' Subst.id := by
  refine ⟨W, ?_⟩
  intro Γ i A hΓ EΓ hl hn
  simp only [subst_id]
  simp only [Subst.id]
  exact ScopedTypeRecovery.convert (ScopedTypeRecovery.bvar (i := i)) (R i)

/-- A computed domain supplies recovery of the reduced annotation from the
original declaration. Older oracle entries remain identical. -/
theorem RecoveringSubstitution.of_domain_compute
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (R : ScopedCompute Image (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B)) :
    RecoveringSubstitution Image (proofEraseCtx (B :: Γ)) (proofEraseCtx (A :: Γ)) Subst.id := by
  apply RecoveringSubstitution.of_oracle_compute
    (ContextSubstitution.of_defeqCtx hΓ (.succ .zero HAB.symm))
  intro i
  cases i with
  | zero =>
    have RW := R.rename hrename (ContextRenaming.of_liftN hΓ
      (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, HAB.hasType.1⟩) Ctx.LiftN.one)
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, subst_bvar_liftN] using RW
  | succ i =>
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons]
    exact .refl
end ProofShape

/-- A joint computation of a typed annotation gives the interpreted identity
needed for pullback, without assuming annotation conversion separately. -/
theorem proofErase_joint_domain_pullback (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (R : ScopedCompute (ErasedJointStage D domainStage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B)) :
    RecoveringSubstitution (ErasedJointStage D domainStage)
      (proofEraseCtx (B :: Γ)) (proofEraseCtx (A :: Γ)) ProofShape.Subst.id := by
  have HC : JointCompare (ErasedJointStage D domainStage) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ B) := .compute R .refl (.leaf .refl)
  have HAB := (proofErase_joint_compare_reflect (erased_joint_stage_descent heq hs domainStage)
    hΓ hA hB HC).2 rfl (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hB)
  exact RecoveringSubstitution.of_domain_compute (erased_joint_stage_rename heq hs domainStage)
    hΓ (HAB.of_l henv hΓ hA) R

/-- Typed body computation under a reduced annotation pulls back to the original
annotation with exactly the same raw source and output. Stage bounds add. -/
theorem proofErase_joint_compute_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage D domainStage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (B :: Γ) e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedCompute (ErasedJointStage D (domainStage + stage)) (proofEraseCtx (A :: Γ))
      (proofErase (B :: Γ) e) out := by
  have H := R.subst_recovering (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs domainStage)
    (erased_joint_stage_recovering heq hs domainStage stage)
    (show OnCtx (B :: Γ) (env.IsType univs) from ⟨hΓ, v, hB⟩) he rfl rfl
    (proofErase_joint_domain_pullback heq hs hΓ hA hB RA)
  simpa only [ProofShape.subst_id] using H

/-- Selected type recovery pulls back with its exact output, even though the
context's fresh oracle annotation changes. -/
theorem proofErase_joint_recovery_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage D domainStage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (B :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedTypeRecovery (ErasedJointStage D (domainStage + stage)) (proofEraseCtx (A :: Γ))
      (proofErase (B :: Γ) e) out := by
  have H := R.subst_recovering (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs domainStage)
    (erased_joint_stage_mono (Nat.le_add_right domainStage stage))
    (erased_joint_stage_recovering heq hs domainStage stage)
    (show OnCtx (B :: Γ) (env.IsType univs) from ⟨hΓ, v, hB⟩) he rfl rfl
    (proofErase_joint_domain_pullback heq hs hΓ hA hB RA)
  simpa only [ProofShape.subst_id] using H

/-- Both joint comparison modes pull back along domain computation, retaining
all endpoint syntax and accounting for recursive recovered applications. -/
theorem proofErase_joint_compare_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage D domainStage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    JointCompare (ErasedJointStage D (domainStage + stage)) (proofEraseCtx (A :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have H' := H.subst_recovering (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs domainStage)
    (erased_joint_stage_mono (Nat.le_add_right domainStage stage))
    (erased_joint_stage_recovering heq hs domainStage stage)
    (show OnCtx (B :: Γ) (env.IsType univs) from ⟨hΓ, v, hB⟩) ha hb rfl rfl rfl
    (proofErase_joint_domain_pullback heq hs hΓ hA hB RA)
  simpa only [ProofShape.subst_id] using H'

/-- Recursive explicit-carrier guards pull back along domain computation with
both endpoints and the supplied carrier unchanged. -/
theorem proofErase_joint_carrier_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointStage D domainStage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) T) (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    JointCarrierGuard (ErasedJointStage D (domainStage + stage)) (proofEraseCtx (A :: Γ))
      (proofErase (B :: Γ) T) (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have H' := H.subst_recovering (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs domainStage)
    (erased_joint_stage_mono (Nat.le_add_right domainStage stage))
    (erased_joint_stage_recovering heq hs domainStage stage)
    (show OnCtx (B :: Γ) (env.IsType univs) from ⟨hΓ, v, hB⟩) ha hb rfl rfl rfl rfl
    (proofErase_joint_domain_pullback heq hs hΓ hA hB RA)
  simpa only [ProofShape.subst_id] using H'

end Lean4Lean.VEnv.Strengthening
