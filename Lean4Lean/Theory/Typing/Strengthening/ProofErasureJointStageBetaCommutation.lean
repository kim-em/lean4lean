import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageCertification

/-! # Finite beta commutation from strictly lower source-stage transport

The original typed path can be equipped with future beta and substitution
certificates without changing its endpoints. Those certificates are preserved
by every parallel square, so finite iteration never needs transport of an
arbitrary higher-stage target comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem singleton_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (H : JointSingletonPrimitive (ErasedJointStage D stage) Δ source out)
    (RB : BetaPar source reduced) :
    ∃ shared, BetaPar out shared ∧ ErasedBetaStableJoint D Δ reduced shared := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨args', rfl, HA⟩ := RB.const_spine
    obtain ⟨_, _, _, R, HT', HR⟩ := V.parallel_beta_residual_with heq
      (erased_joint_family_descent (erased_joint_stage_descent heq hs stage))
      (Hbeta.beta_stable_family_transport heq hs) HT ha hcalc HG HA
    exact ⟨_, R, .inr ⟨HT', HR⟩⟩

private theorem stage_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (n : Nat)
    (Hbeta : ∀ k, k < n → JointPropBetaTransport (ErasedJointStage D k) (ErasedJointUnion D)) :
    ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ErasedJointStage D n (proofEraseCtx Γ) (proofErase Γ e) out →
      BetaPar (proofErase Γ e) reduced →
      ∃ shared, BetaPar out shared ∧ ErasedBetaStableJoint D (proofEraseCtx Γ) reduced shared := by
  induction n with
  | zero =>
    intro Γ e T out reduced _ _ H P
    obtain ⟨shared, PB, HR⟩ := erased_iota_primitive_parallel_beta_residual H P
    exact ⟨shared, PB, .inl HR⟩
  | succ n ih =>
    intro Γ e T out reduced hΓ ht H RB
    rcases H with H | H | H
    · exact ih (fun k hk => Hbeta k (by omega)) hΓ ht H RB
    · exact singleton_residual heq hs (Hbeta n (by omega)) H RB
    · exact singleton_residual heq hs (Hbeta n (by omega))
        (proofErase_joint_prefix_as_general_with heq (erased_joint_stage_descent heq hs n)
          (erased_joint_stage_rename heq hs n) hregistry hΓ ht H) RB

/-- The computation base stage commutes with arbitrary finite beta without
any proposition-transport premise. Its core primitives already belong to the
enriched target. This does not establish stage-zero comparison transport. -/
theorem proofErase_joint_zero_beta_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) reduced shared :=
  proofErase_beta_stable_joint_beta_commute heq hs hΓ ht (R.mono (fun H => .inl H)) B

/-- Every stage-n+1 primitive parallel square has a residual retaining future
beta and substitution certificates, assuming beta transport only at stage n. -/
theorem erased_joint_stage_beta_stable_parallel_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ErasedJointStage D (stage + 1) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧ ErasedBetaStableJoint D (proofEraseCtx Γ) reduced shared :=
  stage_residual heq hs hregistry (stage + 1)
    (fun _ hk => Hbeta.source_mono (erased_joint_stage_mono (by omega))) hΓ ht H P

/-- A stage-n+1 path commutes with one parallel development into a target that
is closed under both substitution and further parallel residuals. -/
theorem proofErase_joint_stage_beta_stable_parallel_strip
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) reduced shared := by
  apply proofErase_scoped_parallel_beta_strip_to (erased_joint_stage_descent heq hs (stage + 1))
    (erased_joint_stage_head (stage + 1)) (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) ?_ hΓ ht R P
  intro Γ e T out reduced hΓ ht H P
  obtain ⟨shared, PB, HR⟩ := erased_joint_stage_beta_stable_parallel_residual
    heq hs hregistry Hbeta hΓ ht H P
  exact ⟨shared, PB, .base HR⟩

/-- Arbitrary finite beta commutes with stage-n+1 computation using only
stage-n proposition beta transport. Exact certification first embeds the
original path in the internally stable target; every iteration preserves
those certificates without invoking transport on enlarged target guards. -/
theorem proofErase_joint_stage_beta_commute_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) reduced shared :=
  proofErase_beta_stable_joint_beta_commute heq hs hΓ ht
    (proofErase_joint_stage_compute_certify_of_lower_beta heq hs hregistry Hbeta hΓ ht R) B

/-- The certified finite-beta residual is an actual finite later-stage joint
path. There is no full-union beta-stability premise or recovery requirement on
any substituted argument; the input stability bound is strictly lower. -/
theorem proofErase_joint_stage_beta_commute_later_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out)
    (B : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ later shared, stage + 1 ≤ later ∧ ProofShape.BetaRed out shared ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ) reduced shared := by
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_stage_beta_commute_of_lower_beta
    heq hs hregistry Hbeta hΓ ht R B
  have RS := RS.mono erased_beta_stable_joint_into_union
  obtain ⟨later, RS⟩ := RS.finite_stage erased_joint_stage_mono
  exact ⟨max (stage + 1) later, shared, Nat.le_max_left _ _, BS,
    RS.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

end Lean4Lean.VEnv.Strengthening
