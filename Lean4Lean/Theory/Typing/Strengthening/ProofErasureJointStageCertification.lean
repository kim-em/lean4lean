import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Exact certification of finite-stage joint computations

Lower-stage proposition beta transport certifies the original singleton guard
without changing either endpoint. Determinism of the generated telescope
identifies the reflexive-development output with the original output. Typed
computation substitution then preserves this exactness through full paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem certify_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (H : JointSingletonPrimitive (ErasedJointStage D stage) Δ source out) :
    ErasedBetaStableJoint D Δ source out := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | @intro C args domains result V ha hcalc HG =>
    have HA : List.Forall₂ BetaPar args args := by
      clear ha hcalc HG HT
      induction args with
      | nil => exact .nil
      | cons a args ih => exact .cons (.refl _) ih
    obtain ⟨domains', result', hcalc', _, HT', HR⟩ := V.parallel_beta_residual_with heq
      (erased_joint_family_descent (erased_joint_stage_descent heq hs stage))
      (Hbeta.beta_stable_family_transport heq hs) HT ha hcalc HG HA
    have E := Option.some.inj (hcalc.symm.trans hcalc')
    cases E
    exact .inr ⟨HT', HR⟩

private theorem certify_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (n : Nat)
    (Hbeta : ∀ k, k < n → JointPropBetaTransport (ErasedJointStage D k) (ErasedJointUnion D)) :
    ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ErasedJointStage D n (proofEraseCtx Γ) (proofErase Γ e) out →
      ErasedBetaStableJoint D (proofEraseCtx Γ) (proofErase Γ e) out := by
  induction n with
  | zero => exact fun _ _ H => .inl H
  | succ n ih =>
    intro Γ e T out hΓ ht H
    rcases H with H | H | H
    · exact ih (fun k hk => Hbeta k (by omega)) hΓ ht H
    · exact certify_singleton heq hs (Hbeta n (by omega)) H
    · exact certify_singleton heq hs (Hbeta n (by omega))
        (proofErase_joint_prefix_as_general_with heq (erased_joint_stage_descent heq hs n)
          (erased_joint_stage_rename heq hs n) hregistry hΓ ht H)

/-- Every typed stage-n+1 primitive has a beta/substitution certificate at its
original endpoints. Only stage-n proposition beta transport is required; the
output is not replaced by an unspecified beta reduct. -/
theorem erased_joint_stage_certify_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ErasedJointStage D (stage + 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ErasedBetaStableJoint D (proofEraseCtx Γ) (proofErase Γ e) out :=
  certify_stage heq hs hregistry (stage + 1)
    (fun _ hk => Hbeta.source_mono (erased_joint_stage_mono (by omega))) hΓ ht H

/-- Typed primitive substitution lands in the certified relation with its
exact substituted output. Future substitutions and beta residuals therefore
remain available without a stability assumption for enlarged target guards. -/
theorem erased_joint_stage_certified_subst_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D)) :
    ErasedPrimitiveSubstitutionTo (ErasedJointStage D (stage + 1)) (ErasedBetaStableJoint D) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
  have HC := erased_joint_stage_certify_of_lower_beta heq hs hregistry Hbeta W.wf ht H
  have HS := erased_beta_stable_joint_subst heq hs HC (ContextSubstitution.of_typed hΓ₀ W E)
  rw [← proofErase_subst_with hΓ₀ W ht E] at HS
  exact .base HS

/-- An entire typed computation is certified exactly, including all sequential
intermediates and binder bodies. This is an embedding at the original source
and output, not just a commutation square with an extra output beta path. -/
theorem proofErase_joint_stage_compute_certify_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ e) out := by
  have W : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ) ProofShape.Subst.id :=
    ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ))
  simpa only [ProofShape.subst_id] using R.subst_typed
    (erased_joint_stage_descent heq hs (stage + 1))
    (erased_joint_stage_certified_subst_of_lower_beta heq hs hregistry Hbeta) hΓ ht rfl rfl W

end Lean4Lean.VEnv.Strengthening
