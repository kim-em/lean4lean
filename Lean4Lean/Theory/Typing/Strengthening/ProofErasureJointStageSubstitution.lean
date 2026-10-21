import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageBetaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Computation substitution from strictly lower source-stage stability

Only guards below the source primitive stage need beta transport. The expanded
guard retains its original stage until both endpoints contract into the union.
Specialized Eq guards are encoded in the same source relation before transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem primitive_substitution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (n : Nat)
    (Hbeta : ∀ k, k < n → JointPropBetaTransport (ErasedJointStage D k) (ErasedJointUnion D)) :
    ∀ {Γ Γ₀ σ τ e T out}, OnCtx Γ₀ (env.IsType univs) →
      Ctx.SubstEq env univs Γ₀ σ σ Γ → ErasedSubstAgreement Γ Γ₀ σ τ →
      env.HasType univs Γ e T → ErasedJointStage D n (proofEraseCtx Γ) (proofErase Γ e) out →
      ErasedJointUnion D (proofEraseCtx Γ₀) (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  induction n with
  | zero =>
    intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
    rw [proofErase_subst_with hΓ₀ W ht E]
    exact ⟨0, erased_iota_primitive_subst H⟩
  | succ n ih =>
    intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
    have HP : JointPropSubstitution (ErasedJointStage D n) (ErasedJointUnion D) :=
      fun hΓ W hP hQ HC => JointPropBetaTransport.subst_stage heq hs (Hbeta n (by omega)) hΓ W hP hQ HC
    have transport (H : JointSingletonPrimitive (ErasedJointStage D n)
        (proofEraseCtx Γ) (proofErase Γ e) out) :
        ErasedJointUnion D (proofEraseCtx Γ₀)
          (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
      rw [proofErase_subst_with hΓ₀ W ht E]
      exact erased_joint_union_iff.2 (.inr (.inl
        (proofErase_joint_general_substitution_with heq (erased_joint_stage_descent heq hs n)
          (erased_joint_union_descent heq hs) HP H (ContextSubstitution.of_typed hΓ₀ W E))))
    rcases H with H | H | H
    · exact ih (fun k hk => Hbeta k (by omega)) hΓ₀ W E ht H
    · exact transport H
    · exact transport (proofErase_joint_prefix_as_general_with heq
        (erased_joint_stage_descent heq hs n) (erased_joint_stage_rename heq hs n)
        hregistry W.wf ht H)

/-- Substitution of a typed stage-n+1 primitive retains one actual union
primitive, rather than merely a finite target path. Only stage-n proposition
beta transport is required. -/
theorem erased_joint_stage_primitive_subst_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (H : ErasedJointStage D (stage + 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ErasedJointUnion D (proofEraseCtx Γ₀) (proofErase Γ₀ (e.subst σ)) (out.subst τ) :=
  primitive_substitution heq hs hregistry (stage + 1)
    (fun _ hk => Hbeta.source_mono (erased_joint_stage_mono (by omega))) hΓ₀ W E ht H

/-- Computations at stage n+1 substitute into the union assuming beta
transport only for proposition comparisons whose input stage is n. Output
certificates need no stability law, and no exact image recovery is assumed. -/
theorem erased_joint_stage_subst_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D)) :
    ErasedPrimitiveSubstitutionTo (ErasedJointStage D (stage + 1)) (ErasedJointUnion D) :=
  fun hΓ₀ W E ht H => .base
    (erased_joint_stage_primitive_subst_of_lower_beta heq hs hregistry Hbeta hΓ₀ W E ht H)

/-- Arbitrary typed simultaneous substitution of a stage n+1 path needs only
stage-n proposition beta transport. Every sequential intermediate is realized
in the source stage before transport; target paths are never fed back into
the stability hypothesis. -/
theorem proofErase_joint_stage_compute_subst_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) :=
  proofErase_scoped_compute_subst_typed (erased_joint_stage_descent heq hs (stage + 1))
    (erased_joint_stage_subst_of_lower_beta heq hs hregistry Hbeta) hΓ₀ W E ht R

end Lean4Lean.VEnv.Strengthening
