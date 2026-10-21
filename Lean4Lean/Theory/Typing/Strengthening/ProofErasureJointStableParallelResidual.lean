import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStablePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitutableParallelStrip
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelPrimitiveResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableFamilyBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointParallelSingleton

/-! # Source-stage parallel commutation from lower-stage guard transport

The target primitive carries all future typed substitutions. Lower-stage guard
transport certifies every primitive beta square, and the compatible-path theorem
handles applications without reapplying beta stability to target paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Local residual property: every typed primitive parallel beta square has a
residual primitive stable under all typed substitutions. At nonzero stages the
theorem below establishes this from lower-source-stage proposition beta
transport; an unconditional proof of that transport remains missing. -/
def JointStageStableParallelResidual (D : PureObservation.Definitions) (stage : Nat) : Prop :=
  ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ErasedJointStage D stage (proofEraseCtx Γ) (proofErase Γ e) out →
    BetaPar (proofErase Γ e) reduced →
    ∃ shared, BetaPar out shared ∧
      SubstitutionStablePrimitive (ErasedJointUnion D) (proofEraseCtx Γ) reduced shared

/-- Ordinary core primitives have substitution-stable parallel residuals
syntactically. This closes the computation base stage without proposition
beta stability, canonical Eq, or declaration soundness. -/
theorem joint_zero_stable_parallel_residual : JointStageStableParallelResidual D 0 := by
  intro Γ e T out reduced _ _ H P
  obtain ⟨shared, PB, HR⟩ := erased_iota_primitive_parallel_beta_residual H P
  exact ⟨shared, PB, ⟨0, HR⟩, fun _ => ⟨0, erased_iota_primitive_subst HR⟩⟩

/-- A singleton parallel residual retains its original stage guard long enough
to certify all future substitutions. Only the source guard stage needs beta
transport; the resulting union guard is never used as a new input to it. -/
theorem proofErase_joint_singleton_stable_parallel_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (H : JointSingletonPrimitive (ErasedJointStage D stage) Δ source out)
    (RB : BetaPar source reduced) :
    ∃ shared, BetaPar out shared ∧
      SubstitutionStablePrimitive (ErasedJointUnion D) Δ reduced shared := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨args', rfl, HA⟩ := RB.const_spine
    obtain ⟨_, _, _, R, HT', HR⟩ := V.parallel_beta_residual_with heq
      (erased_joint_family_descent (erased_joint_stage_descent heq hs stage))
      (Hbeta.stable_family_transport heq hs) HT ha hcalc HG HA
    exact ⟨_, R, singleton_with_stable_guard heq hs HT' HR⟩

private theorem stage_stable_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (n : Nat)
    (Hbeta : ∀ k, k < n → JointPropBetaTransport (ErasedJointStage D k) (ErasedJointUnion D)) :
    JointStageStableParallelResidual D n := by
  induction n with
  | zero => exact joint_zero_stable_parallel_residual
  | succ n ih =>
    intro Γ e T out reduced hΓ ht H RB
    rcases H with H | H | H
    · exact ih (fun k hk => Hbeta k (by omega)) hΓ ht H RB
    · exact proofErase_joint_singleton_stable_parallel_residual heq hs (Hbeta n (by omega)) H RB
    · exact proofErase_joint_singleton_stable_parallel_residual heq hs (Hbeta n (by omega))
        (proofErase_joint_prefix_as_general_with heq (erased_joint_stage_descent heq hs n)
          (erased_joint_stage_rename heq hs n) hregistry hΓ ht H) RB

/-- All stage-n+1 primitive parallel residuals, including specialized Eq roots,
carry future-substitution certificates assuming proposition beta transport at
stage n only. Inherited primitives use monotonicity of that same source bound. -/
theorem joint_stage_stable_parallel_residual_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D)) :
    JointStageStableParallelResidual D (stage + 1) :=
  stage_stable_residual heq hs hregistry (stage + 1)
    (fun _ hk => Hbeta.source_mono (erased_joint_stage_mono (by omega)))

/-- Stable primitive residuals lift to full stage-indexed paths with one
parallel output residual. The produced path still carries substitution
certificates, so its body segments can be instantiated without a new global
stability premise. The local residual property is supplied explicitly. -/
theorem proofErase_joint_stable_parallel_beta_strip
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hres : JointStageStableParallelResidual D stage)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (SubstitutionStablePrimitive (ErasedJointUnion D))
        (proofEraseCtx Γ) reduced shared := by
  apply proofErase_scoped_parallel_beta_strip_to (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_head stage)
    (substitution_stable_primitive_descent (erased_joint_union_descent heq hs))
    (fun H => erased_joint_union_head H.1) SubstitutionStablePrimitive.subst ?_ hΓ ht R P
  intro Γ e T out reduced hΓ ht H P
  obtain ⟨shared, PB, HR⟩ := Hres hΓ ht H P
  exact ⟨shared, PB, .base HR⟩

/-- One parallel beta development commutes with every typed stage-n+1 path
under stage-n proposition beta transport alone. The output path retains
substitution certificates. Iteration along arbitrary finite beta still needs
beta closure of this enriched target or a stronger invariant retaining origins. -/
theorem proofErase_joint_stage_parallel_strip_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out)
    (P : BetaPar (proofErase Γ e) reduced) :
    ∃ shared, BetaPar out shared ∧
      ScopedCompute (SubstitutionStablePrimitive (ErasedJointUnion D))
        (proofEraseCtx Γ) reduced shared :=
  proofErase_joint_stable_parallel_beta_strip heq hs
    (joint_stage_stable_parallel_residual_of_lower_beta heq hs hregistry Hbeta) hΓ ht R P

end Lean4Lean.VEnv.Strengthening
