import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExactStageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedGuardTransport

/-! # Substitution at every finite computed-joint stage

Images recovered at stage `k` transport a stage `n` derivation to stage `n + k`.
The induction transports the full preceding-stage checker before reconstructing
each guarded singleton or Eq primitive. No guarded confluence is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
variable {D : PureObservation.Definitions} {k n : Nat}

/-- Exact-image primitive substitution with an additive stage bound. Guards
are transported recursively at the preceding source and target stages. -/
theorem primitive_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n {Γ Δ Δ' τ e T source out}, ErasedComputedJointStage D n Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
      ErasedComputedJointStage D (n + k) Δ' (source.subst τ) (out.subst τ) := by
  intro n
  induction n with
  | zero =>
    intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee W
    simpa only [Nat.zero_add] using
      (erased_computed_joint_stage_mono (Δ := Δ') (Nat.zero_le k)
        (erased_iota_primitive_subst (σ := τ) H))
  | succ n ih =>
    have hcompute : ∀ {Γ Δ Δ' τ e T source out},
        ScopedCompute (ErasedComputedJointStage D n) Δ source out →
        OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
        proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
        ScopedCompute (ErasedComputedJointStage D (n + k)) Δ' (source.subst τ) (out.subst τ) := by
      intro Γ Δ Δ' τ e T source out R hΓ ht EΓ Ee W
      exact R.transport_typed (erased_computed_joint_stage_descent heq hs n)
        (ImageSubstitution D k) (fun W => W.cons heq hs)
        (fun H hΓ ht EΓ Ee W => .base (ih H hΓ ht EΓ Ee W)) hΓ ht EΓ Ee W
    have G : ComputedGuardSubstitution (ErasedComputedJointStage D n)
        (ErasedComputedJointStage D (n + k)) (ImageSubstitution D k) :=
      ⟨(fun W => W.interpretation), (fun W => W.cons heq hs),
        fun H => check_of_compute heq hs (erased_computed_joint_stage_descent heq hs n)
          (Nat.le_add_left k n) hcompute H⟩
    intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee W
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have WR : ImageSubstitution D k (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
      rw [EΓ, EΓ₀]
      exact W
    rw [Nat.succ_add]
    rcases H with H | H | H
    · exact .inl (ih H hΓ ht EΓ Ee W)
    · refine .inr (.inl ⟨H.1.subst W.interpretation, ?_⟩)
      have HH := proofErase_computed_singleton_guard_subst_between heq
        (erased_computed_joint_stage_descent heq hs n)
        (erased_computed_joint_stage_descent heq hs (n + k)) G hΓ₀ WS ES WR ht
        (by simpa only [EΓ, Ee] using H.2)
      simpa only [EΓ₀, Ee] using HH
    · apply Or.inr; apply Or.inr
      have HH := proofErase_computed_prefix_guard_subst_between heq G hΓ WR ht
        (by simpa only [EΓ, Ee] using H)
      simpa only [EΓ₀, Ee] using HH


/-- All compatible computations transport with the same additive stage bound,
including transitive intermediate terms and computations below binders. -/
theorem compute (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedComputedJointStage D n) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution D k Δ Δ' τ) :
    ScopedCompute (ErasedComputedJointStage D (n + k)) Δ' (source.subst τ) (out.subst τ) :=
  R.transport_typed (erased_computed_joint_stage_descent heq hs n)
    (ImageSubstitution D k) (fun W => W.cons heq hs)
    (fun H hΓ ht EΓ Ee W => .base (primitive_subst heq hs n H hΓ ht EΓ Ee W))
    hΓ ht EΓ Ee W

/-- Exact selected native types survive every finite guarded stage. -/
theorem recovery (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedComputedJointStage D n) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution D k Δ Δ' τ) :
    ScopedTypeRecovery (ErasedComputedJointStage D (n + k)) Δ' (source.subst τ) (out.subst τ) :=
  recovery_of_compute heq hs (erased_computed_joint_stage_descent heq hs n)
    (Nat.le_add_left k n) (fun R => compute heq hs R) R hΓ ht EΓ Ee W

/-- Both complete checking views transport at all finite stages; the image
hypothesis is a native recovery certificate, not a target checking premise. -/
theorem check (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedComputedJointStage D n) Δ kind a b) :
    ComputedJointTransportResult (ImageSubstitution D k)
      (ErasedComputedJointStage D (n + k)) Δ kind a b :=
  check_of_compute heq hs (erased_computed_joint_stage_descent heq hs n)
    (Nat.le_add_left k n) (fun R => compute heq hs R) H

end Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
