import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExactStageImages

/-! # Exact recovery and checking from typed computation transport

An image bound is enough to transport all recovery constructors. Conversion
replays the selected source type, then transports its forward computation.
-/
namespace Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
variable {D : PureObservation.Definitions} {k later : Nat}

/-- Every native recovery constructor transports exactly once typed computation
transport is established and the target stage includes the image stage. -/
theorem recovery_of_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Source) (hle : k ≤ later)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
      ScopedCompute (ErasedComputedJointStage D later) Δ' (source.subst τ) (out.subst τ))
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution D k Δ Δ' τ) :
    ScopedTypeRecovery (ErasedComputedJointStage D later) Δ' (source.subst τ) (out.subst τ) :=
  NativeImageTransport.recovery_of_compute (erased_computed_joint_stage_rename heq hs k) hstep
    (fun H => erased_computed_joint_stage_mono hle H) hcompute R hΓ ht EΓ Ee W

/-- Full joint checking transports using exact native recovery for the selected
application domain. Computed applications and all guard constructors are included. -/
theorem check_of_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Source) (hle : k ≤ later)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
      ScopedCompute (ErasedComputedJointStage D later) Δ' (source.subst τ) (out.subst τ))
    (H : ComputedJointCheck Source Δ kind a b) :
    ComputedJointTransportResult (ImageSubstitution D k)
      (ErasedComputedJointStage D later) Δ kind a b :=
  NativeImageTransport.check_of_compute (erased_computed_joint_stage_rename heq hs k) hstep
    (fun H => erased_computed_joint_stage_mono hle H) hcompute H

end Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
