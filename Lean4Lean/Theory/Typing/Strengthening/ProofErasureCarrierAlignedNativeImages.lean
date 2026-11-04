import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRecoveredTransport

/-! # Full aligned transport with exactly recoverable native images

The native-image transport theorems discharge every callback of the full
aligned induction. The only remaining image input is explicit recovery of each
retained variable at its exact substituted oracle type.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeImageTransport
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Native-image substitution preserves the full aligned checker, including
recursive comparisons of independently recovered types and fresh eta binders.
Computation transport is the sole relation-specific callback. -/
theorem aligned_of_compute
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (H : CarrierAlignedCompare Source Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ImageSubstitution ImageStep Δ Δ' τ) :
    CarrierAlignedCompare Target Δ' mode (sa.subst τ) (sb.subst τ) :=
  H.transport_native (ImageSubstitution ImageStep) hstep
    (fun W => W.cons hrename) (fun W S => ContextSubstitution.sort W.interpretation S)
    hcompute (fun R => recovery_of_compute hrename hstep hinclude hcompute R)
    (fun H => check_of_compute hrename hstep hinclude hcompute H)
    (fun H => recovered_of_compute hrename hstep hinclude hcompute H)
    hΓ ha hb EΓ Ea Eb W

end Lean4Lean.VEnv.Strengthening.NativeImageTransport
