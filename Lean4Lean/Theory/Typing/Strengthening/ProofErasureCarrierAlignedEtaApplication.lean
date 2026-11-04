import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeEtaExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawApplicationSupport

/-! # Typed application of native eta expansion

The recovered domain may differ from the function's assigned domain. Forward
replay and Pi injectivity still type its actual argument at that domain, so
the expanded application contracts by raw beta, also for proof arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A guarded native eta expansion applied to any argument of the original
function beta-contracts to its original raw application. No native recovery
of the argument or equality of the two displayed domains is required. -/
theorem proofErase_nativeEtaExpansion_application_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (H : NativeEtaExpansion Step (proofEraseCtx Γ) (proofErase Γ f) out) :
    ProofShape.BetaRed (.app out (proofErase Γ x))
      (.app (proofErase Γ f) (proofErase Γ x)) := by
  cases H with
  | intro R S =>
    rename_i A' B' u
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨D, C, hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero] using R)
    obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := (ED ▸ S).descend hΓ hΓ W hD
    have hxD := argument_at_displayed_domain hΓ hf hfD hx
    have EL (e : ProofShape) : (e.liftN 1).inst (proofErase Γ x) = e := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
    simpa only [ProofShape.inst, EL, proofErase_eta_argument_inst hΓ hD hxD] using
      (ProofShape.BetaRed.beta (A := A') (b := .app ((proofErase Γ f).liftN 1) (etaArgument u))
        (a := proofErase Γ x))

/-- The application square remains a raw beta square after independently
computing the argument. Replay supplies its original typing and exact output. -/
theorem proofErase_nativeEtaExpansion_computed_argument_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (harg : ErasedScopedPrimitiveDescent ArgStep)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (H : NativeEtaExpansion Step (proofEraseCtx Γ) (proofErase Γ f) out)
    (RX : ScopedCompute ArgStep (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ProofShape.BetaRed (.app out outX) (.app (proofErase Γ f) outX) := by
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize harg hΓ hx rfl rfl RX
  rw [← EX]
  exact proofErase_nativeEtaExpansion_application_beta hstep hΓ hf HX.hasType.2 H

end Lean4Lean.VEnv.Strengthening
