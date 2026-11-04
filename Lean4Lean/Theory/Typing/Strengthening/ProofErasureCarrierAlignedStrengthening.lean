import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCongruence

/-! # Exact strengthening of aligned native carrier comparisons -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Both comparison modes preserve and reflect unused binder insertion at
common typed endpoints. Primitive certificate descent and renaming suffice;
no completeness, beta stability, or semantic target soundness is assumed. -/
theorem proofErase_carrier_aligned_compare_lift_iff
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    CarrierAlignedCompare Step (proofEraseCtx Γ') mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k) ↔
    CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · intro H
    exact (proofErase_carrier_aligned_compare_certificate_descend hstep
      hΓ hΓ' W rfl ha hb H).1 ⟨_, ha.isType henv hΓ |>.choose_spec⟩
  · intro H
    have R := H.rename hrename (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
