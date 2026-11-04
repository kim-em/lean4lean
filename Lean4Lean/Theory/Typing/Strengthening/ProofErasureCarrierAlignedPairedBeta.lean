import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCongruence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplicationSupport

/-! # Paired beta with joining bodies and independently related images

Two typed bodies may have different written domains and a shared finite erased
beta reduct. Their argument images need only compare in inferred mode: no join
or exact recovery at a written domain is required. This covers a body-join
fragment, not substitution through arbitrary comparison certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A finite common beta reduct of two bodies may be instantiated at distinct
inferred-related images. The left body supplies the typed shared template;
the right body may live under a different written domain. -/
theorem proofErase_carrier_aligned_joined_body_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hΓE : OnCtx (E :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (E :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (hyE : env.HasType univs Γ y E)
    (RB : ProofShape.BetaRed (proofErase (A :: Γ) b) shared)
    (RC : ProofShape.BetaRed (proofErase (E :: Γ) c) shared)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨b', Rb', Eb'⟩ := proofErase_beta_replay hΓA hb RB
  have hb' := (Rb'.simAt henv.orderedStrong henv.betaSubjectReduction hΓA B hb).hasType.2
  have HT := proofErase_carrier_aligned_inst_images hrename hΓA hb' hx hy H
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb',
    proofErase_instN hΓA hy Ctx.InstN.zero hb', Eb'] at HT
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb,
    proofErase_instN hΓE hyE Ctx.InstN.zero hc]
  have RX : ProofShape.BetaRed ((proofErase (A :: Γ) b).inst (proofErase Γ x))
      (shared.inst (proofErase Γ x)) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst (σ := ProofShape.Subst.one (proofErase Γ x))
  have RY : ProofShape.BetaRed ((proofErase (E :: Γ) c).inst (proofErase Γ y))
      (shared.inst (proofErase Γ y)) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RC.subst (σ := ProofShape.Subst.one (proofErase Γ y))
  exact .compute (.beta RX) (.beta RY) HT

/-- Paired head-beta contracta compare even with distinct written lambda
domains and nonjoining argument images, provided the erased bodies have an
explicit finite common beta reduct. Common assigned function typing transports
the argument typings to both displayed domains. -/
theorem proofErase_carrier_aligned_joined_head_beta
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P T))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P T))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (RB : ProofShape.BetaRed (proofErase (A :: Γ) b) shared)
    (RC : ProofShape.BetaRed (proofErase (E :: Γ) c) shared)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨⟨u, hA⟩, B, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C, hc⟩ := hg.lam_inv henv hΓ
  exact proofErase_carrier_aligned_joined_body_images hrename ⟨hΓ, u, hA⟩ ⟨hΓ, v, hE⟩ hb hc
    (argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx)
    (argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hy)
    (argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hy) RB RC H

end Lean4Lean.VEnv.Strengthening
