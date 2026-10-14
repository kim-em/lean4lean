import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionRealization

/-! # Commuting template computation with computation of substitution images

Typed replay reconstructs the template output. The computed image map remains
interpretable, so both routes around the square retain the same scoped relation.
No normalization, comparison composition, or computational confluence is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A typed template computation commutes with pointwise image computation.
The two lower edges end at exactly the same raw substituted output. The
template output and computed images need no supplied original representatives. -/
theorem proofErase_scoped_compute_subst_square
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ ρ) (ha : env.HasType univs Γ a A)
    (H : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) out)
    (R : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ i) (τ i)) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst ρ) ((proofErase Γ a).subst τ) ∧
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst ρ) (out.subst ρ) ∧
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst τ) (out.subst τ) ∧
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (out.subst ρ) (out.subst τ) := by
  have WI : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨b, HB, EB⟩ := proofErase_scoped_compute_descend hstep W.wf W.wf WI ha rfl
    (by simpa only [ProofShape.liftN_zero] using H)
  simp only [ProofShape.liftN_zero] at EB
  have WC : ProofShape.ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) ρ :=
    ProofShape.ContextSubstitution.of_typed hΓ₀ W E
  refine ⟨proofErase_scoped_compute_subst_images hsubst hΓ₀ W ha E R,
    H.subst hsubst WC, H.subst hsubst (WC.compute_images hstep R), ?_⟩
  rw [← EB]
  exact proofErase_scoped_compute_subst_images hsubst hΓ₀ W HB.hasType.2 E R

/-- The substitution square stays inside each finite contextual prefix stage.
In particular, reducing captured arguments does not require a deeper K guard. -/
theorem proofErase_scoped_prefix_subst_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ ρ) (ha : env.HasType univs Γ a A)
    (H : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ a) out)
    (R : ∀ i, ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      (ρ i) (τ i)) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst ρ) ((proofErase Γ a).subst τ) ∧
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst ρ) (out.subst ρ) ∧
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      ((proofErase Γ a).subst τ) (out.subst τ) ∧
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      (out.subst ρ) (out.subst τ) :=
  proofErase_scoped_compute_subst_square (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) hΓ₀ W E ha H R

end Lean4Lean.VEnv.Strengthening
